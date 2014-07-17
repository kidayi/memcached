/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signal.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>

/* Forward Declarations */
static void item_link_q(item *it);
static void item_unlink_q(item *it);

#define LARGEST_ID POWER_LARGEST

//evict--依法收回
typedef struct {
    uint64_t evicted;
    uint64_t evicted_nonzero;
    rel_time_t evicted_time;
    uint64_t reclaimed;
    uint64_t outofmemory;
    uint64_t tailrepairs;
    uint64_t expired_unfetched;
    uint64_t evicted_unfetched;
    uint64_t crawler_reclaimed;
} itemstats_t;

//lru双向链表，分别记录2个端点
//指针的数组
static item *heads[LARGEST_ID];
static item *tails[LARGEST_ID];

//crawler--爬行动物
static crawler crawlers[LARGEST_ID];
static itemstats_t itemstats[LARGEST_ID];
static unsigned int sizes[LARGEST_ID];

static int crawler_count = 0;
static volatile int do_run_lru_crawler_thread = 0;
static int lru_crawler_initialized = 0;
static pthread_mutex_t lru_crawler_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  lru_crawler_cond = PTHREAD_COND_INITIALIZER;

void item_stats_reset(void) {
    mutex_lock(&cache_lock);
	//设置0
    memset(itemstats, 0, sizeof(itemstats));
    mutex_unlock(&cache_lock);
}


/* Get the next CAS id for a new item. */
uint64_t get_cas_id(void) {
	//静态变量
    static uint64_t cas_id = 0;
    return ++cas_id;
}

/* Enable this for reference-count debugging. */
#if 0
# define DEBUG_REFCNT(it,op) \
                fprintf(stderr, "item %x refcnt(%c) %d %c%c%c\n", \
                        it, op, it->refcount, \
                        (it->it_flags & ITEM_LINKED) ? 'L' : ' ', \
                        (it->it_flags & ITEM_SLABBED) ? 'S' : ' ')
#else
# define DEBUG_REFCNT(it,op) while(0)
#endif

/**
 * Generates the variable-sized part of the header for an object.
 *
 * key     - The key
 * nkey    - The length of the key
 * flags   - key flags
 * nbytes  - Number of bytes to hold value and addition CRLF terminator
 * suffix  - Buffer for the "VALUE" line suffix (flags, size).
 * nsuffix - The length of the suffix is stored here.
 *
 * Returns the total size of the header.
 */
static size_t item_make_header(const uint8_t nkey, const int flags, const int nbytes,
                     char *suffix, uint8_t *nsuffix) {
    /* suffix is defined at 40 chars elsewhere.. */
	//suffix目标str地址，格式为" %d %d\r\n"，两个参数
	//nsuffix指针参数可以把数据回传
	//suffix串为[空格flags空格(nbytes-2)]
    *nsuffix = (uint8_t) snprintf(suffix, 40, " %d %d\r\n", flags, nbytes - 2);
	//总大小=item的大小+key的大小nkey+suffix串的大小+数据的大小nbytes
	//内存结构为item+key+suffix串+数据
    return sizeof(item) + nkey + *nsuffix + nbytes;
}

/*@null@*/
item *do_item_alloc(char *key, const size_t nkey, const int flags,
                    const rel_time_t exptime, const int nbytes,
                    const uint32_t cur_hv) {
    uint8_t nsuffix;
    item *it = NULL;
    char suffix[40];
	//第一个参数为nkey+1
    size_t ntotal = item_make_header(nkey + 1, flags, nbytes, suffix, &nsuffix);
    if (settings.use_cas) {
		//这里对cas的情况有补充
        ntotal += sizeof(uint64_t);
    }

	//找到一个class
    unsigned int id = slabs_clsid(ntotal);
    if (id == 0)
        return 0;

    mutex_lock(&cache_lock);
    /* do a quick check if we have any expired items in the tail.. */
	//从lru的尾部查过期的item
    int tries = 5;
    int tried_alloc = 0;
    item *search;
    void *hold_lock = NULL;
	//全体失效时间
    rel_time_t oldest_live = settings.oldest_live;

	//取class队列的尾指针
    search = tails[id];
    /* We walk up *only* for locked items. Never searching for expired.
     * Waste of CPU for almost all deployments */
    for (; tries > 0 && search != NULL; tries--, search=search->prev) {
        if (search->nbytes == 0 && search->nkey == 0 && search->it_flags == 1) {
            /* We are a crawler, ignore it. */
			//跳过crawler
            tries++;
            continue;
        }
        uint32_t hv = hash(ITEM_key(search), search->nkey);
        /* Attempt to hash item lock the "search" item. If locked, no
         * other callers can incr the refcount
         */
        /* Don't accidentally grab ourselves, or bail if we can't quicklock */
        //accidentally--意外的，grab--夺取，bail--保释
		//item_trylock函数--寻找锁然后trylock
		if (hv == cur_hv || (hold_lock = item_trylock(hv)) == NULL)
            continue;
		
        /* Now see if the item is refcount locked */
        if (refcount_incr(&search->refcount) != 2) {
            refcount_decr(&search->refcount);
			//rare--罕见的
            /* Old rare bug could cause a refcount leak. We haven't seen
             * it in years, but we leave this code in to prevent failures
             * just in case */
			//表示原来的refcount不等于1，可能==0，可能>=2
			//tail_repair_time默认值是等于0的，因此不执行这段代码
			//这段代码似乎是处理引用计数泄露代码的
            if (settings.tail_repair_time &&
					//search->time最后访问时间
                    search->time + settings.tail_repair_time < current_time) {
                itemstats[id].tailrepairs++;
				//其它使用search变量的地方是否受影响？
                search->refcount = 1;
				//符合tail_repair_time时间，过期处理
				//从hash桶和lru中移除
				//unlink内部调用了一次do_item_remove
                do_item_unlink_nolock(search, hv);
            }
            if (hold_lock)
                item_trylock_unlock(hold_lock);
            continue;
        }

        /* Expired or flushed */
		//到这里表示refcount原来等于1，现在等于2的情况
		//和上面的判定条件不同
        if ((search->exptime != 0 && search->exptime < current_time)
				//oldest_live表示在oldest_live时间之前的数据失效
				|| (search->time <= oldest_live && oldest_live <= current_time)) {
            //search对象过期了
			itemstats[id].reclaimed++;
            if ((search->it_flags & ITEM_FETCHED) == 0) {
				//还没有标记过fetched，才自加一下
                itemstats[id].expired_unfetched++;
            }
            it = search;
			//用新的数据更新class
			//ITEM_ntotal(it)计算的结果和make_header不同
			//但是ntotal在make_header函数后处理了cas的情况
            slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
            
			//过期处理，it当前引用计数为2
			do_item_unlink_nolock(it, hv);
			//现在引用计数为1
            /* Initialize the item block: */
			//初始化为
            it->slabs_clsid = 0;
        } else if ((it = slabs_alloc(ntotal, id)) == NULL) {
			//search没过期，尝试分配内存，这里search引用计数原来为1，现在为2
			//这里是分配失败的情况
            tried_alloc = 1;
			//evict--依法回收
            if (settings.evict_to_free == 0) {
                itemstats[id].outofmemory++;
            } else {
				//这个slab的分配失败次数加1
                itemstats[id].evicted++;
                itemstats[id].evicted_time = current_time - search->time;
                if (search->exptime != 0)
                    itemstats[id].evicted_nonzero++;
                if ((search->it_flags & ITEM_FETCHED) == 0) {
                    itemstats[id].evicted_unfetched++;
                }
                it = search;
                slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
                do_item_unlink_nolock(it, hv);
				//这里it引用计数为1
                /* Initialize the item block: */
                it->slabs_clsid = 0;

                /* If we've just evicted an item, and the automover is set to
                 * angry bird mode, attempt to rip memory into this slab class.
                 * TODO: Move valid object detection into a function, and on a
                 * "successful" memory pull, look behind and see if the next alloc
                 * would be an eviction. Then kick off the slab mover before the
                 * eviction happens.
                 */
                if (settings.slab_automove == 2)
					//做内存页面balance
                    slabs_reassign(-1, id);
            }
        }

		//search引用计数减一还原,it如果为新分配的和search不是一个对象
        refcount_decr(&search->refcount);
        /* If hash values were equal, we don't grab a second lock */
        if (hold_lock)
            item_trylock_unlock(hold_lock);
		
		//如果没有continue,就会走到这个break
        break;
    } //for end

	//!tried_alloc表示没有经历内存分配失败
	//tries==0 || search==NULL表示for循环完毕
    if (!tried_alloc && (tries == 0 || search == NULL))
        it = slabs_alloc(ntotal, id);

    if (it == NULL) {
        itemstats[id].outofmemory++;
        mutex_unlock(&cache_lock);
        return NULL;
    }

    assert(it->slabs_clsid == 0);
	//如果it从链表里重用的，也应该从链表中去掉了，所以应该是！=heads[id]
    assert(it != heads[id]);

    /* Item initialization can happen outside of the lock; the item's already
     * been removed from the slab LRU.
     */
	//调用者的引用
    it->refcount = 1;     /* the caller will have a reference */
    mutex_unlock(&cache_lock);
    it->next = it->prev = it->h_next = 0;
	
	//修改slabs_clsid
    it->slabs_clsid = id;

    DEBUG_REFCNT(it, '*');
    it->it_flags = settings.use_cas ? ITEM_CAS : 0;
    it->nkey = nkey;
    it->nbytes = nbytes;
	//拷贝key
    memcpy(ITEM_key(it), key, nkey);
    it->exptime = exptime;
    memcpy(ITEM_suffix(it), suffix, (size_t)nsuffix);
    it->nsuffix = nsuffix;
    return it;
}

void item_free(item *it) {
    size_t ntotal = ITEM_ntotal(it);
    unsigned int clsid;
    assert((it->it_flags & ITEM_LINKED) == 0);
    assert(it != heads[it->slabs_clsid]);
    assert(it != tails[it->slabs_clsid]);
    assert(it->refcount == 0);

    /* so slab size changer can tell later if item is already free or not */
    clsid = it->slabs_clsid;
	
	//设置为0
    it->slabs_clsid = 0;
    DEBUG_REFCNT(it, 'F');
	
	//回到内存池
    slabs_free(it, ntotal, clsid);
}

/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
//exceed--超过
//能否找到classid
bool item_size_ok(const size_t nkey, const int flags, const int nbytes) {
    char prefix[40];
    uint8_t nsuffix;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes,
                                     prefix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

	//能否找到classid
    return slabs_clsid(ntotal) != 0;
}

//加入到链表头
static void item_link_q(item *it) { /* item is the new head */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(it != *head);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = 0;
    it->next = *head;
    if (it->next) it->next->prev = it;
    *head = it;
	
	//*tail在为0时才设置
    if (*tail == 0) *tail = it;
	
    sizes[it->slabs_clsid]++;
    return;
}

//从lru双向链表中去掉
static void item_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    sizes[it->slabs_clsid]--;
    return;
}


int do_item_link(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_LINK(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & (ITEM_LINKED|ITEM_SLABBED)) == 0);
    mutex_lock(&cache_lock);
	
	//添加linked标志位，修改time
    it->it_flags |= ITEM_LINKED;
    it->time = current_time;

    STATS_LOCK();
    stats.curr_bytes += ITEM_ntotal(it);
    stats.curr_items += 1;
    stats.total_items += 1;
    STATS_UNLOCK();

    /* Allocate a new CAS ID on link. */
    ITEM_set_cas(it, (settings.use_cas) ? get_cas_id() : 0);
	//添加到hash桶
    assoc_insert(it, hv);
	//添加到head
    item_link_q(it);
	//增加引用计数
    refcount_incr(&it->refcount);
    mutex_unlock(&cache_lock);

    return 1;
}

void do_item_unlink(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    mutex_lock(&cache_lock);
    if ((it->it_flags & ITEM_LINKED) != 0) {
		//去掉标志位
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
		//从hash表删除
        assoc_delete(ITEM_key(it), it->nkey, hv);
		
		//从lru队列中去掉
        item_unlink_q(it);
		
		//减引用计数，并判断
        do_item_remove(it);
    }
    mutex_unlock(&cache_lock);
}

/* FIXME: Is it necessary to keep this copy/pasted code? */
void do_item_unlink_nolock(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {
		//去标志位
        it->it_flags &= ~ITEM_LINKED;
		
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
		
		//过期了，从hash表里去掉
        assoc_delete(ITEM_key(it), it->nkey, hv);
		
		//从lru双向链表中去掉
        item_unlink_q(it);
		
        do_item_remove(it);
    }
}

void do_item_remove(item *it) {
    MEMCACHED_ITEM_REMOVE(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);
    assert(it->refcount > 0);

	//应用计数减一，并判断引用计数
    if (refcount_decr(&it->refcount) == 0) {
        item_free(it);
    }
}

//update访问时间和链表地址，没操作hash桶
void do_item_update(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        mutex_lock(&cache_lock);
        if ((it->it_flags & ITEM_LINKED) != 0) {
			//从链表中去掉
            item_unlink_q(it);
			//修改访问时间
            it->time = current_time;
			
			//加入到链表头
            item_link_q(it);
        }
        mutex_unlock(&cache_lock);
    }
}

int do_item_replace(item *it, item *new_it, const uint32_t hv) {
    MEMCACHED_ITEM_REPLACE(ITEM_key(it), it->nkey, it->nbytes,
                           ITEM_key(new_it), new_it->nkey, new_it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);
	
	//从hash桶和lru链表中去掉，减引用计数并检查
    do_item_unlink(it, hv);
	//放入hash桶和lru链表，并增加引用计数
    return do_item_link(new_it, hv);
}

/*@null@*/
//输出class lru队列中item的信息
char *do_item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes) {
    unsigned int memlimit = 2 * 1024 * 1024;   /* 2MB max response size */
    char *buffer;
    unsigned int bufcurr;
    item *it;
    unsigned int len;
    unsigned int shown = 0;
    char key_temp[KEY_MAX_LENGTH + 1];
    char temp[512];

	//取出class的队列头
    it = heads[slabs_clsid];

    buffer = malloc((size_t)memlimit);
    if (buffer == 0) return NULL;
    bufcurr = 0;

	//limit==0无限制
    while (it != NULL && (limit == 0 || shown < limit)) {
        assert(it->nkey <= KEY_MAX_LENGTH);
        if (it->nbytes == 0 && it->nkey == 0) {
            it = it->next;
            continue;
        }
        /* Copy the key since it may not be null-terminated in the struct */
        //拷贝到临时key_temp
		strncpy(key_temp, ITEM_key(it), it->nkey);
		//设置数组元素
        key_temp[it->nkey] = 0x00; /* terminate */
		
		//拷贝内容到temp中
        len = snprintf(temp, sizeof(temp), "ITEM %s [%d b; %lu s]\r\n",
                       key_temp, it->nbytes - 2,
                       (unsigned long)it->exptime + process_started);
        if (bufcurr + len + 6 > memlimit)  /* 6 is END\r\n\0 */
            break;
        memcpy(buffer + bufcurr, temp, len);
        bufcurr += len;
        shown++;
        it = it->next;
    }

	//"END\r\n"--数组为6
    memcpy(buffer + bufcurr, "END\r\n", 6);
    bufcurr += 5;

    *bytes = bufcurr;
    return buffer;
}

//获取itemstats[i].evicted数据
void item_stats_evictions(uint64_t *evicted) {
    int i;
    mutex_lock(&cache_lock);
    for (i = 0; i < LARGEST_ID; i++) {
        evicted[i] = itemstats[i].evicted;
    }
    mutex_unlock(&cache_lock);
}

void do_item_stats_totals(ADD_STAT add_stats, void *c) {
    itemstats_t totals;
    memset(&totals, 0, sizeof(itemstats_t));
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        totals.expired_unfetched += itemstats[i].expired_unfetched;
        totals.evicted_unfetched += itemstats[i].evicted_unfetched;
        totals.evicted += itemstats[i].evicted;
        totals.reclaimed += itemstats[i].reclaimed;
        totals.crawler_reclaimed += itemstats[i].crawler_reclaimed;
    }
    APPEND_STAT("expired_unfetched", "%llu",
                (unsigned long long)totals.expired_unfetched);
    APPEND_STAT("evicted_unfetched", "%llu",
                (unsigned long long)totals.evicted_unfetched);
    APPEND_STAT("evictions", "%llu",
                (unsigned long long)totals.evicted);
    APPEND_STAT("reclaimed", "%llu",
                (unsigned long long)totals.reclaimed);
    APPEND_STAT("crawler_reclaimed", "%llu",
                (unsigned long long)totals.crawler_reclaimed);
}

void do_item_stats(ADD_STAT add_stats, void *c) {
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        if (tails[i] != NULL) {
            const char *fmt = "items:%d:%s";
            char key_str[STAT_KEY_LEN];
            char val_str[STAT_VAL_LEN];
            int klen = 0, vlen = 0;
            if (tails[i] == NULL) {
                /* We removed all of the items in this slab class */
                continue;
            }
            APPEND_NUM_FMT_STAT(fmt, i, "number", "%u", sizes[i]);
            APPEND_NUM_FMT_STAT(fmt, i, "age", "%u", current_time - tails[i]->time);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted",
                                "%llu", (unsigned long long)itemstats[i].evicted);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_nonzero",
                                "%llu", (unsigned long long)itemstats[i].evicted_nonzero);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_time",
                                "%u", itemstats[i].evicted_time);
            APPEND_NUM_FMT_STAT(fmt, i, "outofmemory",
                                "%llu", (unsigned long long)itemstats[i].outofmemory);
            APPEND_NUM_FMT_STAT(fmt, i, "tailrepairs",
                                "%llu", (unsigned long long)itemstats[i].tailrepairs);
            APPEND_NUM_FMT_STAT(fmt, i, "reclaimed",
                                "%llu", (unsigned long long)itemstats[i].reclaimed);
            APPEND_NUM_FMT_STAT(fmt, i, "expired_unfetched",
                                "%llu", (unsigned long long)itemstats[i].expired_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_unfetched",
                                "%llu", (unsigned long long)itemstats[i].evicted_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "crawler_reclaimed",
                                "%llu", (unsigned long long)itemstats[i].crawler_reclaimed);
        }
    }

    /* getting here means both ascii and binary terminators fit */
    add_stats(NULL, 0, NULL, 0, c);
}

/** dumps out a list of objects of each size, with granularity of 32 bytes */
/*@null@*/
void do_item_stats_sizes(ADD_STAT add_stats, void *c) {

    /* max 1MB object, divided into 32 bytes size buckets */
    const int num_buckets = 32768;
    unsigned int *histogram = calloc(num_buckets, sizeof(int));

    if (histogram != NULL) {
        int i;

        /* build the histogram */
        for (i = 0; i < LARGEST_ID; i++) {
            item *iter = heads[i];
            while (iter) {
                int ntotal = ITEM_ntotal(iter);
                int bucket = ntotal / 32;
                if ((ntotal % 32) != 0) bucket++;
                if (bucket < num_buckets) histogram[bucket]++;
                iter = iter->next;
            }
        }

        /* write the buffer */
        for (i = 0; i < num_buckets; i++) {
            if (histogram[i] != 0) {
                char key[8];
                snprintf(key, sizeof(key), "%d", i * 32);
                APPEND_STAT(key, "%u", histogram[i]);
            }
        }
        free(histogram);
    }
    add_stats(NULL, 0, NULL, 0, c);
}

/** wrapper around assoc_find which does the lazy expiration logic */
item *do_item_get(const char *key, const size_t nkey, const uint32_t hv) {
    //mutex_lock(&cache_lock);
    item *it = assoc_find(key, nkey, hv);
    if (it != NULL) {
		//在hash桶里
		//增加引用计数,get一次增加一次
        refcount_incr(&it->refcount);
        /* Optimization for slab reassignment. prevents popular items from
         * jamming in busy wait. Can only do this here to satisfy lock order
         * of item_lock, cache_lock, slabs_lock. */
		
		//jamming--人为干扰
        if (slab_rebalance_signal &&
            ((void *)it >= slab_rebal.slab_start && (void *)it < slab_rebal.slab_end)) {
			//如果当前内存页在rebalance,it删除
            do_item_unlink_nolock(it, hv);
            do_item_remove(it);
            it = NULL;
        }
    }
    //mutex_unlock(&cache_lock);
    int was_found = 0;

    if (settings.verbose > 2) {
        int ii;
        if (it == NULL) {
            fprintf(stderr, "> NOT FOUND ");
        } else {
            fprintf(stderr, "> FOUND KEY ");
            was_found++;
        }
        for (ii = 0; ii < nkey; ++ii) {
			//打印key的每个字符
            fprintf(stderr, "%c", key[ii]);
        }
    }

    if (it != NULL) {
        if (settings.oldest_live != 0 && settings.oldest_live <= current_time &&
            it->time <= settings.oldest_live) {
			//it过期，oldest以前的全过期
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
				//was_found在settings.verbose条件下才修改
                fprintf(stderr, " -nuked by flush");
            }
        } else if (it->exptime != 0 && it->exptime <= current_time) {
			//it过期
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by expire");
            }
        } else {
			//没过期，设置表示检查过？
            it->it_flags |= ITEM_FETCHED;
            DEBUG_REFCNT(it, '+');
        }
    }

    if (settings.verbose > 2)
        fprintf(stderr, "\n");

    return it;
}

item *do_item_touch(const char *key, size_t nkey, uint32_t exptime,
                    const uint32_t hv) {
    item *it = do_item_get(key, nkey, hv);
    if (it != NULL) {
        it->exptime = exptime;
    }
    return it;
}

/* expires items that are more recent than the oldest_live setting. */
void do_item_flush_expired(void) {
    int i;
    item *iter, *next;
    if (settings.oldest_live == 0)
        return;
    for (i = 0; i < LARGEST_ID; i++) {
        /* The LRU is sorted in decreasing time order, and an item's timestamp
         * is never newer than its last access time, so we only need to walk
         * back until we hit an item older than the oldest_live time.
         * The oldest_live checking will auto-expire the remaining items.
         */
        for (iter = heads[i]; iter != NULL; iter = next) {
            /* iter->time of 0 are magic objects. */
            if (iter->time != 0 && iter->time >= settings.oldest_live) {
                next = iter->next;
                if ((iter->it_flags & ITEM_SLABBED) == 0) {
                    do_item_unlink_nolock(iter, hash(ITEM_key(iter), iter->nkey));
                }
            } else {
                /* We've hit the first old item. Continue to the next queue. */
                break;
            }
        }
    }
}

//放入lru双向链表尾部
static void crawler_link_q(item *it) { /* item is the new tail */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(*tail != 0);
    assert(it != *tail);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
	
	//放入tail尾部
    it->prev = *tail;
    it->next = 0;
    if (it->prev) {
        assert(it->prev->next == 0);
        it->prev->next = it;
    }
    *tail = it;
	
	//当*head为0时，放入head
    if (*head == 0) *head = it;
    return;
}

//从lru链表中删除
static void crawler_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    return;
}

/* This is too convoluted, but it's a difficult shuffle. Try to rewrite it
 * more clearly. */
//convoluted--复杂的
//shuffle--洗牌
static item *crawler_crawl_q(item *it) {
    item **head, **tail;
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);
    assert(it->slabs_clsid < LARGEST_ID);
	//取出对应class的队列
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    /* We've hit the head, pop off */
    if (it->prev == 0) {
		//如果没有prev
        assert(*head == it);
        if (it->next) {
			//如果有next
			//用二级指针修改头，去掉it
            *head = it->next;
            assert(it->next->prev == it);
            it->next->prev = 0;
        }
		//返回NULL
        return NULL; /* Done */
    }

    /* Swing ourselves in front of the next item */
    /* NB: If there is a prev, we can't be the head */
    assert(it->prev != it);
    if (it->prev) {
		//必然有prev
        if (*head == it->prev) {
            /* Prev was the head, now we're the head */
			//如果it是第二个，头指向第二个
            *head = it;
        }
        if (*tail == it) {
            /* We are the tail, now they are the tail */
			//如果it是最后一个，尾指向前一个
            *tail = it->prev;
        }
        assert(it->next != it);
        if (it->next) {
			//如果有next，next接到prev后面，去掉it
            assert(it->prev->next == it);
            it->prev->next = it->next;
            it->next->prev = it->prev;
        } else {
            /* Tail. Move this above? */
			//如果没有next，设置prev的next为0，去掉it
            it->prev->next = 0;
        }
        /* prev->prev's next is it->prev */
		//这里prev肯定存在
		//it->next已经备份到prev的next上了
		//it->next设置为prev
        it->next = it->prev;
		//新next的prev变成it的prev
        it->prev = it->next->prev;
		//相当于把it插入到原来prev的前面
        it->next->prev = it;
        /* New it->prev now, if we're not at the head. */
        if (it->prev) {
			//如果有prev，修改prev的next为it
            it->prev->next = it;
        }
    }
    assert(it->next != it);
    assert(it->prev != it);

	//返回新的next，也就是旧的prev
    return it->next; /* success */
}

/* I pulled this out to make the main thread clearer, but it reaches into the
 * main thread's values too much. Should rethink again.
 */
static void item_crawler_evaluate(item *search, uint32_t hv, int i) {
    rel_time_t oldest_live = settings.oldest_live;
    if ((search->exptime != 0 && search->exptime < current_time)
        || (search->time <= oldest_live && oldest_live <= current_time)) {
		//如果search过期了
        itemstats[i].crawler_reclaimed++;

        if (settings.verbose > 1) {
            int ii;
            char *key = ITEM_key(search);
            fprintf(stderr, "LRU crawler found an expired item (flags: %d, slab: %d): ",
                search->it_flags, search->slabs_clsid);
            for (ii = 0; ii < search->nkey; ++ii) {
                fprintf(stderr, "%c", key[ii]);
            }
            fprintf(stderr, "\n");
        }
        if ((search->it_flags & ITEM_FETCHED) == 0) {
            itemstats[i].expired_unfetched++;
        }
        do_item_unlink_nolock(search, hv);
        do_item_remove(search);
        assert(search->slabs_clsid == 0);
    } else {
		//如果没过期
        refcount_decr(&search->refcount);
    }
}

static void *item_crawler_thread(void *arg) {
    int i;

    pthread_mutex_lock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "Starting LRU crawler background thread\n");
    while (do_run_lru_crawler_thread) {
    pthread_cond_wait(&lru_crawler_cond, &lru_crawler_lock);

    while (crawler_count) {
        item *search = NULL;
        void *hold_lock = NULL;

        for (i = 0; i < LARGEST_ID; i++) {
            if (crawlers[i].it_flags != 1) {
                continue;
            }
            pthread_mutex_lock(&cache_lock);
			//前移item，返回原prev，每个item在不同的队列
            search = crawler_crawl_q((item *)&crawlers[i]);
            if (search == NULL ||
					//先做自减
					(crawlers[i].remaining && --crawlers[i].remaining < 1)) {
				//没找到search或者自减后remaining<1
                if (settings.verbose > 2)
                    fprintf(stderr, "Nothing left to crawl for %d\n", i);
                crawlers[i].it_flags = 0;
                crawler_count--;
				//从链表中删除
                crawler_unlink_q((item *)&crawlers[i]);
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            uint32_t hv = hash(ITEM_key(search), search->nkey);
            /* Attempt to hash item lock the "search" item. If locked, no
             * other callers can incr the refcount
             */
			//trylock成功，返回hold_lock
            if ((hold_lock = item_trylock(hv)) == NULL) {
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            /* Now see if the item is refcount locked */
            if (refcount_incr(&search->refcount) != 2) {
                refcount_decr(&search->refcount);
                if (hold_lock)
                    item_trylock_unlock(hold_lock);
                pthread_mutex_unlock(&cache_lock);
                continue;
            }

            /* Frees the item or decrements the refcount. */
            /* Interface for this could improve: do the free/decr here
             * instead? */
			//到这里表明refcount==2
            item_crawler_evaluate(search, hv, i);

            if (hold_lock)
                item_trylock_unlock(hold_lock);
            pthread_mutex_unlock(&cache_lock);

            if (settings.lru_crawler_sleep)
                usleep(settings.lru_crawler_sleep);
        }
    }
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread sleeping\n");
    STATS_LOCK();
    stats.lru_crawler_running = false;
    STATS_UNLOCK();
    }
    pthread_mutex_unlock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread stopping\n");

    return NULL;
}

static pthread_t item_crawler_tid;

int stop_item_crawler_thread(void) {
    int ret;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 0;
    pthread_cond_signal(&lru_crawler_cond);
    pthread_mutex_unlock(&lru_crawler_lock);
    if ((ret = pthread_join(item_crawler_tid, NULL)) != 0) {
        fprintf(stderr, "Failed to stop LRU crawler thread: %s\n", strerror(ret));
        return -1;
    }
    settings.lru_crawler = false;
    return 0;
}

int start_item_crawler_thread(void) {
    int ret;

    if (settings.lru_crawler)
        return -1;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 1;
    settings.lru_crawler = true;
    if ((ret = pthread_create(&item_crawler_tid, NULL,
        item_crawler_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create LRU crawler thread: %s\n",
            strerror(ret));
        pthread_mutex_unlock(&lru_crawler_lock);
        return -1;
    }
    pthread_mutex_unlock(&lru_crawler_lock);

    return 0;
}

//在队列尾部放入一个crawler类型元素
enum crawler_result_type lru_crawler_crawl(char *slabs) {
    char *b = NULL;
    uint32_t sid = 0;
    uint8_t tocrawl[POWER_LARGEST];
    if (pthread_mutex_trylock(&lru_crawler_lock) != 0) {
        return CRAWLER_RUNNING;
    }
    pthread_mutex_lock(&cache_lock);

    if (strcmp(slabs, "all") == 0) {
        for (sid = 0; sid < LARGEST_ID; sid++) {
            tocrawl[sid] = 1;
        }
    } else {
        for (char *p = strtok_r(slabs, ",", &b);
             p != NULL;
             p = strtok_r(NULL, ",", &b)) {

            if (!safe_strtoul(p, &sid) || sid < POWER_SMALLEST
                    || sid > POWER_LARGEST) {
                pthread_mutex_unlock(&cache_lock);
                pthread_mutex_unlock(&lru_crawler_lock);
                return CRAWLER_BADCLASS;
            }
			//标记对应id的数组元素
            tocrawl[sid] = 1;
        }
    }

    for (sid = 0; sid < LARGEST_ID; sid++) {
		//tocrawl是标志位数组
		//tails是class的队列的数组
        if (tocrawl[sid] != 0 && tails[sid] != NULL) {
            if (settings.verbose > 2)
                fprintf(stderr, "Kicking LRU crawler off for slab %d\n", sid);
            //一个crawler类型的数组
			crawlers[sid].nbytes = 0;
            crawlers[sid].nkey = 0;
            crawlers[sid].it_flags = 1; /* For a crawler, this means enabled. */
            crawlers[sid].next = 0;
            crawlers[sid].prev = 0;
            crawlers[sid].time = 0;
            crawlers[sid].remaining = settings.lru_crawler_tocrawl;
            crawlers[sid].slabs_clsid = sid;
			//强转为item*，前几个字段都一样，放入队列尾部
            crawler_link_q((item *)&crawlers[sid]);
            crawler_count++;
        }
    }
    pthread_mutex_unlock(&cache_lock);
    pthread_cond_signal(&lru_crawler_cond);
    STATS_LOCK();
    stats.lru_crawler_running = true;
    STATS_UNLOCK();
    pthread_mutex_unlock(&lru_crawler_lock);
    return CRAWLER_OK;
}

//crawler--爬行者
int init_lru_crawler(void) {
	//判断是否已经初始化
    if (lru_crawler_initialized == 0) {
		//初始化
        if (pthread_cond_init(&lru_crawler_cond, NULL) != 0) {
            fprintf(stderr, "Can't initialize lru crawler condition\n");
            return -1;
        }
		//初始化
        pthread_mutex_init(&lru_crawler_lock, NULL);
		//改flag
        lru_crawler_initialized = 1;
    }
    return 0;
}
