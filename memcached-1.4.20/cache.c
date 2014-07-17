/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#ifndef NDEBUG
#include <signal.h>
#endif

#include "cache.h"

#ifndef NDEBUG
//8字节64位无符号int，做buffer-check使用
const uint64_t redzone_pattern = 0xdeadbeefcafebabe;
int cache_error = 0;
#endif

const int initial_pool_size = 64;

//构建void** ptr二级数组缓存
cache_t* cache_create(const char *name, size_t bufsize, size_t align,
					  //函数指针
                      cache_constructor_t* constructor,
					  //函数指针
                      cache_destructor_t* destructor) {
    cache_t* ret = calloc(1, sizeof(cache_t));
	
	//strdup()在内部调用了malloc()为变量分配内存
    char* nm = strdup(name);
    void** ptr = calloc(initial_pool_size, sizeof(void*));
    if (ret == NULL || nm == NULL || ptr == NULL ||
        pthread_mutex_init(&ret->mutex, NULL) == -1) {
        free(ret);
        free(nm);
        free(ptr);
        return NULL;
    }

	//给cache_t* ret赋值
    ret->name = nm;
    ret->ptr = ptr;
    ret->freetotal = initial_pool_size;
    ret->constructor = constructor;
    ret->destructor = destructor;

#ifndef NDEBUG
	//bufsize+2个64位uint的大小
    ret->bufsize = bufsize + 2 * sizeof(redzone_pattern);
#else
    ret->bufsize = bufsize;
#endif

    return ret;
}

static inline void* get_object(void *ptr) {
#ifndef NDEBUG
    uint64_t *pre = ptr;
	//按uint类型移动指针
    return pre + 1;
#else
    return ptr;
#endif
}

void cache_destroy(cache_t *cache) {
    while (cache->freecurr > 0) {
        void *ptr = cache->ptr[--cache->freecurr];
        if (cache->destructor) {
			//析构get_object返回的地址
            cache->destructor(get_object(ptr), NULL);
        }
        free(ptr);
    }
    free(cache->name);
    free(cache->ptr);
    pthread_mutex_destroy(&cache->mutex);
    free(cache);
}

void* cache_alloc(cache_t *cache) {
    void *ret;
    void *object;
    pthread_mutex_lock(&cache->mutex);
    if (cache->freecurr > 0) {
		//获取第一个free的地址
        ret = cache->ptr[--cache->freecurr];
		//get_object返回处理后的地址
        object = get_object(ret);
    } else {
        object = ret = malloc(cache->bufsize);
        if (ret != NULL) {
            object = get_object(ret);

            if (cache->constructor != NULL &&
                cache->constructor(object, NULL, 0) != 0) {
                free(ret);
                object = NULL;
            }
        }
    }
    pthread_mutex_unlock(&cache->mutex);

#ifndef NDEBUG
    if (object != NULL) {
        /* add a simple form of buffer-check */
		//ret转型uint64
        uint64_t *pre = ret;
		//给指针pre的前64位赋值
        *pre = redzone_pattern;
		//ret移动到数据的地址，跳过前64位
        ret = pre+1;
		//ret的数据后面64位也拷贝为redzone_pattern，做buffer-check
		//其中ret已经是后移64位到数据开始地址了
		//cache->bufsize-(2*sizeof(redzone_pattern))--数据的大小
        memcpy(((char*)ret) + cache->bufsize - (2 * sizeof(redzone_pattern)),
               &redzone_pattern, sizeof(redzone_pattern));
    }
#endif

    return object;
}

void cache_free(cache_t *cache, void *ptr) {
    pthread_mutex_lock(&cache->mutex);

#ifndef NDEBUG
    /* validate redzone... */
	//地址+数据长度，校验数据后面的redzone_pattern
    if (memcmp(((char*)ptr) + cache->bufsize - (2 * sizeof(redzone_pattern)),
               &redzone_pattern, sizeof(redzone_pattern)) != 0) {
        raise(SIGABRT);
        cache_error = 1;
        pthread_mutex_unlock(&cache->mutex);
        return;
    }
    uint64_t *pre = ptr;
	//向前移动64位
    --pre;
	//校验数据前面的redzone_pattern
    if (*pre != redzone_pattern) {
        raise(SIGABRT);
        cache_error = -1;
        pthread_mutex_unlock(&cache->mutex);
        return;
    }
	//前移后的地址复制给ptr
    ptr = pre;
#endif
    if (cache->freecurr < cache->freetotal) {
        cache->ptr[cache->freecurr++] = ptr;
    } else {
        /* try to enlarge free connections array */
        size_t newtotal = cache->freetotal * 2;
        void **new_free = realloc(cache->ptr, sizeof(char *) * newtotal);
        if (new_free) {
            cache->freetotal = newtotal;
            cache->ptr = new_free;
            cache->ptr[cache->freecurr++] = ptr;
        } else {
            if (cache->destructor) {
                cache->destructor(ptr, NULL);
            }
            free(ptr);

        }
    }
    pthread_mutex_unlock(&cache->mutex);
}

