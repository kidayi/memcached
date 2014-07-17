/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#ifndef NDEBUG
#include <signal.h>
#endif

#include "cache.h"

#ifndef NDEBUG
//8�ֽ�64λ�޷���int����buffer-checkʹ��
const uint64_t redzone_pattern = 0xdeadbeefcafebabe;
int cache_error = 0;
#endif

const int initial_pool_size = 64;

//����void** ptr�������黺��
cache_t* cache_create(const char *name, size_t bufsize, size_t align,
					  //����ָ��
                      cache_constructor_t* constructor,
					  //����ָ��
                      cache_destructor_t* destructor) {
    cache_t* ret = calloc(1, sizeof(cache_t));
	
	//strdup()���ڲ�������malloc()Ϊ���������ڴ�
    char* nm = strdup(name);
    void** ptr = calloc(initial_pool_size, sizeof(void*));
    if (ret == NULL || nm == NULL || ptr == NULL ||
        pthread_mutex_init(&ret->mutex, NULL) == -1) {
        free(ret);
        free(nm);
        free(ptr);
        return NULL;
    }

	//��cache_t* ret��ֵ
    ret->name = nm;
    ret->ptr = ptr;
    ret->freetotal = initial_pool_size;
    ret->constructor = constructor;
    ret->destructor = destructor;

#ifndef NDEBUG
	//bufsize+2��64λuint�Ĵ�С
    ret->bufsize = bufsize + 2 * sizeof(redzone_pattern);
#else
    ret->bufsize = bufsize;
#endif

    return ret;
}

static inline void* get_object(void *ptr) {
#ifndef NDEBUG
    uint64_t *pre = ptr;
	//��uint�����ƶ�ָ��
    return pre + 1;
#else
    return ptr;
#endif
}

void cache_destroy(cache_t *cache) {
    while (cache->freecurr > 0) {
        void *ptr = cache->ptr[--cache->freecurr];
        if (cache->destructor) {
			//����get_object���صĵ�ַ
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
		//��ȡ��һ��free�ĵ�ַ
        ret = cache->ptr[--cache->freecurr];
		//get_object���ش����ĵ�ַ
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
		//retת��uint64
        uint64_t *pre = ret;
		//��ָ��pre��ǰ64λ��ֵ
        *pre = redzone_pattern;
		//ret�ƶ������ݵĵ�ַ������ǰ64λ
        ret = pre+1;
		//ret�����ݺ���64λҲ����Ϊredzone_pattern����buffer-check
		//����ret�Ѿ��Ǻ���64λ�����ݿ�ʼ��ַ��
		//cache->bufsize-(2*sizeof(redzone_pattern))--���ݵĴ�С
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
	//��ַ+���ݳ��ȣ�У�����ݺ����redzone_pattern
    if (memcmp(((char*)ptr) + cache->bufsize - (2 * sizeof(redzone_pattern)),
               &redzone_pattern, sizeof(redzone_pattern)) != 0) {
        raise(SIGABRT);
        cache_error = 1;
        pthread_mutex_unlock(&cache->mutex);
        return;
    }
    uint64_t *pre = ptr;
	//��ǰ�ƶ�64λ
    --pre;
	//У������ǰ���redzone_pattern
    if (*pre != redzone_pattern) {
        raise(SIGABRT);
        cache_error = -1;
        pthread_mutex_unlock(&cache->mutex);
        return;
    }
	//ǰ�ƺ�ĵ�ַ���Ƹ�ptr
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

