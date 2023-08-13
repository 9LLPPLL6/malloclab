/*
 * 基于隐式简单空闲链表实现
 * 块大小8字节对齐，有效载荷8字节对齐
 * 块有一个一个字的头部，头部记录块大小，最低位记录分配情况，第二低位记录前一个块的空闲情况
 * 空闲块有一个脚部（头部的副本），已分配块没有
 * 采取立即合并
 * 下一次适配
 * 使用分割
 * 最小块大小是8字节
 * 堆起始有一个4字节对齐填充块，有一个8字节只有头部和脚部的序言块（8/1），堆结尾有一个结尾块，只有头部，（0/1）
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "glimmer",
    /* First member's full name */
    "lee",
    /* First member's email address */
    "LLP_PLL@look.out",
    /* Second member's full name */
    "lpl",
    /* Second member's email address */
    "239148349@qq.com"};

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void printf_list(char *start_block);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 向上舍入到最接近的对齐倍数*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SWORD 4                                                               // 单字
#define DWORD 8                                                               // 双字
#define CHUNKSIZE (1 << 12)                                                   // 默认扩展堆大小
#define PACK(size, alloc, prealloc) ((size) | (alloc) | ((prealloc) << (1)))  // 赋值给头部和脚部
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))                          // 把val存在p指向的一个字中
#define GET(p) (*((unsigned int *)(p)))                                       // 取p指向的一个字中的值
#define GET_SIZE(p) ((GET(p)) & (~0x7))                                       // 取块大小
#define GET_ALLOC(p) ((GET(p)) & (0x1))                                       // 取分配位
#define GET_PREALLOC(p) (((GET(p)) & (0x2)) >> (1))                           // 取前一个块的分配位
#define HEAD(bp) (((char *)(bp)) - (SWORD))                                   // 得到块的头部
#define FTRP(bp) (((char *)(bp)) + (GET_SIZE(HEAD(bp))) - (DWORD))            // 得到脚部
#define NEXT_BLOCK(bp) (((char *)(bp)) + (GET_SIZE(HEAD(bp))))                // 下一个块指针
#define PRE_BLOCK(bp) (((char *)(bp)) - (GET_SIZE(((char *)(bp)) - (DWORD)))) // 上一个块指针
#define MAX(x, y) ((x) > (y) ? (x) : (y))                                     // 返回较大值
#define MIN(x, y) ((x) < (y) ? (x) : (y))                                     // 返回较小值

char *heap_list; // 指向序言块
char *fit_p;     // 指向上一次分配的块的下一块
/*
 * mm_init - initialize the malloc package.
 * 正常返回0，有问题返回-1
 */
int mm_init(void)
{
    if ((heap_list = mem_sbrk(4 * SWORD)) == ((void *)-1))
        return -1;
    PUT(heap_list, 0);
    PUT(heap_list + SWORD * 1, PACK(DWORD, 1, 1));
    PUT(heap_list + SWORD * 2, PACK(DWORD, 1, 1));
    PUT(heap_list + SWORD * 3, PACK(0, 1, 1));
    heap_list += DWORD;
    if (extend_heap(2*DWORD / SWORD) == NULL)
        return -1;
    fit_p = heap_list + DWORD;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t block_size, extend_size;
    char *bp;
    if (size == 0)
        return NULL;
    if (size <= SWORD)
        block_size = 8;
    else
        block_size = ((size + SWORD + (DWORD - 1)) / DWORD) * DWORD;
    bp = find_fit(block_size);
    if (bp)
        place(bp, block_size);
    else
    {
        extend_size = MAX(block_size, CHUNKSIZE);
        bp = extend_heap(extend_size / SWORD);
        if (bp)
            place(bp, block_size);
    }
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HEAD(ptr));
    unsigned int prealloc = GET_PREALLOC(((char *)(ptr)) - 4);
    PUT(FTRP(ptr), PACK(size, 0, prealloc));
    PUT(HEAD(ptr), PACK(size, 0, prealloc));
    size_t next_size = GET_SIZE(HEAD(NEXT_BLOCK(ptr)));
    unsigned int alloc = GET_ALLOC(HEAD(NEXT_BLOCK(ptr)));
    PUT(HEAD(NEXT_BLOCK(ptr)), PACK(next_size, alloc, 0));
    if (alloc == 0)
        PUT((char *)(ptr) + size + next_size - 8, PACK(next_size, alloc, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr;
    char *next_bp;
    size_t new_size, next_bsize, old_size;
    unsigned int next_alloc, old_prealloc;
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }
    // 计算新块的大小
    if (size <= SWORD)
        new_size = 8;
    else
        new_size = ((size + SWORD + (DWORD - 1)) / DWORD) * DWORD;
    // 计算旧块的大小
    old_size = GET_SIZE(((char *)(ptr)) - 4);
    old_prealloc = GET_PREALLOC((char *)(ptr)-4);
    if (new_size == old_size)
        return ptr;
    else if (new_size > old_size)
    {
        next_bp = NEXT_BLOCK(ptr);
        next_bsize = GET_SIZE(HEAD(next_bp));
        next_alloc = GET_ALLOC(HEAD(next_bp));
        if ((next_alloc == 0) && ((old_size + next_bsize) >= new_size)) // 下一个块是空闲块且大小足够
        {
            if ((old_size + next_bsize - new_size) < 8) // 不分割
            {
                if (fit_p == (char *)(NEXT_BLOCK(ptr)))
                    fit_p = (char *)(NEXT_BLOCK(NEXT_BLOCK(ptr)));
                char *p = ((char *)(ptr) + (old_size + next_bsize) - 4);
                size_t size1 = GET_SIZE(p);
                unsigned int alloc1 = GET_ALLOC(p);
                PUT(p, PACK(size1, alloc1, 1));
                PUT((char *)(ptr)-4, PACK(old_size + next_bsize, 1, old_prealloc));
            }
            else // 分割
            {
                size_t now_size = old_size + next_bsize - new_size;
                PUT((char *)(ptr)-4, PACK(new_size, 1, old_prealloc));
                PUT((char *)(ptr) + new_size - 4, PACK(now_size, 0, 1));
                PUT((char *)(ptr) + old_size + next_bsize - 8, PACK(now_size, 0, 1));
                if ((fit_p == (char *)(NEXT_BLOCK(ptr))))
                    fit_p = (char *)(ptr) + new_size;
                coalesce((char *)(ptr) + new_size);
            }
            return ptr;
        }
        else // 下一个块不是空闲块或者块大小不足够
        {
            new_ptr = mm_malloc(size);
            int length = (old_size - 4) / 4;
            unsigned int *ulptr = (unsigned int *)ptr;
            unsigned int *ulnew_ptr = (unsigned int *)new_ptr;
            for (int i = 0; i < length; i++)
            {
                *ulnew_ptr = *ulptr;
                ulnew_ptr++;
                ulptr++;
            }
            mm_free(ptr);
            return new_ptr;
        }
    }
    else // 旧块比新块大
    {
        unsigned int n_alloc = GET_ALLOC((char *)(ptr) + old_size - 4);
        if (n_alloc == 0 || (old_size - new_size) >= 8)
        {
            PUT(HEAD(ptr), PACK(new_size, 1, old_prealloc));
            PUT((char *)(ptr) + new_size - 4, PACK(old_size - new_size, 0, 1));
            PUT((char *)(ptr) + old_size - 8, PACK(old_size - new_size, 0, 1));
            size_t size2 = GET_SIZE((char *)(ptr) + old_size - 4);
            PUT((char *)(ptr) + old_size - 4, PACK(size2, n_alloc, 0));
            if (n_alloc == 0)
            {
                PUT((char *)(ptr) + old_size + size2 - 8, PACK(size2, n_alloc, 0));
                coalesce((char *)(ptr) + new_size);
            }
        }
        return ptr;
    }
}

/*
 * 以空闲块的方式扩展堆，成功返回指向空闲块的指针，失败返回NULL
 */
static void *extend_heap(size_t words)
{
    size_t size;
    char *bp;
    size = ((words % 2) == 0 ? (words * SWORD) : (words + 1) * SWORD);
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        // printf_list((char *)(heap_list) + 8);
        return NULL;
    }
    // printf_list((char *)(heap_list) + 8);
    unsigned int prealloc = GET_PREALLOC(((char *)(bp)) - 4);
    PUT((char *)(bp)-4, PACK(size, 0, prealloc));
    PUT((char *)(bp) + size - DWORD, PACK(size, 0, prealloc));
    PUT((char *)(bp) + size - SWORD, PACK(0, 1, 0));
    return coalesce(bp);
}
/*
 *合并空闲块,返回指向该空闲块的指针
 */
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HEAD(bp));
    unsigned int next_alloc = GET_ALLOC(HEAD(NEXT_BLOCK(bp)));
    unsigned int prev_alloc = GET_PREALLOC((char *)(bp)-4);
    size_t next_size = GET_SIZE(HEAD(NEXT_BLOCK(bp)));
    size_t prev_size;
    if (next_alloc && prev_alloc)
        return bp;
    else if (next_alloc && !prev_alloc)
    {
        prev_size = GET_SIZE(HEAD(PRE_BLOCK(bp)));
        size = size + prev_size;
        unsigned int pal = GET_PREALLOC((char *)(PRE_BLOCK(bp)) - 4);
        PUT(HEAD(PRE_BLOCK(bp)), PACK(size, 0, pal));
        PUT(FTRP(bp), PACK(size, 0, pal));
        if (fit_p == (char *)(bp))
            fit_p = (char *)PRE_BLOCK(bp);
        return PRE_BLOCK(bp);
    }
    else if (prev_alloc && !next_alloc)
    {
        if (fit_p == (char *)(NEXT_BLOCK(bp)))
            fit_p = (char *)bp;
        size += next_size;
        unsigned int pal = GET_PREALLOC((char *)(bp)-4);
        PUT(HEAD(bp), PACK(size, 0, pal));
        PUT(((char *)(bp)) + size - DWORD, PACK(size, 0, pal));
        return bp;
    }
    else
    {
        if ((fit_p == (char *)(NEXT_BLOCK(bp))) || (fit_p == (char *)(bp)))
            fit_p = (char *)PRE_BLOCK(bp);
        prev_size = GET_SIZE(HEAD(PRE_BLOCK(bp)));
        size = size + prev_size + next_size;
        unsigned int pal = GET_PREALLOC((char *)(PRE_BLOCK(bp)) - 4);
        PUT(HEAD(PRE_BLOCK(bp)), PACK(size, 0, pal));
        PUT(FTRP(NEXT_BLOCK(bp)), PACK(size, 0, pal));
        return (((char *)(bp)) - GET_SIZE(((char *)(bp)) - DWORD));
    }
}
/*
 * 寻找合适的空闲块，成功返回块指针，失败返回NULL
 */
static void *find_fit(size_t size)
{
    size_t block_size;
    unsigned int alloc;
    char *start = fit_p;
    block_size = GET_SIZE(HEAD(start));
    alloc = GET_ALLOC(HEAD(start));
    while (1)
    {
        if (alloc == 1 || block_size < size)
        {
            start = start + block_size;
            block_size = GET_SIZE(HEAD(start));
            alloc = GET_ALLOC(HEAD(start));
            if (block_size == 0)
            {
                start = heap_list + DWORD;
                if (start == fit_p)
                    return NULL;
                block_size = GET_SIZE(HEAD(start));
                alloc = GET_ALLOC(HEAD(start));
                continue;
            }
            if (start == fit_p)
                return NULL;
        }
        else
        {
            fit_p = NEXT_BLOCK(start);
            if (GET_SIZE((char *)(fit_p)-4) == 0)
                fit_p = heap_list + DWORD;
            return start;
        }
    }
}
/*
 * 分割块
 */
static void place(void *bp, size_t size)
{
    size_t block_size, free_bsize;
    if (bp == NULL)
        return;
    unsigned int prealloc = GET_PREALLOC((char *)(bp)-4);
    block_size = GET_SIZE(HEAD(bp));
    if (block_size - size < 8) // 不分割
    {
        PUT(HEAD(bp), PACK(block_size, 1, prealloc));
        size_t next_size = GET_SIZE((char *)NEXT_BLOCK(bp) - 4);
        unsigned int alloc = GET_ALLOC((char *)NEXT_BLOCK(bp) - 4);
        PUT((char *)(NEXT_BLOCK(bp)) - 4, PACK(next_size, alloc, 1));
        if (alloc == 0)
            PUT((char *)NEXT_BLOCK(bp) + next_size - DWORD, PACK(next_size, alloc, 1));
        return;
    }
    // 分割
    free_bsize = block_size - size;
    // 已分配块
    PUT(HEAD(bp), PACK(size, 1, prealloc));

    // 剩下的空闲块
    PUT((char *)(bp) + size - SWORD, PACK(free_bsize, 0, 1));
    PUT((char *)(bp) + block_size - DWORD, PACK(free_bsize, 0, 1));
}

static void printf_list(char *start_block)
{
    unsigned int alloc, pre_alloc;
    size_t size = GET_SIZE(HEAD(start_block));
    while (size != 0)
    {
        alloc = GET_ALLOC(HEAD(start_block));
        pre_alloc = GET_PREALLOC(HEAD(start_block));
        printf("size=%u  alloc= %u  pre_alloc=%u\n", size, alloc, pre_alloc);
        start_block = NEXT_BLOCK(start_block);
        size = GET_SIZE(HEAD(start_block));
    }
    alloc = GET_ALLOC((char *)(start_block)-4);
    pre_alloc = GET_PREALLOC((char *)(start_block)-4);
    printf("size=%u  alloc= %u  pre_alloc=%u\n", size, alloc, pre_alloc);
    printf("-------------------------------\n");
}