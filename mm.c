/*
 * 基于隐式简单空闲链表实现
 * 块大小8字节对齐，有效载荷8字节对齐
 * 块有一个一个字的头部，头部记录块大小，最低位记录分配情况，块有一个脚部（头部的副本）
 * 采取立即合并
 * 使用分割
 * 最小块大小是16字节
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 向上舍入到最接近的对齐倍数*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SWORD 4                                                               // 单字
#define DWORD 8                                                               // 双字
#define CHUNKSIZE (1 << 12)                                                   // 默认扩展堆大小
#define PACK(size, alloc) ((size) | (alloc))                                  // 赋值给头部和脚部
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))                          // 把val存在p指向的一个字中
#define GET(p) (*((unsigned int *)(p)))                                       // 取p指向的一个字中的值
#define GET_SIZE(p) ((GET(p)) & (~0x7))                                       // 取块大小
#define GET_ALLOC(p) ((GET(p)) & (0x1))                                       // 取分配位
#define HEAD(bp) (((char *)(bp)) - (SWORD))                                   // 得到块的头部
#define FTRP(bp) (((char *)(bp)) + (GET_SIZE(HEAD(bp))) - (DWORD))            // 得到脚部
#define NEXT_BLOCK(bp) (((char *)(bp)) + (GET_SIZE(HEAD(bp))))                // 下一个块指针
#define PRE_BLOCK(bp) (((char *)(bp)) - (GET_SIZE(((char *)(bp)) - (DWORD)))) // 上一个块指针
#define MAX(x, y) ((x) > (y) ? (x) : (y))                                     // 返回较大值
#define MIN(x, y) ((x) < (y) ? (x) : (y))                                     // 返回较小值

char *heap_list; // 指向序言块
/*
 * mm_init - initialize the malloc package.
 * 正常返回0，有问题返回-1
 */
int mm_init(void)
{
    if ((heap_list = mem_sbrk(4 * SWORD)) == ((void *)-1))
        return -1;
    PUT(heap_list, 0);
    PUT(heap_list + SWORD * 1, PACK(DWORD, 1));
    PUT(heap_list + SWORD * 2, PACK(DWORD, 1));
    PUT(heap_list + SWORD * 3, PACK(0, 1));
    heap_list += DWORD;
    if (extend_heap(CHUNKSIZE / SWORD) == NULL)
        return -1;

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
    if (size <= DWORD)
        block_size = 16;
    else
        block_size = ((size + DWORD + (DWORD - 1)) / DWORD) * DWORD;
    bp = find_fit(block_size);
    if (bp)
        place(bp, block_size);
    else
    {
        extend_size = MAX(block_size, CHUNKSIZE);
        bp = extend_heap(extend_size / SWORD);
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
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HEAD(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr;
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }
    size_t old_size = GET_SIZE((char *)(ptr)-4);
    new_ptr = mm_malloc(size);
    size_t new_size = GET_SIZE((char *)(new_ptr)-4);
    int length = (MIN(old_size, new_size) - 8) / 8;
    long long *ulptr = (long long *)ptr;
    long long*ulnew_ptr = (long long *)new_ptr;
    for (int i = 0; i < length; i++)
    {
        *ulnew_ptr = *ulptr;
        ulnew_ptr++;
        ulptr++;
    }
    mm_free(ptr);
    return new_ptr;
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
        return NULL;
    PUT((char *)(bp)-4, PACK(size, 0));
    PUT((char *)(bp) + size - DWORD, PACK(size, 0));
    PUT((char *)(bp) + size - SWORD, PACK(0, 1));
    return coalesce(bp);
}
/*
 *合并空闲块,返回指向该空闲块的指针
 */
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HEAD(bp));
    unsigned int next_alloc = GET_ALLOC(HEAD(NEXT_BLOCK(bp)));
    unsigned int prev_alloc = GET_ALLOC(HEAD(PRE_BLOCK(bp)));
    size_t next_size = GET_SIZE(HEAD(NEXT_BLOCK(bp)));
    size_t prev_size = GET_SIZE(HEAD(PRE_BLOCK(bp)));
    if (next_alloc && prev_alloc)
        return bp;
    else if (next_alloc && !prev_alloc)
    {
        size = size + prev_size;
        PUT(HEAD(PRE_BLOCK(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return PRE_BLOCK(bp);
    }
    else if (prev_alloc && !next_alloc)
    {
        size += next_size;
        PUT(HEAD(bp), PACK(size, 0));
        PUT(((char *)(bp)) + size - DWORD, PACK(size, 0));
        return bp;
    }
    else
    {
        size = size + prev_size + next_size;
        PUT(HEAD(PRE_BLOCK(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLOCK(bp)), PACK(size, 0));
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
    char *start = heap_list + DWORD;
    block_size = GET_SIZE(HEAD(start));
    alloc = GET_ALLOC(HEAD(start));
    while (block_size != 0)
        if (alloc == 1 || block_size < size)
        {
            start = start + block_size;
            block_size = GET_SIZE(HEAD(start));
            alloc = GET_ALLOC(HEAD(start));
        }
        else
            return start;
    return NULL;
}
/*
 * 分割块
 */
static void place(void *bp, size_t size)
{
    size_t block_size, free_bsize;
    if (bp == NULL)
        return;
    block_size = GET_SIZE(HEAD(bp));
    if (block_size - size < 16) // 不分割
    {
        PUT(HEAD(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
        return;
    }
    // 分割
    free_bsize = block_size - size;
    // 已分配块
    PUT(HEAD(bp), PACK(size, 1));
    PUT((char *)(bp) + size - DWORD, PACK(size, 1));
    // 剩下的空闲块
    PUT((char *)(bp) + size - SWORD, PACK(free_bsize, 0));
    PUT((char *)(bp) + block_size - DWORD, PACK(free_bsize, 0));
}