/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

/* rounds up to the nearest multiple of ALIGNMENT */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define NEXT_FREE(bp) (*(unsigned int *)(bp))                   // 다음 free block의 block pointer를 return
#define PREV_FREE(bp) (*(unsigned int *)((char *)(bp) + WSIZE)) // 이전 free block의 block pointer를 return

#define PUT_NEXT_ADDRESS(bp, address) (*(unsigned int *)(bp) = (address))                     // bp의 next free block으로 address를 설정
#define PUT_PREV_ADDRESS(bp, address) (*(unsigned int *)(((char *)(bp) + WSIZE)) = (address)) // bp의 previous free block으로 address를 설정

#define NUM_CLASS 10

int get_class(size_t size);
void splice_free(void *bp);
void add_free(void *bp);
void place(void *bp, size_t asize);
static void *coalesce(void *bp);

/*
 * mm_init - initialize the malloc package.
 */

void *heap_listp;

// size에 대한 class 구하는 함수
int get_class(size_t size)
{
    int class_num = 1;
    size_t tmp_size = size >> 4;

    while (tmp_size > 1)
    {
        tmp_size >>= 1;
        class_num++;
    }
    if (class_num > NUM_CLASS)
        class_num = NUM_CLASS;
    return class_num;
}

// asize를 할당할 수 있는 free block을 찾는 함수
static void *find_fit(size_t asize)
{
    int class_num = get_class(asize);
    void *bp;

    while (class_num <= NUM_CLASS)
    {
        bp = GET(heap_listp + (class_num++ - 1) * WSIZE);
        if (bp != mem_heap_lo())
        {
            void *tmp = bp;
            while (tmp != mem_heap_lo() && GET_SIZE(HDRP(tmp)) < asize)
                tmp = NEXT_FREE(tmp);
            if (tmp != mem_heap_lo())
                return tmp;
        }
    }
    return NULL;
}

// bp를 free list에서 빼는 함수 - prev block과 next block의 연결 조정
void splice_free(void *bp)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    int class_num = get_class(block_size);
    void *root = GET(heap_listp + (class_num - 1) * WSIZE);
    if (bp == root)
    {
        PUT(heap_listp + (class_num - 1) * WSIZE, NEXT_FREE(bp));
    }
    else
    {
        PUT_NEXT_ADDRESS(PREV_FREE(bp), NEXT_FREE(bp));
        if (NEXT_FREE(bp) != mem_heap_lo())
            PUT_PREV_ADDRESS(NEXT_FREE(bp), PREV_FREE(bp));
    }
}

// bp를 free list의 맨 앞에 넣는 함수
void add_free(void *bp)
{
    size_t block_size = GET_SIZE(HDRP(bp)) >> 3;
    int class_num = get_class(block_size);
    void *root = GET(heap_listp + (class_num - 1) * WSIZE);
    if (root != mem_heap_lo())
    {
        PUT_PREV_ADDRESS(root, bp);
    }
    PUT_NEXT_ADDRESS(bp, root);
    PUT(heap_listp + (class_num - 1) * WSIZE, bp);
}

// bp에 asize 만큼의 공간을 할당하는 함수
void place(void *bp, size_t asize)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    if ((block_size - asize) >= 2 * DSIZE)
    {
        splice_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        add_free(NEXT_BLKP(bp));
    }
    else
    {
        splice_free(bp);
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}

// 앞 뒤 block의 할당 여부를 검사하고 free block들을 합쳐주는 함수
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        splice_free(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        splice_free(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        splice_free(PREV_BLKP(bp));
        splice_free(NEXT_BLKP(bp));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

int mm_init(void)
{
    if ((heap_listp = mem_sbrk((4 + NUM_CLASS) * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    size_t prolog_size = DSIZE + NUM_CLASS * WSIZE;
    PUT(heap_listp + (1 * WSIZE), PACK(prolog_size, 1));
    for (int i = 1; i <= NUM_CLASS; i++)
        PUT(heap_listp + ((1 + i) * WSIZE), mem_heap_lo());
    PUT(heap_listp + ((2 + NUM_CLASS) * WSIZE), PACK(prolog_size, 1));
    PUT(heap_listp + ((3 + NUM_CLASS) * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - 2 * WSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
