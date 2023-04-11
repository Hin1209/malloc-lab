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
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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

#define NEXT_FREE(bp) (*(unsigned int *)(bp))
#define PREV_FREE(bp) (*(unsigned int *)((char *)(bp) + WSIZE))

#define PUT_NEXT_ADDRESS(bp, address) (*(unsigned int *)(bp) = (address))
#define PUT_PREV_ADDRESS(bp, address) (*(unsigned int *)(((char *)(bp) + WSIZE)) = (address))

#define NUM_CLASS 10

/*
 * mm_init - initialize the malloc package.
 */
static void *coalesce(void *bp);

void *heap_listp;

int can_merge(size_t size)
{
    while (size > 1)
    {
        if (size & 0x1)
            return 0;
        size >>= 1;
    }
    return 1;
}

int get_class(size_t size)
{
    int class_num = 0;
    size_t tmp_size = size >> 3;
    while (tmp_size > 1)
    {
        tmp_size >>= 1;
        class_num++;
    }
    return class_num;
}

static void *find_fit(size_t asize)
{
    int class_num = get_class(asize);
    if (class_num > NUM_CLASS)
        class_num = NUM_CLASS;

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

void splice_free(void *bp)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    int class_num = get_class(block_size);

    if (class_num > NUM_CLASS)
        class_num = NUM_CLASS;

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

void add_free(void *bp)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    int class_num = get_class(block_size);

    if (class_num > NUM_CLASS)
        class_num = NUM_CLASS;

    void *root = GET(heap_listp + (class_num - 1) * WSIZE);
    if (root != mem_heap_lo())
    {
        PUT_PREV_ADDRESS(root, bp);
    }
    PUT_NEXT_ADDRESS(bp, root);
    PUT(heap_listp + (class_num - 1) * WSIZE, bp);
}

void place(void *bp, size_t asize)
{
    size_t block_size = GET_SIZE(HDRP(bp));
    size_t spare_size = block_size - asize;
    void *candidate = NEXT_BLKP(bp);
    if (asize < spare_size)
    {
        splice_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        size_t tmp_size = block_size / 2;
        void *next_bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(candidate)) && can_merge(spare_size + GET_SIZE(HDRP(candidate))))
        {
            splice_free(candidate);
            size_t new_size = spare_size + GET_SIZE(HDRP(candidate));
            PUT(HDRP(next_bp), PACK(new_size, 0));
            PUT(FTRP(next_bp), PACK(new_size, 0));
            add_free(next_bp);
        }
        else
        {
            while (spare_size >= 16)
            {
                PUT(HDRP(next_bp), PACK(tmp_size, 0));
                PUT(FTRP(next_bp), PACK(tmp_size, 0));
                add_free(next_bp);
                next_bp = NEXT_BLKP(next_bp);
                spare_size -= tmp_size;
                if (!GET_ALLOC(HDRP(candidate)) && can_merge(spare_size + GET_SIZE(HDRP(candidate))))
                {
                    splice_free(candidate);
                    size_t new_size = spare_size + GET_SIZE(HDRP(candidate));
                    PUT(HDRP(next_bp), PACK(new_size, 0));
                    PUT(FTRP(next_bp), PACK(new_size, 0));
                    add_free(next_bp);
                    break;
                }
                tmp_size >>= 1;
            }
        }
    }
    else
    {
        splice_free(bp);
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t tmp_size;
    int can_split = 1;

    if (prev_alloc && next_alloc)
    {
        add_free(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if (can_merge(size))
        {
            splice_free(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
        }
        add_free(bp);
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if (can_merge(size))
        {
            splice_free(PREV_BLKP(bp));
            PUT(FTRP(bp), PACK(size, 0));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
            add_free(PREV_BLKP(bp));
            bp = PREV_BLKP(bp);
        }
        else
        {
            add_free(bp);
        }
    }

    else
    {
        int left_merge = can_merge(size + GET_SIZE(PREV_BLKP(bp)));
        int right_merge = can_merge(size + GET_SIZE(NEXT_BLKP(bp)));
        int full_merge = can_merge(size + GET_SIZE(PREV_BLKP(bp)) + GET_SIZE(NEXT_BLKP(bp)));
        if (full_merge)
        {
            size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

            splice_free(PREV_BLKP(bp));
            splice_free(NEXT_BLKP(bp));

            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
            add_free(PREV_BLKP(bp));
            bp = PREV_BLKP(bp);
        }
        else if (left_merge && right_merge)
        {
            if (GET_SIZE(PREV_BLKP(bp)) >= GET_SIZE(NEXT_BLKP(bp)))
            {
                size += GET_SIZE(HDRP(PREV_BLKP(bp)));
                splice_free(PREV_BLKP(bp));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0));
                add_free(PREV_BLKP(bp));
                bp = PREV_BLKP(bp);
            }
            else
            {
                size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
                splice_free(NEXT_BLKP(bp));
                PUT(HDRP(bp), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0));
                add_free(bp);
            }
        }
        else if (left_merge && !right_merge)
        {
            size += GET_SIZE(HDRP(PREV_BLKP(bp)));
            splice_free(PREV_BLKP(bp));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            add_free(PREV_BLKP(bp));
            bp = PREV_BLKP(bp);
        }
        else if (right_merge && !left_merge)
        {
            size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
            splice_free(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            add_free(bp);
        }
        else if (!left_merge && !right_merge && !full_merge)
        {
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            add_free(bp);
        }
    }
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    void *last_foo = mem_heap_hi() - 7;
    void *last_bp = last_foo - GET_SIZE(last_foo) + 8;
    if (!GET_ALLOC(last_foo))
    {
        size = (words * WSIZE) - GET_SIZE(last_foo);
    }
    else
        size = words * WSIZE;
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

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0)
        return NULL;

    asize = 2 * DSIZE;
    while (asize < size + DSIZE)
        asize <<= 1;

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

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
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
