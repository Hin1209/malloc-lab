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

/*
 * mm_init - initialize the malloc package.
 */

void *heap_listp;
unsigned int *root;

static void *find_fit(size_t asize)
{
    printf("find\n");
    void *bp = root;

    while (bp != mem_heap_lo() && GET_SIZE(HDRP(bp)) < asize)
    {
        bp = NEXT_FREE(bp);
    }

    if (bp == mem_heap_lo())
        return NULL;
    return bp;
}

void place(void *bp, size_t asize)
{
    printf("place\n");
    size_t block_size = GET_SIZE(HDRP(bp));
    if ((block_size - asize) >= 2 * DSIZE)
    {
        printf("here1\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
        printf("hh\n");
        if (bp != root)
        {
            if (NEXT_FREE(bp) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(bp), PREV_FREE(bp));
            PUT_NEXT_ADDRESS(PREV_FREE(bp), NEXT_FREE(bp));
        }
        else
        {
            root = NEXT_FREE(bp);
        }
        if (root != mem_heap_lo())
            PUT_PREV_ADDRESS(root, NEXT_BLKP(bp));
        printf("??\n");
        PUT_NEXT_ADDRESS(NEXT_BLKP(bp), root);
        root = NEXT_BLKP(bp);
        printf("???\n");
    }
    else
    {
        printf("here2\n");
        if (bp != root)
        {
            PUT_NEXT_ADDRESS(PREV_FREE(bp), NEXT_FREE(bp));
            if (NEXT_FREE(bp) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(bp), PREV_FREE(bp));
        }
        else
        {
            root = NEXT_FREE(bp);
        }
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}

static void *coalesce(void *bp)
{
    printf("col\n");
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        PUT_NEXT_ADDRESS(bp, root);
        if (root != mem_heap_lo())
            PUT_PREV_ADDRESS(root, bp);
        root = bp;
    }

    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if (root != NEXT_BLKP(bp))
        {
            if (PREV_FREE(NEXT_BLKP(bp)) != root)
                PUT_NEXT_ADDRESS(PREV_FREE(NEXT_BLKP(bp)), NEXT_FREE(NEXT_BLKP(bp)));
            if (NEXT_FREE(NEXT_BLKP(bp)) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(NEXT_BLKP(bp)), PREV_FREE(NEXT_BLKP(bp)));
            PUT_NEXT_ADDRESS(bp, root);
            PUT_PREV_ADDRESS(root, bp);
            root = bp;
        }
        else
        {
            root = bp;
            PUT_NEXT_ADDRESS(bp, NEXT_FREE(NEXT_BLKP(bp)));
            if (NEXT_FREE(NEXT_BLKP(bp)) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(NEXT_BLKP(bp)), bp);
        }
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if (root != PREV_BLKP(bp))
        {
            if (PREV_FREE(PREV_BLKP(bp)) != root)
                PUT_NEXT_ADDRESS(PREV_FREE(PREV_BLKP(bp)), NEXT_FREE(PREV_BLKP(bp)));
            if (NEXT_FREE(PREV_BLKP(bp)) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(PREV_BLKP(bp)), PREV_FREE(PREV_BLKP(bp)));
            PUT_NEXT_ADDRESS(PREV_BLKP(bp), root);
            PUT_PREV_ADDRESS(root, PREV_BLKP(bp));
        }

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        root = bp;
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        if (root != PREV_BLKP(bp))
        {
            if (PREV_FREE(PREV_BLKP(bp)) != root)
                PUT_NEXT_ADDRESS(PREV_FREE(PREV_BLKP(bp)), NEXT_FREE(PREV_BLKP(bp)));
            if (NEXT_FREE(PREV_BLKP(bp)) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(PREV_BLKP(bp)), PREV_FREE(PREV_BLKP(bp)));
            PUT_NEXT_ADDRESS(PREV_BLKP(bp), root);
            PUT_PREV_ADDRESS(root, PREV_BLKP(bp));
        }
        else
        {
            root = NEXT_FREE(PREV_BLKP(bp));
        }
        if (root != NEXT_BLKP(bp))
        {
            PUT_NEXT_ADDRESS(PREV_FREE(NEXT_BLKP(bp)), NEXT_FREE(NEXT_BLKP(bp)));
            if (NEXT_FREE(NEXT_BLKP(bp)) != mem_heap_lo())
                PUT_PREV_ADDRESS(NEXT_FREE(NEXT_BLKP(bp)), PREV_FREE(NEXT_BLKP(bp)));
        }
        else
        {
            root = NEXT_FREE(NEXT_BLKP(bp));
        }

        PUT_NEXT_ADDRESS(PREV_BLKP(bp), root);
        if (root != mem_heap_lo())
            PUT_PREV_ADDRESS(root, PREV_BLKP(bp));
        root = PREV_BLKP(bp);

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words)
{
    printf("extend\n");
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
    printf("init\n");
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);
    root = mem_heap_lo();

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
    printf("mal\n");
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
        printf("^^\n");
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    printf("$$\n");
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    printf('free\n');
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
    printf("real\n");
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
