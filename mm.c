/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Only a header is stored with the size to allow
 * for realloc() to retrieve the block size.  Blocks are never coalesced 
 * or reused in this naive implementation. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include <time.h>

#include "mm.h"
#include "memlib.h"
#include "config.h"             /* defines ALIGNMENT */
#include "list.h"

struct free_blocks {
	int size;
	struct list free_blocks_list;
	struct list_elem elem;
};

struct boundary_tag {
    int inuse:1;        // inuse bit
    int size:31;        // size of block, in words
};

/* FENCE is used for heap prologue/epilogue. */
const struct boundary_tag FENCE = { .inuse = 1, .size = 0 };

/* A C struct describing the beginning of each block. 
 * For implicit lists, used and free blocks have the same 
 * structure, so one struct will suffice for this example.
 * If each block is aligned at 4 mod 8, each payload will
 * be aligned at 0 mod 8.
 */
struct block {
    struct boundary_tag header; /* offset 0, at address 4 mod 8 */
    char payload[0];            /* offset 4, at address 0 mod 8 */
    struct list_elem elem;
};

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITx
#define SEG_LISTS

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define MIN_BLOCK_SIZE_WORDS 8 /* Minimum block size in words */
#define CHUNKSIZE  (1<<10)  /* Extend heap by this amount (bytes) 2^12 */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

#define MAX_BLOCK	4096
#define MIN_BLOCK	8
#define STEP_AMOUNT	2

/* Global variables */
static struct block *heap_listp = 0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static struct block *rover;           /* Next fit rover */
#endif

/*Global variables */
static struct list free_list; /* List of free blocks */
int count = 0;

/* Function prototypes for internal helper routines */
static struct block *extend_heap(size_t words);
static void place(struct block *bp, size_t asize);
static struct block *find_fit(size_t asize);
static struct block *coalesce(struct block *bp);
static void add_freeblock(struct block *blk);
static void print_free_block_list();
#ifdef SEG_LISTS
static void init_free_lists();
#endif
static void mark_block_used();

/* Given a block, obtain previous's block footer.
   Works for left-most block also. */
static struct boundary_tag * prev_blk_footer(struct block *blk) {
    return &blk->header - 1;
}

/* Return if block is free */
static bool blk_free(struct block *blk) { 
    return !blk->header.inuse; 
}

/* Return size of block is free */
static size_t blk_size(struct block *blk) { 
    return blk->header.size; 
}

/* Given a block, obtain pointer to previous block.
   Not meaningful for left-most block. */
static struct block *prev_blk(struct block *blk) {
    struct boundary_tag *prevfooter = prev_blk_footer(blk);
    assert(prevfooter->size != 0);
    return (struct block *)((size_t *)blk - prevfooter->size);
}

/* Given a block, obtain pointer to next block.
   Not meaningful for right-most block. */
static struct block *next_blk(struct block *blk) {
    assert(blk_size(blk) != 0);
    return (struct block *)((size_t *)blk + blk->header.size);
}

/* Given a block, obtain its footer boundary tag */
static struct boundary_tag * get_footer(struct block *blk) {
    return (void *)((size_t *)blk + blk->header.size) 
                   - sizeof(struct boundary_tag);
}

/* Set a block's size and inuse bit in header and footer */
static void set_header_and_footer(struct block *blk, int size, int inuse) {
    blk->header.inuse = inuse;
    blk->header.size = size;
    * get_footer(blk) = blk->header;    /* Copy header to footer */
}

/* Mark a block as used and  its size. */
static void mark_block_used(struct block *blk, int size) {
    set_header_and_footer(blk, size, 1);
}


/* Mark a block as free and set its size. */
static void mark_block_free(struct block *blk, int size) {
    set_header_and_footer(blk, size, 0);
}

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	// printf("\nstarting init");
	//printf("BEGIN INIT:\n");
	
	if(count < 0)
		print_free_block_list();
	
	/* Initialize the free list */
#ifdef SEG_LISTS
	init_free_lists();
#else
	list_init(&free_list);
#endif
	
    /* Create the initial empty heap */
    struct boundary_tag * initial = mem_sbrk(2 * sizeof(struct boundary_tag));
    if (initial == (void *)-1)
        return -1;

    /* We use a slightly different strategy than suggested in the book.
     * Rather than placing a min-sized prologue block at the beginning
     * of the heap, we simply place two fences.
     * The consequence is that coalesce() must call prev_blk_footer()
     * and not prev_blk() - prev_blk() cannot be called on the left-most
     * block.
     */
    initial[0] = FENCE;                     /* Prologue footer */
    heap_listp = (struct block *)&initial[1];
    initial[1] = FENCE;                     /* Epilogue header */

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
		
	// printf("\ninitialization successful");
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size)
{
    
    // printf("\nstarting malloc");
    //count++;
    //printf("BEGIN MALLOC: %d\n", count);
    //printFreeBlockList();
    
    size_t awords;      /* Adjusted block size in words */
    size_t extendwords;  /* Amount to extend heap if no fit */
    struct block *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += 2 * sizeof(struct boundary_tag);    /* account for tags */
    size = (size + DSIZE - 1) & ~(DSIZE - 1);   /* align to double word */
    awords = MAX(MIN_BLOCK_SIZE_WORDS, size/WSIZE);
                                                /* respect minimum size */

    /* Search the free list for a fit */
    if ((bp = find_fit(awords)) != NULL) {
        place(bp, awords);
	// mark_block_used(bp, blk_size(bp));
	// list_remove(&bp->elem);
	// printf("\nmalloc successful");
        return bp->payload;
    }

    /* No fit found. Get more memory and place the block */
    //	printf("\nno fit found for %i, extending", awords);
    extendwords = MAX(awords,CHUNKSIZE);
    if ((bp = extend_heap(extendwords)) == NULL)  
        return NULL;
    place(bp, awords);
    // mark_block_used(bp, blk_size(bp));
    // list_remove(&bp->elem);
    // printf("\nextend malloc successful");
    return bp->payload;
} 

/* 
 * mm_free - Free a block 
 */
void mm_free(void *bp)
{
	// printf("\nstarting free");
    if (bp == 0) 
        return;

    /* Find block from user pointer */
    struct block *blk = bp - offsetof(struct block, payload);
//    if (heap_listp == 0) {
//        mm_init();
//    }

    mark_block_free(blk, blk_size(blk));
    coalesce(blk);
	// printf("\nfree successful");
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static struct block *coalesce(struct block *bp) 
{
	// printf("\nstarting coalesce\n");
    bool prev_alloc = prev_blk_footer(bp)->inuse;
    bool next_alloc = !blk_free(next_blk(bp));
    size_t size = blk_size(bp);
	
//	print_free_block_list();

    if (prev_alloc && next_alloc) {            /* Case 1 */
		// printf("case 1");
		add_freeblock(bp);
		return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
		// printf("case 2");
		struct block *temp;
		temp = next_blk(bp);
		list_remove(&temp->elem);
        mark_block_free(bp, size + blk_size(next_blk(bp)));
		add_freeblock(bp);
		return bp;
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
		// printf("case 3\n");
		struct block *temp;
		temp = prev_blk(bp);
		// printf("removing block of size %i\n", blk_size(temp));
		list_remove(&temp->elem);
        mark_block_free(temp, size + blk_size(temp));
		add_freeblock(temp);
		return temp;
    }

    else {                                     /* Case 4 */
		// printf("case 4");
		struct block *temp;
		struct block *temp2;
		
		temp = prev_blk(bp);
		list_remove(&temp->elem);
		
		temp2 = next_blk(bp);
		list_remove(&temp2->elem);
		
        mark_block_free(temp, size + blk_size(temp) + blk_size(temp2));
		add_freeblock(temp);
		return temp;
    }
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > bp) && (rover < next_blk(bp))) 
        rover = bp;
#endif

	// printf("\ncoalesce successful");
    return bp;
}

static void add_freeblock(struct block *blk)
{
	// printf("\nadd freeblock started");
#ifdef SEG_LISTS

    if (blk == 0)
	return;
    
    struct list_elem *e;
    
    for (e = list_begin (&free_list); e != list_end (&free_list); e = list_next (e)) {
	struct free_blocks *seg_blocks = list_entry (e, struct free_blocks, elem);
	if (seg_blocks->size <= blk_size(blk)) {
	    list_push_back(&seg_blocks->free_blocks_list, &blk->elem);
	    return;
	}
    }
    
#else
	list_push_back(&free_list, &blk->elem);
#endif
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    struct block *oldblock = ptr - offsetof(struct block, payload);
    oldsize = blk_size(oldblock) * WSIZE;
    struct block *next_block = next_blk(oldblock);
    size_t next_size = blk_size(next_block);
    
    /*
     * If new size is larger than block and next block is free, then
     * extend current block.
     */
    if (blk_free(next_block) && (oldsize > size)) {

	/*
	 * ALIGN PAYLOAD TO 8 BYTES
	 */
	
	// mark next block as used
	mark_block_used(next_block, blk_size(next_block));
	// removed block from freelist
	list_remove(&next_block->elem);
	// update current block size
	oldblock->header.size = oldsize + next_size;
    	return oldblock;
    }

    /*
     * Otherwise, if new size is smaller than block size, then shrink
     * current block.
     */
    //else if (blk_free(next_block) && size < oldsize) {
	/// IMPLEMENT
    //}

    /* Otherwise, malloc, copy and free. */
    else {

	newptr = mm_malloc(size);
	
	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
	    return 0;
	}
	
	/* Copy the old data. */
	if (size < oldsize) oldsize = size;
	memcpy(newptr, ptr, oldsize);
	
	/* Free the old block. */
	mm_free(ptr);
	
	return newptr;
    }
}

/* 
 * checkheap - We don't check anything right now. 
 */
void mm_checkheap(int verbose)  
{ 
}

/* 
 * The remaining routines are internal helper routines 
 */
 #ifdef SEG_LISTS
 static void init_free_lists()
{
	list_init(&free_list);

	int i;
	for(i = MAX_BLOCK; i >= MIN_BLOCK; i /= STEP_AMOUNT) 
	{
		struct free_blocks *setupblocks = mem_sbrk(sizeof(struct free_blocks));
		setupblocks->size = i;
		list_init(&setupblocks->free_blocks_list);
		list_push_back(&free_list, &setupblocks->elem);
	}
}
#endif

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static struct block *extend_heap(size_t words) 
{
	// printf("\nstarting extendheap");
    void *bp;

    /* Allocate an even number of words to maintain alignment */
    words = (words + 1) & ~1;
    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1)  
        return NULL;

    /* Initialize free block header/footer and the epilogue header.
     * Note that we scoop up the previous epilogue here. */
    struct block * blk = bp - sizeof(FENCE);
    mark_block_free(blk, words);
    next_blk(blk)->header = FENCE;

	// printf("\nextend heap by block of size: %i", blk_size(blk));
    /* Coalesce if the previous block was free */
	// printf("\nextendheap successful, calling coalesce");
    return coalesce(blk);
}

/* 
 * place - Place block of asize words at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(struct block *bp, size_t asize)
{
    size_t csize = blk_size(bp);

    if ((csize - asize) >= MIN_BLOCK_SIZE_WORDS) {
        mark_block_used(bp, asize);
	list_remove(&bp->elem);
	struct block *temp = next_blk(bp);
        mark_block_free(temp, csize-asize);
	add_freeblock(temp);
    }
    else { 
        mark_block_used(bp, csize);
	list_remove(&bp->elem);
    }
}

/* 
 * find_fit - Find a fit for a block with asize words 
 */
static struct block *find_fit(size_t asize)
{
	// printf("\nsearching for block");
#ifdef NEXT_FIT 
    /* Next fit search */	
    struct list_elem *e;
    
    for (e = list_begin (&free_list); e != list_end (&free_list); e = list_next (e)) {
        struct block *rover = list_entry (e, struct block, elem);
	if (blk_free(rover) && (asize <= blk_size(rover)))
	    return rover;	
    }

    return NULL;  /* no fit found */
#endif
#ifdef SEG_LISTS
    
//    printf("\nstart search");
	struct list_elem *e3;
	for (e3 = list_rbegin (&free_list); e3 != list_rend (&free_list);
           e3 = list_prev (e3))
    {
        struct free_blocks *seg_blocks = list_entry (e3, struct free_blocks, elem);
		if (!list_empty(&seg_blocks->free_blocks_list) && (seg_blocks->size >= asize || list_prev(e3) == list_rend(&free_list))) {
			struct list_elem *e4;
            struct list_elem *e5 = list_rbegin(&seg_blocks->free_blocks_list);
			for (e4 = list_begin (&seg_blocks->free_blocks_list); e4 != list_end (&seg_blocks->free_blocks_list);
				   e4 = list_next (e4))
			{
                
                
				struct block *foundblock = list_entry (e4, struct block, elem);
                struct block *foundblock2 = list_entry (e5, struct block, elem);
//                printf("\nSize of Block: %i, Searching Size: %i", blk_size(foundblock), asize);
				if (blk_size(foundblock) >= asize)
				{
					// place(foundblock, blk_size(foundblock));
					// mark_block_used(foundblock, blk_size(foundblock));
					// printf("\nblock found");				    
				    return foundblock;
				}
                if (blk_size(foundblock2) >= asize)
				{
				    // place(foundblock, blk_size(foundblock));
				    // mark_block_used(foundblock, blk_size(foundblock));
				    // printf("\nblock found");
				    return foundblock2;
				}
                
                e5 = list_prev(e5);
                if (e4 == e5 || list_next(e5) == e4) {
                    return NULL;
                }
			}
		}
    }
//	printf("\nno block found");
	return NULL;
	
#else 
	// printf("TESTTT");
    /* First fit search */
	struct list_elem *e2;
	
	for (e2 = list_begin (&free_list); e2 != list_end (&free_list);
           e2 = list_next (e2))
    {
        struct block *rover = list_entry (e2, struct block, elem);
		if (blk_free(rover) && (asize <= blk_size(rover)))
			return rover;
		
    }
	
    return NULL; /* No fit */
#endif
}

static void print_free_block_list()
{
	printf("\n---------------------------\n");
#ifdef SEG_LISTS
	struct list_elem *e;
	
	for (e = list_begin (&free_list); e != list_end (&free_list);
           e = list_next (e))
    {
		struct free_blocks *seg_blocks = list_entry (e, struct free_blocks, elem);
		printf("Free of Size: %d\n", seg_blocks->size);
		if (!list_empty(&seg_blocks->free_blocks_list)) 
		{
			struct list_elem *e2;
	
			for (e2 = list_begin (&seg_blocks->free_blocks_list); e2 != list_end (&seg_blocks->free_blocks_list); e2 = list_next (e2))
			{
				struct block *foundblock = list_entry (e2, struct block, elem);
				printf("Free: %d\n", blk_size(foundblock));
			}
		} else {
			printf("None\n");
		}
	}
#else
	struct list_elem *e;
	
	for (e = list_begin (&free_list); e != list_end (&free_list);
           e = list_next (e))
    {
        struct block *rover = list_entry (e, struct block, elem);
		printf("Free: %d\n", blk_size(rover));
    }
#endif	
	printf("---------------------------\n");
}

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "kar-nayefc",
    /* First member's full name */
    "Nayef Copty",
    /* First member's SLO (@cs.vt.edu) email address */
    "nayefc",
    /* Second member's full name (leave blank if none) */
    "K Alnajar",
    /* Second member's SLO (@cs.vt.edu) email address (leave blank if none) */
    "kar"
};
