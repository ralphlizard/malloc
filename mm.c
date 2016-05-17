/*
 * mm.c
 *
 * Ralph Kim - junghyu1
 *
 * All block have both header and footer which indicates the total
 * size of the block and whether the block is allocated.
 *
 * All blocks are aligned to multiples of 8 bytes.
 *
 * Blocks have a minimum size of 16 bytes to accommodate a 
 * header (4 bytes), footer (4 bytes), and pointer to successive
 * free block (8 bytes).
 *
 * All free blocks are singly-linked to the successive block in the 
 * explicit free list.
 *
 * There is a list of segregated free list. Letting i be index, the 
 * free list at i contains all free blocks of total size in the range
 * 2^(i-1) + 1 to 2^i, except the last free list, which contains
 * every free block that the other free lists do not contain.
 *
 * Free blocks are entered into the corresponding free list in last-in
 * first-out order.
 *
 * The free block in which malloc allocates a block is found through
 * the first-fit search.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define NUMLIST     25      /* Number of segregated lists */
#define MINSIZE     16      /* Minimum size of a block (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(unsigned int *)(p))
#define PUT(p, val)    (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp to a free block, read the value of pred and succ */
#define SUCC(bp)       (*(char **) (bp))

/* Given block ptr bp, compute address of the next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Global variables */
static char *heap_listp;  /* Pointer to prologue block */
static char *freelists[NUMLIST]; /* List of all segregated lists */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t size);
static void freelist_remove(void *bp);
static void freelist_insert(void *bp);

/*
 * mm-init - Initialize the heap for malloc. return -1 on error, 0 on success.
 */
int mm_init(void)
{
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);                          /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (2*WSIZE); /* heap_listp now points to prologue block */
  /* initialize all seg lists */
  for (int i = 0; i < NUMLIST; i++)
    freelists[i] = heap_listp;
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}

/*
 * malloc - allocates a block with of payload at least of size bytes.
 * Returns a block pointer to the allocated block.
 */
void *malloc (size_t size)
{
  char *bp;
  size = MAX(ALIGN(size + DSIZE), MINSIZE); /* make room for header/footer */
  
  /* Search the free list for a fit */
  if ((bp = find_fit(size)) != NULL) {
    place(bp, size);
    return bp;
  }
  
  /* No fit found. Get more memory and place the block */
  if ((bp = extend_heap((MAX(size,CHUNKSIZE))/WSIZE)) == NULL)
    return NULL;
  place(bp, size);
  return bp;
}

/*
 * free - frees allocated memory at ptr. Returns nothing.
 */
void free (void *ptr) {
  // if ptr is NULL, do nothing
  if (ptr == 0)
    return;
  size_t size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  /* coalesce ptr with adjacent free blocks */
  coalesce(ptr);
}

/*
 * realloc - allocates a block with payload of at least size bytes
 * and returns block pointer bp with the payload initialized
 * to the payload of oldptr.
 */
void *realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;
  
  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0)
  {
    free(oldptr);
    return 0;
  }
  
  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL)
    return malloc(size);
  
  /* If realloc() fails the original block is left untouched  */
  if (!(newptr = malloc(size)))
    return 0;
  
  /* Copy the old data. */
  oldsize = MIN(GET_SIZE(HDRP(oldptr)), size);
  memcpy(newptr, oldptr, oldsize);
  
  /* Free the old block. */
  free(oldptr);
  
  return newptr;
}

/*
 * calloc - allocates a block with payload of at least size bytes
 * and returns block pointer bp with the payload initialized to 0
 */
void *calloc (size_t nmemb, size_t size) {
  char *bp = malloc(nmemb * size);
  int i;
  int payload_size;
  payload_size = GET_SIZE(HDRP(bp)) - DSIZE; /* remove header/footer size */
  for (i = 0; i < payload_size; i = i + WSIZE)
    PUT(bp + i, 0);
  return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
  return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap - returns nothings if the heap conforms to the specs.
 * exits with a warning message otherwise.
 */
void mm_checkheap(int lineno) {
  char *curptr;
  char *curfree;
  char *first_free;
  
  /* check prologue */
  if (!GET_ALLOC(HDRP(heap_listp)) ||
      GET_SIZE(HDRP(heap_listp)) != DSIZE ||
      GET(HDRP(heap_listp)) != GET(FTRP(heap_listp)))
  {
    printf("Prologue block is malformed\n");
  }
  
  for (int i = 0; i < NUMLIST; i++)
    
  {
    first_free = freelists[i];
    curfree = first_free;
    printf("Start free list\n");
    /* check through free list forward */
    while (!GET_ALLOC(HDRP(curfree)))
    {
      printf("  %p\n", curfree);
      curptr = heap_listp + DSIZE;
      /* ensure free list element can be found by traversing the heap */
      while (curfree != curptr)
      {
        if (!(in_heap(curptr)))
        {
          printf("Couldn't find element of free list in heap: %i\n", lineno);
          exit(0);
        }
        curptr = NEXT_BLKP(curptr);
      }
      if (!(in_heap(curfree)))
      {
        printf("A block in free list is outside of heap: %i\n", lineno);
      }
      curfree = SUCC(curfree);
    }
    printf("Stop free list\n");
  }
  
  curptr = heap_listp + DSIZE;
  /* iterate through every block pointer */
  while (in_heap(curptr))
  {
    printf("Checking %p Size %i Alloc %i\n", curptr,
           (int) GET_SIZE(HDRP(curptr)), (int) GET_ALLOC(HDRP(curptr)));
    /* check for header/footer mismatch, minimum block size, and alignment */
    if (GET(HDRP(curptr)) != GET(FTRP(curptr)))
    {
      printf("Header %u and footer %u mismatch: %i\n", GET(HDRP(curptr)),
             GET(FTRP(curptr)), lineno);
      exit(0);
    }
    if (GET_SIZE(HDRP(curptr)) < MINSIZE)
    {
      printf("Block size %i is too small: %i\n", (int) GET_SIZE(HDRP(curptr)),
             lineno);
      exit(0);
    }
    if (!(aligned(curptr)))
    {
      printf("Block is not aligned: %i\n", lineno);
      exit(0);
    }
    
    for (int i = 0; i < NUMLIST; i++)
    {
      if (GET_SIZE(HDRP(curptr)) <= (unsigned int) 1<<i)
      {
        first_free = freelists[i];
        break;
      }
    }
    
    curfree = first_free;
    if ((GET_ALLOC(HDRP(curptr))) == 0)
    {
      /* look through free list to make sure curptr is included */
      while (curptr != curfree)
      {
        /* reached the end of the free list */
        if (GET_ALLOC(HDRP(curfree)))
        {
          printf("Unallocated block %p is not in free list: %i\n", curptr,
                 lineno);
          exit(0);
        }
        curfree = SUCC(curfree);
      }
    }
    curptr = NEXT_BLKP(curptr);
  }
  return;
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
  
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;
  
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * Use this to take care of inserting free block into free list
 * instead of directly calling freelist_insert
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  
  /* bp has no adjacent free block */
  if (prev_alloc && next_alloc)
  {
    freelist_insert(bp);
    return bp;
  }
  
  /* bp has free block to the right */
  else if (prev_alloc && !next_alloc)
  {
    freelist_remove(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  /* bp has free block to the left */
  else if (!prev_alloc && next_alloc)
  {
    freelist_remove(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  
  /* bp has free blocks to the left and right */
  else
  {
    freelist_remove(NEXT_BLKP(bp));
    freelist_remove(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  freelist_insert(bp);
  return bp;
}

/*
 * place - Place block of asize bytes at start of free block bp
 * and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));
  freelist_remove(bp);
  
  /* remaining block is large enough to make a free block */
  if ((csize - asize) >= MINSIZE)
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    coalesce(bp);
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

/*
 * find_fit - Find a fit for a block with asize bytes using first fit search.
 */
static void *find_fit(size_t asize)
{
  /* First-fit search */
  int i;
  void *bp;
  
  /* if asize is greater than 2^NUMLIST */
  if (asize > (unsigned int) 1<<(NUMLIST - 1))
  {
    bp = freelists[NUMLIST - 1];
    while (!GET_ALLOC(HDRP(bp)))
    {
      /* found a fit in current free list */
      if (asize <= GET_SIZE(HDRP(bp)))
      {
        return bp;
      }
      bp = SUCC(bp);
    }
    return NULL;
  }
  
  /* look through all free lists */
  for (i = 0; i < NUMLIST; i++)
  {
    if (asize <= (unsigned int) 1<<i)
    {
      bp = freelists[i];
      while (!GET_ALLOC(HDRP(bp)))
      {
        /* found a fit in current free list */
        if (asize <= GET_SIZE(HDRP(bp)))
        {
          return bp;
        }
        bp = SUCC(bp);
      }
    }
  }
  
  return NULL; /* No fit */
}

/*
 * freelist_remove - remove the free block at block pointer bp
 * from its corresponding free list.
 */
static void freelist_remove(void *bp)
{
  size_t succ_alloc = GET_ALLOC(HDRP(SUCC(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  int i;
  
  /* find free list that contains bp */
  for (i = 0; size > (unsigned int) 1<<i; i++) {}
  i = MIN(i, NUMLIST - 1);
  
  /* bp is alone in the free list */
  if (bp == freelists[i] && succ_alloc)
  {
    freelists[i] = heap_listp;
  }
  
  /* bp is first but not last */
  else if (bp == freelists[i] && !succ_alloc)
  {
    freelists[i] = SUCC(bp);
  }
  
  /* bp is not first */
  else
  {
    char *prevptr = freelists[i];
    while (SUCC(prevptr) != bp)
      prevptr = SUCC(prevptr);
    SUCC(prevptr) = SUCC(bp);
  }
  return;
}

/*
 * freelist_insert - locate and insert bp into the correct position in 
 * the corresponding free list ordered in first-in last-out.
 */
static void freelist_insert(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));
  int i;
  
  /* find free list that contains bp */
  for (i = 0; size > (unsigned int) 1<<i; i++) {}
  i = MIN(i, NUMLIST - 1);
  SUCC(bp) = freelists[i];
  freelists[i] = bp;
  return;
}