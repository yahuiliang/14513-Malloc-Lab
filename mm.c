/*
 ******************************************************************************
 *                                   mm.c                                     *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                           Yahui self-implemented heap. :)                  *
 *           The heap uses the best-fit strategy to allocate memory           *
 *           to the program. The max search limit is 10 (find the best one    *
 *           from 10 free blocks). Once this limit has been reached,          *
 *           one block with the minimum fragmentation will be allocated.      *
 *           If none free block is found, the heap will be extended by a      *
 *           chunksize and allocate that memory to the program. If the whole  *
 *           block is too big, it will be splited. The splited part will be   *
 *           added to the free list.                                          *
 *                                                                            *
 *           Free blocks are managed by using the FILO                        *
 *           rule, and they are linked together by using the double-linked    *
 *           list. The segregated list is implemented for optimizing the      *
 *           utilization and throughput of the malloc and free. Different     *
 *           block sizes are assigned to different classes. And each class    *
 *           is a free list.                                                  *
 *                                                                            *
 *           Allocated blocks have the fields of header and payload. The      *
 *           upper bits record the size of the block, and the last 4 bits     *
 *           record prev_min (last 2nd, set if the previous block is mini     *
 *           block), prev_alloc (last 1st, set if the previous block is       *
 *           allocated), and alloc(last, set if the current block is          *
 *           allocated). When the allocated block gets freed, it will         *
 *           determine whether it should be coalesced with others based       *
 *           on these bits.                                                   *
 *                                                                            *
 *           Free blocks have two different sub-divisions: mini blocks and    *
 *           normal blocks. For mini blocks, they only have the header        *
 *           and the next free pointer. For normal blocks, they have the      *
 *           header, the next/prev free pointer, and the footer. Since mini   *
 *           blocks do not have the previous free pointer, when we want to    *
 *           search the previous free block based on the current one, we must *
 *           iterate whole free list to find it. The footer is used for       *
 *           determining the previous block size when coalescing.             *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/*
 * Author: Yahui Liang
 * Email: yahuil@andrew.cmu.edu
 * AndrewID: yahuil
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined (such as when running mdriver-dbg), these macros
 * are enabled. You can use them to print debugging output and to check
 * contracts only in debug mode.
 *
 * Only debugging macros with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */
typedef uint64_t word_t;

// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);

// Double word size (bytes)
static const size_t dsize = 2 * wsize;

// Minimum block size (bytes)
static const size_t min_block_size = dsize;

// The amount of the heap should be extended when
// no block size is big enough for the new allocation
// (Must be divisible by dsize)
static const size_t chunksize = (1 << 12);

// The mask for the last bit of the header (alloc bit)
static const word_t alloc_mask = 0x1;

// The mask for the last second bit of the header (prev alloc bit)
static const word_t prev_alloc_mask = 0x1 << 1;

// The mask for the last third bit of the header (if prev block is tiny block)
static const word_t prev_min_mask = 0x1 << 2;

// Payload is aligned to dsize (16), therefore,
// the lower 4 bits of the header are "dont care"
static const word_t size_mask = ~(word_t)0xF;

// The max search number for the best-fit approach
static const unsigned max_search = 10;

/* Represents the header and payload of one block in the heap */
typedef struct block {
  /* Header contains size + allocation flag */
  word_t header;

  /*
   * We don't know what the size of the payload will be, so we will declare
   * it as a zero-length array, which is a GCC compiler extension. This will
   * allow us to obtain a pointer to the start of the payload.
   *
   * WARNING: A zero-length array must be the last element in a struct, so
   * there should not be any struct fields after it. For this lab, we will
   * allow you to include a zero-length array in a union, as long as the
   * union is the last field in its containing struct. However, this is
   * compiler-specific behavior and should be avoided in general.
   *
   * WARNING: DO NOT cast this pointer to/from other types! Instead, you
   * should use a union to alias this zero-length array with another struct,
   * in order to store additional types of data in the payload memory.
   */
  char payload[0];

  /*
   * Do not inlcude footer here, since it will
   * override the payload.
   */
} block_t;

/*
 * Cast the point for arithmetic operations.
 */
typedef union {
  void *ptr;
  long addr;
} mem;

/*
 * The link for connecting between previous free block
 * and the next free block.
 */
typedef struct {
  block_t *next;
  block_t *prev;
} link_t;

/*
 * Payload and free pointer aliasing
 */
typedef union {
  link_t *link;
  char *ptr;
} node_t;

/* Global variables */

// Pointer to first block
static block_t *heap_start = NULL;

// Segregated free block lists
static block_t *free_start[15];

/* Function prototypes for internal helper routines */

bool mm_checkheap(int lineno);

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *coalesce_block(block_t *block);
static void split_block(block_t *block, size_t asize);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_min);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool extract_prev_alloc(word_t header);
static bool get_prev_alloc(block_t *block);
static bool extract_prev_min(word_t header);
static bool get_prev_min(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc,
                         bool prev_alloc, bool prev_min);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void free_add(block_t *block);
static void free_remove(block_t *block);
static block_t *free_next(block_t *block);
static block_t *free_prev(block_t *block);
static block_t *free_prev_mini(block_t *block);
static void set_free_next(block_t *block, block_t *block_next);
static void set_free_prev(block_t *block, block_t *block_prev);
static bool free_empty(unsigned class);

static bool is_in_range(void *ptr);
static bool is_aligned(void *ptr);

static unsigned get_block_class(block_t *block);
static unsigned get_class(size_t size);

static bool check_prologue_epilogue(word_t *word);
static bool check_size(block_t *block);
static bool check_alloc(block_t *block);
static bool check_prev_next_connection(block_t *block, block_t *block_prev);
static bool check_consecutive_free(block_t *block, block_t *block_prev);
static bool check_free_link(block_t *block);

/*
 * Init the heap by extending 4096 bytes.
 *
 * returns true if the initialization is successful,
 * false otherwise.
 */
bool mm_init(void) {
  int i, len = sizeof(free_start) / sizeof(block_t *);
  // Create the initial empty heap
  word_t *start = (word_t *)(mem_sbrk(2 * wsize));

  /*
   * Runs out of memory for extending the heap
   */
  if (start == (void *)-1) {
    return false;
  }

  /*
   * Prologue and epologue have same strucuter as
   * header and footer. However, their allocated
   * bit is always set, and the length of payload is zero.
   *
   * The prologue is for the payload alignment (16).
   * The epilogue marks the end of the heap (the place where to
   * stop searching free blocks).
   */

  start[0] = pack(0, true, true, false); // Heap prologue (block footer)
  start[1] = pack(0, true, true, false); // Heap epilogue (block header)

  // Heap starts with first "block header", currently the epilogue
  heap_start = (block_t *)&(start[1]);

  // Initialize the free list
  for (i = 0; i < len; i++)
    free_start[i] = NULL;

  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(chunksize) == NULL) {
    return false;
  }

  return true;
}

/*
 * Malloc <size> bytes on heap
 * Returns the pointer points to the allocated start
 */
void *malloc(size_t size) {
  dbg_requires(mm_checkheap(__LINE__));

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;

  if (heap_start == NULL) // Initialize heap if it isn't initialized
  {
    mm_init();
  }

  if (size == 0) // Ignore spurious request
  {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // Adjust block size to include overhead and to meet alignment requirements
  asize = round_up(size + wsize, dsize);
  if (asize < min_block_size)
    asize = min_block_size;

  // Search the free list for a fit
  block = find_fit(asize);

  // If no fit is found, request more memory, and then and place the block
  if (block == NULL) {
    // Always request at least chunksize
    extendsize = max(asize, chunksize);
    block = extend_heap(extendsize);
    if (block == NULL) // extend_heap returns an error
    {
      return bp;
    }
  }

  // The block should be marked as free
  dbg_assert(!get_alloc(block));
  // The malloced block should be removed from the free list
  // since it is not free anymore
  free_remove(block);

  // Mark block as allocated
  size_t block_size = get_size(block);
  write_header(block, block_size, true, get_prev_alloc(block),
               get_prev_min(block));

  // Try to split the block if too large
  split_block(block, asize);

  bp = header_to_payload(block);

  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
}

/*
 * Frees the pointer <bp> previously allocated by malloc
 * If <bp> is freed originally, nothing will be done
 */
void free(void *bp) {
  block_t *block;
  size_t size;

  dbg_requires(mm_checkheap(__LINE__));

  if (bp == NULL)
    return;

  block = payload_to_header(bp);

  if (!get_alloc(block))
    return;

  size = get_size(block);

  // The block should be marked as allocated
  dbg_assert(get_alloc(block));

  // Mark the block as free
  write_header(block, size, false, get_prev_alloc(block), get_prev_min(block));
  write_footer(block, size, false);

  // Try to coalesce the block with its neighbors
  block = coalesce_block(block);

  dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * Reallocate the <ptr> to the new <size>
 * Returns the pointer points to the new start
 */
void *realloc(void *ptr, size_t size) {
  void *newptr;
  block_t *block, *block_next;
  bool next_alloc;
  size_t asize, block_size;

  // If ptr is NULL, then equivalent to malloc
  if (ptr == NULL) {
    return malloc(size);
  }
  // If size == 0, free memory and return NULL
  if (size == 0) {
    free(ptr);
    return NULL;
  }

  newptr = NULL;
  block = payload_to_header(ptr);
  block_next = find_next(block);
  next_alloc = get_alloc(block_next);

  asize = round_up(size + wsize, dsize);
  // If the size is too small, round it up to mini block size
  if (asize < min_block_size)
    asize = min_block_size;

  block_size = get_size(block);
  if (!next_alloc) {
    // Sum up the size with the next free block if exists
    block_size += get_size(block_next);
  }
  if (block_size < asize) {
    // The current block pointed by ptr cannot satisfy the new size
    // malloc the new one
    newptr = malloc(size);
    if (newptr == NULL)
      // no more space
      return NULL;
    // Copy the content
    memcpy(newptr, ptr, get_payload_size(block));
    free(ptr);
  } else {
    // The current block is large enough to be reallocated
    if (!next_alloc)
      // Coalesce with the next free block
      free_remove(block_next);
    // Update the size
    write_header(block, block_size, true, get_prev_alloc(block),
                 get_prev_min(block));
    // Split the block if too large
    split_block(block, asize);
    newptr = block->payload;
  }
  return newptr;
}

/*
 * Malloc <elements * size> bytes, with all set to 0
 */
void *calloc(size_t elements, size_t size) {
  void *bp;
  size_t asize = elements * size;

  if (asize / elements != size) {
    // Multiplication overflowed
    return NULL;
  }

  bp = malloc(asize);
  if (bp == NULL) {
    return NULL;
  }

  // Initialize all bits to 0
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * Extend the heap if the current one is not big enough
 */
static block_t *extend_heap(size_t size) {
  void *bp;

  // Allocate an even number of words to maintain alignment
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  /*
   * The new un-allocated block's start is pointed by bp now
   */

  // Initialize free block header/footer
  block_t *block = payload_to_header(bp);
  write_header(block, size, false, get_prev_alloc(block), get_prev_min(block));
  write_footer(block, size, false);

  // Create new epilogue header
  block_t *block_next = find_next(block);
  // prev_alloc and prev_min flags should be marked as false
  // since the fresh extended heap is not used and its size
  // must be greater than 16
  write_header(block_next, 0, true, false, false);

  // Coalesce in case the previous block was free
  block = coalesce_block(block);

  return block;
}

/*
 * Merge free blocks if adjacents are both free
 */
static block_t *coalesce_block(block_t *block) {
  dbg_requires(!get_alloc(block));

  size_t size = get_size(block);

  /*
   * The footer is removed for allocated blocks
   * Therefore, a prev alloc flag is guarded here
   * to ensure do not extract footer for allocated
   * blocks.
   */

  block_t *block_next = find_next(block);
  block_t *block_prev;

  bool prev_alloc = get_prev_alloc(block);
  bool next_alloc = get_alloc(block_next);

  if (prev_alloc && next_alloc) // Case 1
  {
    // Only the current block will be marked with free
    // Add it to the free list
    free_add(block);
  }

  else if (prev_alloc && !next_alloc) // Case 2
  {
    // Merge the next block with the current one
    // 1. Remove next from the free list
    // 2. Update the size of the current block
    // 3. Add the current block to the free list
    free_remove(block_next);
    size += get_size(block_next);
    write_header(block, size, false, get_prev_alloc(block),
                 get_prev_min(block));
    write_footer(block, size, false);
    free_add(block);
  }

  else if (!prev_alloc && next_alloc) // Case 3
  {
    // Merge the previous block with the current one
    // 1. Remove prev from the free list
    // 2. Update the size of the previous block
    // 3. Add the previous block to the free list
    block_prev = find_prev(block);
    free_remove(block_prev);
    size += get_size(block_prev);
    write_header(block_prev, size, false, get_prev_alloc(block_prev),
                 get_prev_min(block_prev));
    write_footer(block_prev, size, false);
    block = block_prev;
    free_add(block);
  }

  else // Case 4
  {
    // Merge both the previous one and the next one with the current one
    // 1. Remove prev from the free list
    // 2. Remove next from the free list
    // 3. Update the size of the previous block
    // 4. Add the previous block to the free list
    block_prev = find_prev(block);
    free_remove(block_prev);
    free_remove(block_next);
    size += get_size(block_next) + get_size(block_prev);
    write_header(block_prev, size, false, get_prev_alloc(block_prev),
                 get_prev_min(block_prev));
    write_footer(block_prev, size, false);
    block = block_prev;
    free_add(block);
  }

  // Set the next block's prev alloc flag to false
  // Free blocks are coalesced, determine if the size is 16 and set
  // prev_min flag in the next block
  block_next = find_next(block);
  write_header(block_next, get_size(block_next), get_alloc(block_next), false,
               get_size(block) == min_block_size);

  dbg_ensures(!get_alloc(block));

  return block;
}

/*
 * Split the block if i<allocated size> is much smaller than the amount than the
 * <block> can hold
 */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block));

  size_t block_size = get_size(block);
  block_t *block_next;

  if ((block_size - asize) >= min_block_size) {
    // Write the new size to the block
    write_header(block, asize, true, get_prev_alloc(block),
                 get_prev_min(block));

    // Add the splited part into the free list,
    // if allocated part is mini size, the prev_min
    // flag should be set in the splited part.
    block_next = find_next(block);
    write_header(block_next, block_size - asize, false, true,
                 asize == min_block_size);
    write_footer(block_next, block_size - asize, false);
    free_add(block_next);

    // Set the prev alloc flag to the block just after the whole block before
    // splited. Its prev_min flag should also be set if the splited part is
    // mini size.
    block_next = find_next(block_next);
    write_header(block_next, get_size(block_next), get_alloc(block_next), false,
                 block_size - asize == min_block_size);
  } else {
    /*
     * The block size is just the mini size.
     * Sets the next block prev_min flag to true
     */
    block_next = find_next(block);
    write_header(block_next, get_size(block_next), get_alloc(block_next), true,
                 true);
  }
  dbg_ensures(get_alloc(block));
}

/*
 * Find the block whose size greater or equal to <asize>
 */
static block_t *find_fit(size_t asize) {
  unsigned class;
  unsigned classes = sizeof(free_start) / sizeof(block_t *);
  block_t *block;
  size_t size;
  unsigned count = 0;
  block_t *slot = NULL;
  // Iterate through all free classes to find available ones
  for (class = get_class(asize); class < classes && !slot; class ++) {
    block = free_start[class];
    while (block) {
      size = get_size(block);
      // Check if the block can be allocated
      if (asize <= size) {
        // The block can be allocated
        if (!slot || size < get_size(slot)) {
          // The current block minimizes the fragmentation
          // Assign that to the return val
          slot = block;
        }
        count++;
      }
      // Check if the current max best fit search has reached
      if (count >= max_search)
        return slot;
      // Jump to the next block in the free list
      block = free_next(block);
    }
  }
  return slot;
}

/*
 * Heap Consistency Checker
 */
bool mm_checkheap(int line) {
  word_t *prologue = find_prev_footer(heap_start);
  word_t *epilogue;
  block_t *block = heap_start;
  block_t *block_prev = NULL;
  long free_counts = 0;
  unsigned i, len = sizeof(free_start) / sizeof(block_t *);

  // Prologue should be allocated, and marked the start of the heap
  if (!check_prologue_epilogue(prologue))
    return false;

  while (get_size(block) > 0) {
    // payload should be aligned to 16
    if (!is_aligned(block->payload))
      return false;
    // Check the boundary
    if (!is_in_range(block))
      return false;
    // Check if the header size matches with footer size
    if (!check_size(block))
      return false;
    // Check if allocated flags are same between footer and header
    if (!check_alloc(block))
      return false;
    // Check if prev block and next block are connected correctly with the
    // current one
    if (!check_prev_next_connection(block, block_prev))
      return false;
    // Check no two consecutive free blocks
    if (!check_consecutive_free(block, block_prev))
      return false;
    // Check if the free block is linked correctly
    if (!check_free_link(block))
      return false;
    // Check if prev alloc flag is set correctly
    if (block_prev && get_alloc(block_prev) != get_prev_alloc(block))
      return false;
    // Count free blocks
    if (!get_alloc(block))
      free_counts++;
    block_prev = block;
    block = find_next(block);
  }

  // Epilogue should remain allocated, and mark the end of the heap
  epilogue = &(block->header);
  if (!check_prologue_epilogue(epilogue))
    return false;

  // Check if there is a circle in the free list
  for (i = 0; i < len; i++) {
    // Iterate through the segregated list
    block = free_start[i];
    while (block) {
      free_counts--;
      // Check the boundary
      if (!is_in_range(block))
        return false;
      // Check if there is a circle in the list
      if (free_counts < 0)
        return false;
      // Check if the block belongs to the right class
      if (get_block_class(block) != i)
        return false;
      // The block is the free list should not be allocated
      if (get_alloc(block))
        return false;

      block = free_next(block);
    }
  }
  // Check if there are some free blocks not added into the free list
  if (free_counts > 0)
    return false;
  return true;
}

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ba c1 e1 52 13 0a               *
 *                                                                           *
 *****************************************************************************
 */

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n) {
  return n * ((size + (n - 1)) / n);
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_min) {
  word_t packed;
  packed = alloc ? size | alloc_mask : size;
  packed = prev_alloc ? packed | prev_alloc_mask : packed;
  packed = prev_min ? packed | prev_min_mask : packed;
  return packed;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word) { return (word & size_mask); }

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block) { return extract_size(block->header); }

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block) {
  size_t asize = get_size(block);
  return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word) { return (bool)(word & alloc_mask); }

/*
 * extract_prev_alloc: returns the allocation status of the previous block
 *                     in the given header
 */
static bool extract_prev_alloc(word_t word) {
  return (bool)(word & prev_alloc_mask);
}

/*
 * extract_prev_min: returns if the previous block is mini block
 *                   in the given header
 */
static bool extract_prev_min(word_t word) {
  return (bool)(word & prev_min_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block) { return extract_alloc(block->header); }

static bool get_prev_alloc(block_t *block) {
  return extract_prev_alloc(block->header);
}

/*
 * get_prev_min: returns if the previous blocvk is mini block
 */
static bool get_prev_min(block_t *block) {
  return extract_prev_min(block->header);
}

/*
 * write_header: given a block and its size, allocation status,
 *               previous allocation status, and previous block size status
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc,
                         bool prev_alloc, bool prev_min) {
  dbg_requires(block != NULL);
  block->header = pack(size, alloc, prev_alloc, prev_min);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) == size && size > 0);
  // If the size is less or equal to 16, it is the mini block
  // and it does not have the footer
  if (get_size(block) <= min_block_size)
    return;
  word_t *footerp = header_to_footer(block);
  *footerp = pack(size, alloc, false, false);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  if (block == NULL || get_size(block) == 0)
    return NULL;
  return (block_t *)((char *)block + get_size(block));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block) {
  // Compute previous footer position as one word before the header
  return &(block->header) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block) {
  word_t *footerp;
  size_t size;
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);
  if (block == NULL || get_size(block) == 0)
    return NULL;
  if (get_prev_min(block)) {
    // The previous block is the mini block
    return (block_t *)((char *)block - min_block_size);
  } else {
    // The normal block has the footer
    // and it is extracted to determine the size
    footerp = find_prev_footer(block);
    size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
  }
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp) {
  return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block) {
  return (void *)(block->payload);
}

/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 */
static word_t *header_to_footer(block_t *block) {
  return (word_t *)(block->payload + get_size(block) - dsize);
}

/*************************************************************************/

/*
 * The free list uses FILO rule to insert and remove elements
 */

/*
 * Add the block to the free list
 */
static void free_add(block_t *block) {
  unsigned class;
  block_t *block_next = NULL;
  block_t *block_prev = NULL;
  size_t size;

  if (!block)
    return;

  class = get_block_class(block);
  block_next = free_start[class];
  size = get_size(block);

  // Connect the new block with the free list head
  set_free_prev(block_next, block);
  set_free_next(block, block_next);
  set_free_next(block_prev, block);
  set_free_prev(block, block_prev);

  // Reset the head of the list
  free_start[class] = block;
}

/*
 * Remove the block from the free list
 */
static void free_remove(block_t *block) {
  block_t *block_next;
  block_t *block_prev;
  unsigned class;

  if (!block)
    return;

  class = get_block_class(block);
  block_next = free_next(block);
  block_prev = free_prev(block);

  // Disconnect and Reconnect free pointers
  set_free_prev(block_next, block_prev);
  set_free_next(block_prev, block_next);

  if (block == free_start[class])
    free_start[class] = block_next;
}

/*********************************************************************/

/*
 * Get the next free block
 */
static block_t *free_next(block_t *block) {
  node_t node;
  if (!block || get_alloc(block))
    return NULL;
  node.ptr = block->payload;
  return node.link->next;
}

/*
 * Get the previous free block
 */
static block_t *free_prev(block_t *block) {
  node_t node;
  if (!block || get_alloc(block))
    return NULL;
  if (get_size(block) <= min_block_size) {
    // Switch to tiny version
    return free_prev_mini(block);
  } else {
    node.ptr = block->payload;
    return node.link->prev;
  }
}

/*
 * Sets the next free pointer for the current free block
 */
static void set_free_next(block_t *block, block_t *block_next) {
  node_t node;
  // If the size is less than 16, next free pointer cannot be hold by the block
  if (!block || get_size(block) < min_block_size)
    return;
  node.ptr = block->payload;
  node.link->next = block_next;
}

/*
 * Sets the previous free pointer for the current block
 */
static void set_free_prev(block_t *block, block_t *block_prev) {
  node_t node;
  // The mini block cannot hold the previous free pointer
  if (!block || get_size(block) <= min_block_size)
    return;
  node.ptr = block->payload;
  node.link->prev = block_prev;
}

/*
 * Mini free blocks do not have the previous free pointer.
 * This function iterate through the free list to find
 * the previous free block corresponds to the current one
 */
static block_t *free_prev_mini(block_t *block) {
  unsigned class;
  block_t *itr;
  block_t *block_prev = NULL;
  // Only mini free blocks are allowed to use this function
  if (!block || get_alloc(block) || get_size(block) > min_block_size)
    return NULL;
  class = get_block_class(block);
  itr = free_start[class];
  while (itr) {
    if (itr == block)
      return block_prev;
    block_prev = itr;
    itr = free_next(itr);
  }
  return NULL;
}

/*
 * Check whether the free list <class> is empty
 */
static bool free_empty(unsigned class) { return free_start[class] == NULL; }

/*
 * Check if the <ptr> is in the valid heap range
 */
static bool is_in_range(void *ptr) {
  void *lo = mem_heap_lo();
  void *hi = mem_heap_hi();
  return lo <= ptr && ptr <= hi;
}

/*
 * Check if the current address is aligned with 16
 */
static bool is_aligned(void *ptr) {
  mem m;
  m.ptr = ptr;
  return (m.addr % dsize) == 0;
}

/*
 * Get the block class in the segregated list based on its size
 */
static unsigned get_block_class(block_t *block) {
  unsigned size;
  if (!block || get_alloc(block))
    return -1;
  size = get_size(block);
  return get_class(size);
}

/*
 * Get the class in the segregated list based on the size
 */
static unsigned get_class(size_t size) {
  unsigned class;
  size_t len = sizeof(free_start) / sizeof(block_t *);
  if (size <= min_block_size)
    return 0;
  class = 1;
  // class 1: [17, 32]; class 2: [33, 64]; class 3: [65, 128] ...
  while (size > min_block_size && class < len) {
    class ++;
    size >>= 1;
  }
  return class >= len ? len - 1 : class;
}

/*
 * Check if the prologue and epilogue are valid
 * by looking at their allocated flag, size, and
 * actual memory location.
 */
static bool check_prologue_epilogue(word_t *word) {
  return extract_alloc(*word) && (extract_size(*word) == 0) &&
         is_in_range(word);
}

/*
 * Check if the header size matches with the footer size
 *
 * true: pass
 * false: fail
 */
static bool check_size(block_t *block) {
  bool pass = true;
  word_t footer;
  size_t header_size;
  size_t footer_size;
  if (!get_alloc(block) && get_size(block) > min_block_size) {
    footer = *(header_to_footer(block));
    header_size = get_size(block);
    footer_size = extract_size(footer);
    pass = header_size == footer_size;
  }
  return pass;
}

/*
 * Check if the allocation flag is same between
 * header and footer
 *
 * true: pass
 * false: fail
 */
static bool check_alloc(block_t *block) {
  bool pass = true;
  word_t footer;
  bool header_a;
  bool footer_a;
  if (!get_alloc(block) && get_size(block) > min_block_size) {
    footer = *(header_to_footer(block));
    header_a = get_alloc(block);
    footer_a = extract_alloc(footer);
    pass = header_a == footer_a;
  }
  return pass;
}

/*
 * Check if the block can connect to prev and next block
 * correctly by using header and footer
 *
 * true: pass
 * false: fail
 */
static bool check_prev_next_connection(block_t *block, block_t *block_prev) {
  bool pass = true;
  if (block_prev && block_prev != block && get_size(block_prev) > 0)
    pass = pass && block == find_next(block_prev);
  return pass;
}

/*
 * Check if two consecutive free exists
 *
 * true: pass (no consecutive exists)
 * false: fail (consecutive exists)
 */
static bool check_consecutive_free(block_t *block, block_t *block_prev) {
  bool a = get_alloc(block);
  bool a_prev = true;
  bool a_next = true;
  block_t *block_next = find_next(block);
  if (block_prev)
    a_prev = get_alloc(block_prev);
  if (block_next)
    a_next = get_alloc(block_next);
  return (a || a_prev) && (a || a_next);
}

/*
 * Check if free blocks are linked properly
 *
 * true: pass
 * false: fail
 */
static bool check_free_link(block_t *block) {
  block_t *prev_free;
  block_t *next_free;
  if (!get_alloc(block)) {
    prev_free = free_prev(block);
    next_free = free_next(block);
    if (prev_free != NULL && free_next(prev_free) != block)
      return false;
    if (next_free != NULL && free_prev(next_free) != block)
      return false;
  }
  return true;
}
