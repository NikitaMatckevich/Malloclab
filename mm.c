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
    "Nikita Matckevich",
    /* First member's email address */
    "nikita.matckevich@ensta-paris.fr",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PTR_T_SIZE (ALIGN(sizeof(void*)))

// block types

#define FREE 0
#define OCCUPIED 1
#define NO_MATTER 2

// returns the address that lies in len bytes before or after ptr
#define OFFSET(ptr, len) (void*)((char*)(ptr) + (len))

enum { IMPLICIT, EXPLICIT, SEGREGATED} heap_type;
enum { FIRST_FIT, NEXT_FIT, BEST_FIT } search_policy;
size_t  nb_components;
size_t* sizes;
void**  linked_components;

void* blocks;

void mm_check(void);

// finder for implicit lists
// len = 2*SIZE_T_SIZE + size of payload
static void* imp_find_block(size_t len)
{
  static void* res = NULL;
  void* end = mem_heap_hi();
  size_t s;

  switch (search_policy) {
  
  case FIRST_FIT: ;

    res = blocks;
    while (s = *(size_t*)res, (res < end) && ((s & 1) || (s < len))) {
      res = OFFSET(res, (s & -2));
    }
    if (res >= end) {
      res = NULL;
    }
    break;

  case BEST_FIT: ;

    size_t dist = mem_heapsize();
   
    res = NULL;

    for (void* p = blocks; p < end; p = OFFSET(p, (s & -2))) {
      s = *(size_t*)p;
      if (!(s & 1) && (s >= len) && (dist > s - len)) {
          res = p;
          dist = s - len;
      }
    }
    break;
  
  default:
    printf("unexpected seacrh policy\n");
    exit(8);
  }

  return res;
}

// finder for explicit lists
// len = 2*SIZE_T_SIZE + max(size of payload, 2*PTR_T_SIZE)
static void* exp_find_block(size_t len)
{
  static void* res;
  
  size_t i = 0;
  while (i < nb_components - 1 && len > sizes[i]) {
    ++i;
  }

  while (i < nb_components) {

    switch (search_policy) {
    
    case FIRST_FIT: ;
      res = linked_components[i];
      size_t s;
      while ((res != NULL) &&
            (s = *(size_t*)OFFSET(res, -PTR_T_SIZE - SIZE_T_SIZE),
            ((s & 1) || (s < len))))
      {
        res = *(void**)res;
      }
      if (res != NULL) {
        return OFFSET(res, -PTR_T_SIZE - SIZE_T_SIZE);
      }
      break;

    case BEST_FIT: ;
      void* p = linked_components[i];
      size_t dist = mem_heapsize();

      for (size_t s = *(size_t*)OFFSET(p, -PTR_T_SIZE - SIZE_T_SIZE);
           (p != NULL); p = *(void**)p)
      {
        if (!(s & 1) && (s >= len) && (dist > s - len)) {
          res = p;
          dist = s- len;
        }
      }
      if (res != NULL) {
        return OFFSET(res, -PTR_T_SIZE - SIZE_T_SIZE);
      }
      break;
  
    default:
      printf("unexpected seacrh policy\n");
      exit(8);
    }

    i++;
  }

  return NULL;
}

// delete element from free block queue, p is a pointer to the very beginning
// of the block
static void delete_from_queue(void* p) {

  void** to_prev = (void**)OFFSET(p, SIZE_T_SIZE);
  void** to_next = (void**)OFFSET((void*)to_prev, PTR_T_SIZE);
  
  size_t i = 0;
  size_t len = *(size_t*)p;
  while (i < nb_components-1 && len > sizes[i]) {
    ++i;
  }

  if (*to_prev == NULL) {
    linked_components[i] = *to_next;
  } else {
    void** next_of_prev = (void**)OFFSET(*to_prev, PTR_T_SIZE);
    *next_of_prev = *to_next;
  }

  if (*to_next != NULL) {
    void** prev_of_next = (void**)OFFSET(*to_next, -PTR_T_SIZE);
    *prev_of_next = *to_prev;
  }
}

// add element to the queue, p is a pointer to the very beginning of the block
static void add_to_queue(void* p) {

  size_t len = *(size_t*)p;
  
  void** to_prev = (void**)OFFSET(p, SIZE_T_SIZE);
  void** to_next = (void**)OFFSET((void*)to_prev, PTR_T_SIZE);
  
  size_t i = 0;
  while (i < nb_components-1 && len > sizes[i]) {
    ++i;
  }
   
  *to_prev = NULL;
  *to_next = linked_components[i];
  linked_components[i] = (void*)to_next;

  if (*to_next != NULL) {
    void** prev_of_next = (void**)OFFSET(*to_next, -PTR_T_SIZE);
    *prev_of_next = (void*)to_prev;
  }
}

// free block pointed by *p, change the *p value in case of coalescing
static void free_block(void** p) {

  size_t* bbeg = (size_t*)(*p);
  *bbeg = *bbeg & -2;

  size_t* bend = (size_t*)OFFSET(*p, *bbeg - SIZE_T_SIZE);
  *bend = *bend & -2;

  size_t bsize = *bend;

  if (OFFSET((void*)bend, SIZE_T_SIZE) < mem_heap_hi()) {
    size_t* next = (size_t*)OFFSET((void*)bend, SIZE_T_SIZE);
    if ((*next & 1) == FREE) {
      bsize += *next;
      bend = (size_t*)OFFSET((void*)bend, *next);
      if (heap_type == EXPLICIT) {
        delete_from_queue((void*)next);
      }
    }
  }

  if ((void*)bbeg > blocks) {
    size_t* prev = (size_t*)OFFSET((void*)bbeg, -SIZE_T_SIZE);
    if ((*prev & 1) == FREE) {
      bsize += *prev;
      bbeg = (size_t*)OFFSET((void*)bbeg, -(*prev));
      if (heap_type == EXPLICIT) {
        delete_from_queue((void*)bbeg);
      }
    }
  }
  
  *bbeg = bsize;
  *bend = bsize;

  if (heap_type == EXPLICIT) {
    add_to_queue((void*)bbeg);
  }

  *p = bbeg;
}

// occupy the block in the heap, called by malloc
static void add_block(void* p, size_t len) {
 
  if (heap_type == EXPLICIT) {
    delete_from_queue(p);
  }
  
  size_t pload_threshold = 2*SIZE_T_SIZE;
  pload_threshold += ((heap_type == IMPLICIT) || (SIZE_T_SIZE > 2*PTR_T_SIZE)) ?
    SIZE_T_SIZE : 2*PTR_T_SIZE;
  
  size_t* bbeg = (size_t*)p;
  size_t old_size = *bbeg;
 
  if (old_size - len < pload_threshold) {
    len = old_size;
  }

  size_t* bend = (size_t*)OFFSET(p, len - SIZE_T_SIZE);
  *bbeg = len | 1;
  *bend = len | 1;
  
  if (old_size - len >= pload_threshold) {
    size_t resid_len = old_size - len;
    size_t* resid_beg = (size_t*)OFFSET(p, len);
    size_t* resid_end = (size_t*)OFFSET(p, old_size - SIZE_T_SIZE);
    *resid_beg = resid_len;
    *resid_end = resid_len;
    if (heap_type == EXPLICIT) {
      add_to_queue((void*)resid_beg);
    }
  }
}

// adjust heap size if needed
static void* adjust_heap(size_t size)
{
  size_t adjust_size = size;
  size_t last_size = *(size_t*)OFFSET(mem_heap_hi(), -SIZE_T_SIZE + 1);
  if ((last_size & 1) == FREE) {
    adjust_size -= last_size;
  } else {
    last_size = 0;
  }

  void* adjust = mem_sbrk(adjust_size);
  if (adjust == NULL) {
    printf("cannot adjust heap no more\n");
    printf("\theap size = %d", mem_heapsize());
    exit(8);
  }
  void* adjust_end = OFFSET(adjust, adjust_size - SIZE_T_SIZE);

  *(size_t*)adjust = adjust_size;
  *(size_t*)adjust_end = adjust_size;

  free_block(&adjust);
  
  return adjust;
}

// print LIFO queues of free blocks
static void print_linked_components(void) {
  for (size_t i = 0; i < nb_components; ++i) {
    void* curr;
    void* prev;

    curr = linked_components[i];
    prev = NULL;
    printf("[list %i] forward:\n", i);
    while (curr != NULL) {
      printf("\tcurrent block : %p\n", curr);
      printf("\tnext block    : %p\n", *(void**)curr);
      prev = curr;
      curr = *(void**)curr;
      if (prev == curr) {
        char ch;
        scanf("%c", &ch);
      }
    }

    if (prev != NULL) {
      curr = OFFSET(prev, -PTR_T_SIZE);
      prev = NULL;
    }
    while (curr != NULL) {
      printf("\tcurrent block  : %p\n", curr);
      printf("\tprevious block : %p\n", *(void**)curr);
      prev = curr;
      curr = *(void**)curr;
    }
  }
}
/*
static void backup(void) {
  for (int e = 15; e >= 0; e--) {
    switch (codes[e].code) {
    case 1: free_block(&codes[e].address); break;
    case 2: add_block(codes[e].address, codes[e].size); break;
    case 3: printf("OOO i'm nor prepared for that!\n"); break;
    default: break;
    }
  }
}

static void repeat(void) {
  for (int e = 0; e <= 15; e++) {
    switch (codes[e].code) {
    case 1: add_block(codes[e].address, codes[e].size); break;
    case 2: free_block(&codes[e].address); break;
    case 3: printf("OOO i'm nor prepared for that!\n"); break;
    default: break;
    }
    print_linked_components();
  }
}
*/
static int check_bounds(void* p, int status)
{
  size_t* bbeg = (size_t*)p;
  size_t* bend = (size_t*)OFFSET(bbeg, (*bbeg & -2) - SIZE_T_SIZE);
  if (*bbeg != *bend) {
    printf("left and right block sizes aren't equal\n");
    return 0;
  }

  if ((status != NO_MATTER) && ((*bbeg & 1) != (size_t)status)) {
    printf("block in free list marked as occupied\n");
    return 0;
  }

  if ((*bbeg & 1) == 0) {
    if ((void*)bbeg > blocks) {
      size_t* prev_end = (size_t*)OFFSET(bbeg, -SIZE_T_SIZE);
      if ((*prev_end & 1) == FREE) {
        printf("consecutive blocks escaped coalescing\n");
        return 0;
      }
    }
    if (OFFSET(bend, SIZE_T_SIZE) < mem_heap_hi()) {
      size_t* next_beg = (size_t*)OFFSET(bend,  SIZE_T_SIZE);
      if ((*next_beg & 1) == FREE) {
        printf("consecutive blocks escaped coalescing\n");
        return 0;
      }
    }
  }
  return 1;
}

static int check_valid_address(void* p)
{
  if ((p < blocks) || (p > mem_heap_hi())) {
    printf("pointer doesn't point to the heap region\n");
    printf("\taddress = %p\n", p);
    printf("\theap region = [%p, %p]", blocks, mem_heap_hi());
    return 0;
  }
  return 1;
}

static int check_block_size(size_t i, size_t len) {
  if ((i != nb_components-1 && len > sizes[i]) || (i != 0 && len < sizes[i-1])) {
    printf("block is not in the right list\n");
    printf("\treal block size = %d\n", len);
    size_t pload_threshold = 2*SIZE_T_SIZE;
    pload_threshold += (SIZE_T_SIZE > 2*PTR_T_SIZE)? SIZE_T_SIZE : 2*PTR_T_SIZE;
    size_t min = (i == 0) ? pload_threshold : sizes[i-1];
    size_t max = (i == nb_components-1) ? (unsigned int)(-1) : sizes[i];
    printf("\texpected size range = [%d, %d]\n", min, max);
    return 0;
  }
  return 1;
}

static void* forward_iterations(void* s, size_t i) {
  void* prev = NULL;
  for (void* curr = s; curr != NULL; curr = *(void**)curr) {
    
    void* bbeg = OFFSET(curr, -PTR_T_SIZE - SIZE_T_SIZE);

    if (check_block_size(i, *(size_t*)bbeg) == 0)
      return NULL;
    
    void** to_prev = (void**)OFFSET(curr, -PTR_T_SIZE);
    if (prev != *to_prev) {
      printf("free block doesn't point to previous block in list\n");
      return NULL;
    }
     
    prev = (void*)to_prev;
  }

  return prev;
}

static void* backward_iterations(void* s) {
  void* next = NULL;
  for (void* curr = s; curr != NULL; curr = *(void**)curr) {

    if (check_valid_address(curr) == 0)
      return NULL;

    void** to_next = (void**)OFFSET(curr, PTR_T_SIZE);
    if (next != *to_next) {
      printf("free block doesn't point to next block in list\n");
      return NULL;
    }
 
    next = (void*)to_next;
  }

  return next;
}

static int check_free_lists(void)
{ 
  for (size_t i = 0; i < nb_components; ++i) {
    void* s = linked_components[i];
    void* f = forward_iterations(s, i);
    void* r = backward_iterations(f);
    if ((s != NULL) &&  (s != r))
    {
      printf("iterations do not return to blocks point\n");
      printf("STARTING POINT: %p\n", s);
      printf("RETURN POINT: %p\n", r);
      return 0;
    }
  }
  return 1;
}

static void check_implicit_heap(void)
{
  for (void* p = blocks; p < mem_heap_hi(); p = OFFSET(p, (*(size_t*)p & -2)))
  {
    if (!(check_valid_address(p) && check_bounds(p, NO_MATTER))) {
      printf("address = %p\n", p);
      exit(8);
    }
  }
}

void mm_check()
{
  check_implicit_heap();
  if (heap_type == EXPLICIT) {
    check_free_lists();
  }
}

/* mm_init - initialize the malloc package. */
int mm_init(void)
{
  const size_t nb_pages = 64;
  size_t mps = mem_pagesize();

  if (mem_heapsize() == 0) {
    if (mem_sbrk(mps) == NULL) {
      printf("sbrk cannot adjust heap, initialization failed\n");
      exit(8);
    }
  }
  size_t* lo_heap = (size_t*)mem_heap_lo();
  size_t* hi_heap = (size_t*)OFFSET(mem_heap_hi(), -SIZE_T_SIZE + 1);
  *lo_heap = mem_heapsize();
  *hi_heap = mem_heapsize();
 
  blocks = (void*)lo_heap;
 
  heap_type = IMPLICIT;
  search_policy = FIRST_FIT;

  nb_components = 3;
  sizes = (size_t*)mm_malloc((nb_components-1)*sizeof(size_t));
  linked_components = (void**)mm_malloc(nb_components*sizeof(void*));
 
  blocks = mm_malloc(nb_pages*mps);
  blocks = OFFSET(blocks, -SIZE_T_SIZE);

  for (size_t i = 0; i < nb_components - 1; ++i) {
    sizes[i] = (2 + i)*mps/2;
    linked_components[i] = NULL;
  }
  linked_components[nb_components-1] = NULL;

  heap_type = EXPLICIT;

  free_block(&blocks);
  return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
  size_t new_size;
  void* p;

  if (heap_type == IMPLICIT) {
    new_size = ALIGN(size + 2*SIZE_T_SIZE);
    p = imp_find_block(new_size);
  } else {
    new_size = (size > 2*PTR_T_SIZE) ? size : 2*PTR_T_SIZE;
    new_size = ALIGN(new_size + 2*SIZE_T_SIZE);
    p = exp_find_block(new_size);
  }
  
  if (p == NULL) {
    p = adjust_heap(new_size);
  }
 
  add_block(p, new_size);
  
  return OFFSET(p, SIZE_T_SIZE);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *p)
{
  void* bbeg = OFFSET(p, -SIZE_T_SIZE);

  if ((*(size_t*)bbeg & 1) == 0) {
    printf("double free or corruption\n");
    exit(8);
  }
    
  free_block(&bbeg); 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{/*
  void* newptr;

  if (ptr == NULL) {
    return mm_malloc(size);
  } else {
    if (size == 0) {
      mm_free(ptr);
      return ptr;
    } else {
  
      size_t* bbeg = (size_t*)OFFSET(ptr, -SIZE_T_SIZE);
      size_t oldsize = *bbeg & -2;
      size_t newsize = (size > 2*PTR_T_SIZE) ? size : 2*PTR_T_SIZE;
      newsize = ALIGN(newsize + 2*SIZE_T_SIZE);

      size_t adjusted = oldsize;
      size_t* resid_beg = (size_t*)OFFSET(bbeg, oldsize);
      if ((*resid_beg & 1) == FREE) {
        adjusted += *resid_beg;
        if (adjusted >= newsize) {
          delete_from_queue((void*)resid_beg);
        }
      }

      if (adjusted >= newsize) {

        size_t* bend = (size_t*)OFFSET(bbeg, newsize - SIZE_T_SIZE);
        *bbeg = newsize | 1;
        *bend = newsize | 1;

        size_t pload_threshold = 2*SIZE_T_SIZE;
        pload_threshold += ((heap_type == IMPLICIT) || (SIZE_T_SIZE > 2*PTR_T_SIZE)) ?
          SIZE_T_SIZE : 2*PTR_T_SIZE;

        if (adjusted - newsize >= pload_threshold) {
        
          size_t resid_len = oldsize - newsize;
          size_t* resid_beg = (size_t*)OFFSET(bbeg, newsize);
          size_t* resid_end = (size_t*)OFFSET(bbeg, adjusted - SIZE_T_SIZE);
          *resid_beg = resid_len;
          *resid_end = resid_len;
          add_to_queue((void*)resid_beg);
        }

        return ptr;

      } else {
 
        void* newptr = mm_malloc(size);
        if (newptr == NULL)
          return NULL;

        if (size < oldsize)
          oldsize = size;

        memcpy(newptr, ptr, oldsize);
        mm_free(ptr);
  
        return newptr;
      }
    }
  }*/
 
  void *oldptr = ptr;
  void *newptr;
  size_t copy_size;
    
  newptr = mm_malloc(size);
  if (newptr == NULL)
    return NULL;

  copy_size = *(size_t*)OFFSET(oldptr, -SIZE_T_SIZE);
  if (size < copy_size)
    copy_size = size;

  memcpy(newptr, oldptr, copy_size);
  mm_free(oldptr);
  
  return newptr;
}
