//Note to TA:  Makefile conflict: there is no flag such as -Weverything on my computer please use -Wall instead of it. THank you. 

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/queue.h>
#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;
static value_t heap_start_v = 0;
static value_t heap_end_v = 0;
static value_t* heap_first_block = NULL;
static value_t tot_heap_size = 0 ;

#define FREE_LISTS_COUNT 32

static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1


// Header management
static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

TAILQ_HEAD(tailhead, entry) head;
int lastUsed = FREE_LISTS_COUNT -1;

struct entry {
  value_t * val;
  TAILQ_ENTRY(entry) entries;
};

typedef struct sObject {
  /* The next object in the linked list of heap allocated objects. */
  struct sObject* next;
  struct sObject* prev;

  union {
    /* OBJ_VALUE* */
    value_t * value;
    unsigned int size;
  };
} Object;


typedef struct coalescer {

  Object * obj;
  union {
    /* OBJ_VALUE* */
    value_t* value;
  };
} coalesce;




// my defined functions
void attemptCoalescing();
void performCoalescing(coalesce large, coalesce small);

typedef struct {
  Object* allocatedObjects;
  Object* freedObjects;
  /* The total number of currently allocated objects. */
  int numAllocatedObjects;
  int numFreeObjects;
} VM;

VM* newVM() {
  VM* vm = malloc(sizeof(VM));
  vm->allocatedObjects = NULL;
  vm->freedObjects = NULL;
  vm->numAllocatedObjects = 0;
  vm->numFreeObjects = 0;
  return vm;
}

VM * vm;


void add_to_stack(value_t * element) {
  struct entry *elem;
  elem = malloc(sizeof(struct entry));
  if (elem) {
    elem->val = element;
  }
  TAILQ_INSERT_HEAD(&head, elem, entries);
}

value_t * remove_head()
{
  struct entry *elem;
  elem = head.tqh_first;
  if(elem == NULL)
    return NULL;
  TAILQ_REMOVE(&head, head.tqh_first, entries);
  value_t * extracted = elem->val;
  free(elem);
  return extracted;
}

Object* newAllocatedObject(value_t* val) {

  Object* object = malloc(sizeof(Object));
  object->next = vm->allocatedObjects;
  if(vm->allocatedObjects != NULL)
    vm->allocatedObjects->prev = object;
  object->value = val;
  vm->allocatedObjects = object;
  vm->allocatedObjects->prev = NULL;
  vm->numAllocatedObjects++;
  return object;
}

Object* newFreeObject(value_t* val) {
  Object* object = malloc(sizeof(Object));
  object->next = vm->freedObjects;
  if(vm->freedObjects != NULL)
    vm->freedObjects->prev = object;
  object->value = val;
  vm->freedObjects = object;
  vm->freedObjects->prev = NULL;
  vm->numFreeObjects++;
  return object;
}
// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}


// Bitmap management

static int bitmap_is_bit_set(value_t* ptr) {

  ptr = addr_v_to_p(ptr);

  if (!(heap_start <= ptr && ptr < heap_end))
      return 0;

  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0;
}

static void bitmap_set_bit(value_t* ptr) {

  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}

static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

void memory_setup(size_t total_byte_size) {
  memory_start = malloc(total_byte_size);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
  vm = newVM();
}


void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
  Object * curr = vm->allocatedObjects;
  Object * next_point;
  while (curr != NULL) { 
    next_point = curr->next;          
    free(curr);
    curr = next_point;               
  }
  curr = vm->freedObjects;
   while (curr != NULL) { 
    next_point = curr->next;          
    free(curr);  
    curr = next_point;       
  }
  free(vm);
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t);

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);

  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);

  tot_heap_size = heap_end - heap_start;
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;

  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l)
    free_list_heads[l] = memory_start;
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;
}

static value_t* allocate(tag_t tag, value_t size) {
  assert(0 <= size);
  assert(heap_first_block != NULL);
  if (heap_first_block + size + HEADER_SIZE >= heap_end) {
    Object** object = &vm->freedObjects;
    int total_size_available = 0;
    value_t * this_block;
    int counter = 0;
    int before_loop_start_num_freed = vm->numFreeObjects;
    while (*object) {

      Object* traversal = *object;
      this_block = traversal->value;
      value_t curr_size =  header_unpack_size(this_block[-1]);  
      total_size_available += curr_size;
      if(curr_size >= size)
      {
        this_block[-1] = header_pack(tag, size);
        bitmap_set_bit(this_block);
        newAllocatedObject(this_block);
        value_t a;
        for(a = 0; a < curr_size ; a++)
          this_block[a] = 0;
        //printf("Available at %08x with size %d whose next is %08x num %d \n", this_block, curr_size, traversal->next->value, vm->numFreeObjects);
        if(traversal->prev!=NULL)
        {
          //printf("Not first on list \n");
          traversal->prev->next = traversal->next;
          if(traversal->next != NULL)
            traversal->next->prev = traversal->prev;
        }
        else
        {
          //printf("First on list \n");
          vm->freedObjects = traversal->next;
          if(traversal->next != NULL)
            traversal->next->prev = NULL;
        }
        vm->numFreeObjects--;
        //printf("Available at %08x with size %d whose next is %08x num %d \n", this_block, curr_size, traversal->next->value, vm->numFreeObjects);
        
        //printf("Virtual address is %16x \n", addr_v_to_p(this_block));
        //printf("-----\n ");
        return this_block;
      }
      counter++;
      object = &(*object)->next; 
    }
    return NULL;
  }

  value_t * this_block = heap_first_block;
  this_block[-1] = header_pack(tag, size);
  heap_first_block = this_block + size + HEADER_SIZE;
  bitmap_set_bit(heap_first_block);
  newAllocatedObject(this_block);
  return this_block;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}



static void mark(value_t* block) {
  // TODO
  //printf("Treied this \n");
  value_t *aux;
  int a= 0;
  TAILQ_INIT(&head);
  value_t* ext = block;
  unsigned int size;

  while(ext != NULL)
  {
    size = header_unpack_size(ext[-1]);
    int i;
    for (i = 0; i < size; i++) {
      //printf("Starting for loop \n");
        if (bitmap_is_bit_set(ext[i])) {
              aux = addr_v_to_p(ext[i]);

              assert(aux >= heap_start && aux < heap_end );

              bitmap_clear_bit(aux);

              add_to_stack(aux);
            }
     }
     //printf("Right here! \n");
     ext = remove_head();
     //printf("Before this \n");
  }
}

static void sweep() {
  //printf("Treied to sweep \n");
  Object** object = &vm->allocatedObjects;
  while (*object) {
    Object* traversal = *object;
    
     if (bitmap_is_bit_set(addr_p_to_v(traversal->value))) {
     //   /* This object wasn't reached, so remove it from the list and free it. */
         // printf("Ready to free %d : \n", traversal->value);
          Object* unreached = *object;
          *object = unreached->next;

          value_t curr_size =  header_unpack_size(unreached->value[-1]);
          bitmap_clear_bit(traversal->value);
          value_t a;
          newFreeObject(unreached->value);
          vm->numAllocatedObjects--;
         //printf("Num allocated objects %d free objects %d \n", vm->numAllocatedObjects, vm->numFreeObjects);
    } else {
    //   /* This object was reached, so unmark it (for the next GC) and move on to
    //    the next. */
         //printf("Allocated %d \n", traversal->value);
         bitmap_set_bit(traversal->value);
         object = &(*object)->next;
     }

     attemptCoalescing();
  }
}


unsigned int sort_fn_ascend(const coalesce *ptr1, const coalesce *ptr2)
{
   value_t * a = (coalesce*)(ptr1)->value;
   value_t * b = (coalesce*)(ptr2)->value;
   return a - b;
}


void attemptCoalescing()
{
    Object** object = &vm->freedObjects;
    Object*  tmpptr = *object;
    coalesce newitems[vm->numFreeObjects];
    int i = 0;
    while(tmpptr != NULL)
    {
        newitems[i].value = tmpptr->value;
        newitems[i].obj = tmpptr;
        tmpptr = tmpptr->next;
        i++;
    }
    assert(i == vm->numFreeObjects);
    // tmpptr = *object;
    // //printf("Prior to sort \n");
    // qsort(newitems , vm->numFreeObjects , sizeof(coalesce), sort_fn_ascend);
    // //printf("Post sort \n");
    // int a =0;
    // int curr = 0;
    // int firstPos = 0;
    // while(a < vm->numFreeObjects)
    // {
    //   curr = a;
    //   value_t curr_size =  header_unpack_size(newitems[curr].value[-1]);
    //   //printf("newitems %u curr_size %u next item %u \n", newitems[curr].value, curr_size, newitems[a+1].value);
    //   if(a + 1 < vm->numFreeObjects && newitems[curr].value + curr_size == newitems[a+1].value)
    //   {
    //      performCoalescing(newitems[curr], newitems[a+1]);
    //   }
    //   a = a+1;
    // }
    return;
}

void performCoalescing(coalesce large, coalesce small)
{
  //printf("Asking to coalesce \n");

  value_t large_size = header_unpack_size(large.value);
  value_t small_size = header_unpack_size(small.value);

  printf("Coalesce large was %d small was %d \n", large.value, small.value);
  // printf("Came here large size %d small size %d \n", large_size, small_size);
  // // decouple small
  // // if(small.obj->prev != NULL)
  // //   small.obj->prev->next = small.obj->next;
  // // printf("Next failed; \n");
  // // if(small.obj->next != NULL)
  // //   small.obj->next->prev = small.obj->prev;

  // // printf("Now here \n");
  // free(small.obj);
  // // coalesce into large
  // large.obj->value[-1] = header_pack(tag_None, large_size + small_size);
}

value_t* memory_allocate(tag_t tag, value_t size) {
  value_t* first_try = allocate(tag, size);
  if (first_try != NULL)
    return first_try;

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  value_t* second_try = allocate(tag, size);
  if (second_try != NULL)
    return second_try;

  fail("cannot allocate %d words of memory, even after GC");
}

#endif
