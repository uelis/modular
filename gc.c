#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <string.h>

#define MEM_SIZE 1024*10

int8_t from_space_mem[MEM_SIZE];
int8_t to_space_mem[MEM_SIZE];
int8_t* from_space = (int8_t*)&from_space_mem;
int8_t* to_space = (int8_t*)&to_space_mem;

int next_free;

void init() {
  next_free = 0;
}

/* Allocate size bytes.
   Returns NULL if memory is full.
*/
void* gc_alloc(size_t size) {
  int8_t* chunk = from_space + next_free;
  next_free += size;
  if (next_free >= MEM_SIZE) {
    chunk = NULL;    
  }
  // fprintf(stderr, "chunk: %p\n", chunk);  
  return chunk;
}

#define TAG(r) (*((int64_t*)r))
#define SIZE(r) ((TAG(r) >> 32))
#define PTR_COUNT(r) ((TAG(r)& 0xFFFFFFFF) >> 1)
#define NO_FWD(r) (TAG(r) & 0x1)
#define FWD_PTR(r) *((void**)r)
#define PTR(r, i) ((void**)((int64_t*)r + 1) + i)

void* copy_record(void* r, int8_t* next) {
  int size = SIZE(r);
  memcpy((void*)next, (void*)r, size);
  void* copy = (void*)next;
  // forward pointer
  FWD_PTR(r) = (void*)copy;
  return copy;
}

/* Perform garbage collection with the given local roots.
 */
void gc_collect(int64_t rootc, ...) {
  int8_t* next;
  next = to_space;
  
  va_list roots;
  va_start(roots, rootc);
  for (int i = 0; i < rootc; i++) {
    void* root = va_arg(roots, void*);

    int size = SIZE(root);
    int ptr_count = PTR_COUNT(root);
    /*
    printf("%p (%i, %i)\n", root, size, ptr_count);
    for (int i = 0; i < ptr_count; i++) {
      printf("- p: %p\n", *PTR(root, i));
    }
    */
    copy_record(root, next);
    next += size;
  }
  va_end(roots);
    
  int8_t* scan;
  scan = to_space;

  while (scan < next) {
    void* r = (void*)scan;
    int size = SIZE(r);
    int ptr_count = PTR_COUNT(r);
    //    printf("%i\n", (int)(next - to_space));

    for (int i = 0; i < ptr_count; i++) {
      void* p = *PTR(r, i);
      if (p != NULL && (void*)from_space <= p && p < (void*)from_space + MEM_SIZE) {

        if (NO_FWD(p)) {
          int p_size = SIZE(p);
          if (next + p_size >= to_space + MEM_SIZE) {
            printf("oom\n");
            exit(-1);
          }
          copy_record(p, next);
          next += p_size;
        } 
        *PTR(r, i) = FWD_PTR(p);
      }
    }
    scan += size;
  }

  next_free = next - to_space;
  fprintf(stderr, "Collection finished: %i free\n", MEM_SIZE - next_free);
  void *tmp = from_space;
  from_space = to_space;
  to_space = tmp;
}
