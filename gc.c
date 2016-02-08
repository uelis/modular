#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#define MEM_SIZE 1024*1024

int from_space[MEM_SIZE];
int to_space[MEM_SIZE];

int next_free;

void init() {
  next_free = 0;
}

/* Allocate size bytes.
   Returns NULL if memory is full.
*/
void* gc_alloc(size_t size) {
  void* chunk = &from_space[next_free];
  next_free += size;
  if (next_free >= MEM_SIZE) {
    chunk = NULL;    
  }
  return chunk;
}

/* Perform garbage collection with the given local roots.
 */
void gc_collect(const void* roots, ...) {
  printf("oom\n");
  exit(-1);
}
