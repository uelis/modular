#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#define STACK_SIZE 1024*1024

int8_t stack[STACK_SIZE];
int stack_top = STACK_SIZE-1;

void
raise_stack_overflow()
{
  fprintf(stderr, "stack overflow\n");
  exit(-1);
}


/*
 * Allocate size bytes from the top of the stack.
 */
__attribute__((always_inline))
void*
stack_alloc(size_t size)
{
  stack_top -= size;
  if (stack_top < 0) {
    raise_stack_overflow();
  }
  return &stack[stack_top];
}

/*
 * Frees the topmost size bytes from the stack and returns
 * a pointer to the data that has thus been popped.
 */
__attribute__((always_inline))
void*
stack_pop(size_t size)
{
  void *data = &stack[stack_top];
  stack_top += size;
  assert ( stack_top < STACK_SIZE );
  return data;
}
