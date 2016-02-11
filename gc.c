#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#define MEM_SIZE 1024*10

static int8_t from_space_mem[MEM_SIZE];
static int8_t to_space_mem[MEM_SIZE];

static int8_t *from_space = from_space_mem;
static int8_t *to_space = to_space_mem;

static int next_free = 0;

void
raise_out_of_memory()
{
  fprintf(stderr, "out of memory\n");
  exit(-1);
}

bool
in_from_space(int8_t *p)
{
  return (from_space <= p) && (p < from_space + MEM_SIZE);
}

bool
in_to_space(int8_t *p)
{
  return (to_space <= p) && (p < to_space + MEM_SIZE);
}

/* 
 *  Record organisation:
 *  +----------------+---------------------+-----+-----------+------+
 *  | tag (64 bits)  | pointer 1 (int8_t*) | ... | pointer n | data |
 *  +----------------+---------------------+-----+-----------+------+
 *
 *  If the last bit of the tag is 1, then it contains the following data:
 *  - higher most 32 bits: record size (including tag)
 *  - next 31 bits: number of pointers, i.e. n
 *  If the last bit of the tag is 0, then it is a forward pointer.
 */

#define TAG(r)       *((int64_t*)r)
#define SIZE(r)      (TAG(r) >> 32)
#define PTR_COUNT(r) ((TAG(r) & 0xFFFFFFFF) >> 1)
#define NO_FWD(r)    (TAG(r) & 0x1)
#define FWD_PTR(r)   *((int8_t**)r)
#define PTR(r, i)    *((int8_t**)((int64_t*)r + 1) + i)

/* 
 * Allocate size bytes.
 * Returns NULL if memory is full.
 */
void*
gc_alloc(size_t size)
{
  int8_t* chunk = from_space + next_free;
  next_free += size;
  if (next_free >= MEM_SIZE) {
    chunk = NULL;
  }
  return chunk;
}

/* 
 * Copy record to address next and replace its tag with a forward pointer.
 * Assumes that record points to from_space and next points to to_space
 */
void
copy_record(void *record, void *next)
{
  assert( in_from_space(record) );
  assert( in_to_space(next) );
  int size = SIZE(record);
  memcpy(next, record, size);
  /* forward pointer */
  TAG(record) = 0; /* make sure the last bit of tag is 0 */
  FWD_PTR(record) = (void*)next;
}

/* 
 * Perform garbage collection with the given local roots.
 * bytes_needed is the number of bytes that are needed after collection.
 * rootc is the number of root arguments that follow.
 * The following arguments must be pointers into from_space.
 */
void
gc_collect(size_t bytes_needed, int64_t rootc, ...)
{

  int8_t *next;
  next = to_space;

  /* copy roots */
  
  va_list roots;
  va_start(roots, rootc);
  for (int i = 0; i < rootc; i++) {
    int8_t *root = va_arg(roots, int8_t*);
    assert( root != NULL && in_from_space(root) );
    int size = SIZE(root);
    copy_record(root, next);
    next += size;
  }
  va_end(roots);

  /* copy reachable */
  
  int8_t *scan;
  scan = to_space;

  while (scan < next) {
    int size = SIZE(scan);
    int ptr_count = PTR_COUNT(scan);

    for (int i = 0; i < ptr_count; i++) {
      int8_t *p = PTR(scan, i);
      if (p != NULL && in_from_space(p)) {

        if (NO_FWD(p)) {
          int p_size = SIZE(p);
          if (!in_to_space(next + p_size))
            raise_out_of_memory();
          copy_record(p, next);
          next += p_size;
        }
        PTR(scan, i) = FWD_PTR(p);
      }
    }
    scan += size;
  }

  next_free = next - to_space;
  if (bytes_needed > MEM_SIZE - next_free)
    raise_out_of_memory();

  void *tmp = from_space;
  from_space = to_space;
  to_space = tmp;
}
