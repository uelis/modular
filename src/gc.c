#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#define MEM_SIZE 1024*1024*100

static int8_t from_space_mem[MEM_SIZE] __attribute__((aligned(4)));
static int8_t to_space_mem[MEM_SIZE] __attribute__((aligned(4)));

int8_t *from_space = from_space_mem;
int8_t *to_space = to_space_mem;

// invariant: divisible by 4 to guarantee alignment
int next_free = 0;

void
raise_out_of_memory()
{
  fprintf(stderr, "out of memory\n");
  exit(-1);
}

static inline
bool
in_from_space(int8_t *p)
{
  return (from_space <= p) && (p < from_space + MEM_SIZE);
}

static inline
bool
in_to_space(int8_t *p)
{
  return (to_space <= p) && (p < to_space + MEM_SIZE);
}

/*
 *  Record organisation:
 *  +----------------+-----------+-----+-----------+------+
 *  | tag (64 bits)  | pointer 1 | ... | pointer n | data |
 *  +----------------+-----------+-----+-----------+------+
 *
 *  If the least significant bit of the tag is 1, then it 
 *  contains the following data:
 *  - highermost 32 bits: record size (including tag)
 *  - next 31 bits: number of pointers, i.e. n
 *  If the last bit of the tag is 0, then it is a forward pointer.
 */

typedef uint64_t tag_t;

static inline
tag_t
get_tag(int8_t *record) {
  tag_t tag;
  memcpy(&tag, record, sizeof(tag));
  return tag;
}

static inline
void
set_tag(int8_t *record, tag_t tag) {
  assert (tag != 0);
  memcpy(record, &tag, sizeof(tag));
}

static inline
int8_t*
get_pointer(int8_t *record, int i) {
  int8_t *res;
  int8_t *pi = record + sizeof(tag_t) + i * sizeof(int8_t*);
  memcpy(&res, pi, sizeof(res));
  return res;
}

static inline
void
set_pointer(int8_t *record, int i, int8_t *ptr) {
  int8_t *pi = record + sizeof(tag_t) + i * sizeof(int8_t*);
  memcpy(pi, &ptr, sizeof(ptr));
}

static inline
uint64_t
tag_size(tag_t tag) {
  return tag >> 32;
}

static inline
uint64_t
tag_pointer_count(tag_t tag) {
  return (tag & 0xFFFFFFFF) >> 1;
}

static inline
bool
tag_is_fwd_pointer(tag_t tag) {
  return !(tag & 0x1);
}

static inline
bool
is_aligned(void *x) {
  return ((uint64_t)x & 0x03) == 0;
}

static inline
int
add_align(int x) {
  return (x + 0x07) & ~0x07;
}

static
void
print_from_space()
{
  int8_t *scan;
  scan = from_space;

  while (scan < from_space + next_free) {
    tag_t tag = get_tag(scan);
    uint64_t size = tag_size(tag);
    uint64_t ptr_count = tag_pointer_count(tag);
    assert ( !tag_is_fwd_pointer(tag) );
    printf(" [ %" PRId64 ", %" PRId64 "] ", size, ptr_count);
    scan += add_align(size);
    assert ( is_aligned(scan) );
  }
  printf("\n");
}

/*
 * Allocate size bytes.
 * Returns NULL if memory is full.
 */
__attribute__((always_inline))
int8_t*
gc_alloc(size_t size)
{
  if (next_free + add_align(size) >= MEM_SIZE) {
    return NULL;
  }
  int8_t *chunk = from_space + next_free;
  next_free += add_align(size);  
  return chunk;
}

/*
 * Copy record to address next and replace its tag with a forward pointer.
 * Assumes that record points to from_space and next points to to_space
 */
static void
copy_record(int8_t *record, int8_t *next)
{
  assert( in_from_space(record) );
  assert( in_to_space(next) );
  tag_t tag = get_tag(record);
  uint64_t size = tag_size(tag);
  memcpy(next, record, size);
  /* forward pointer */
  assert( is_aligned(next) );
  tag_t fwd = (uint64_t)next;
  set_tag(record, fwd);
}

/*
 * Perform garbage collection with the given local roots.
 * bytes_needed is the number of bytes that are needed after collection.
 * rootc is the number of root arguments that follow.
 * The following arguments must be pointers into from_space.
 */
void
gc_collect(size_t bytes_needed, uint64_t rootc, ...)
{

  int8_t *next;
  next = to_space;

  /* copy roots */

  va_list roots;
  va_start(roots, rootc);
  for (int i = 0; i < rootc; i++) {
    int8_t *root = va_arg(roots, int8_t*);
    if (root != NULL) {
      assert( is_aligned(root) );
      assert( in_from_space(root) );
      tag_t tag = get_tag(root);
      copy_record(root, next);
      next += add_align(tag_size(tag));
    }
  }
  va_end(roots);

  /* copy reachable */

  int8_t *scan;
  scan = to_space;

  while (scan < next) {
    tag_t tag = get_tag(scan);
    uint64_t ptr_count = tag_pointer_count(tag);

    for (int i = 0; i < ptr_count; i++) {
      int8_t *p = get_pointer(scan, i);
      if (p != NULL && in_from_space(p)) {
        tag_t tag_p = get_tag(p);

        if (!tag_is_fwd_pointer(tag_p)) {
          uint64_t p_size = tag_size(tag_p);
          if (!in_to_space(next + add_align(p_size)))
            raise_out_of_memory();
          copy_record(p, next);
          next += add_align(p_size);
          assert ( is_aligned(next) );
          tag_p = get_tag(p);
          // after copy_record tag_p must be fwd pointer
        }
        set_pointer(scan, i, (int8_t*)tag_p);
      }
    }
    scan += add_align(tag_size(tag));
    assert ( is_aligned(scan) );
  }

  next_free = next - to_space;
  if (bytes_needed > MEM_SIZE - next_free)
    raise_out_of_memory();

  int8_t *tmp = from_space;
  from_space = to_space;
  to_space = tmp;
}

