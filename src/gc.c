#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#define MEM_SIZE 1024*1024

static char from_space_mem[MEM_SIZE];
static char to_space_mem[MEM_SIZE];

char *from_space = from_space_mem;
char *to_space = to_space_mem;

int next_free = 0;

void
raise_out_of_memory()
{
  fprintf(stderr, "out of memory\n");
  exit(-1);
}

static inline
bool
in_from_space(char *p)
{
  return (from_space <= p) && (p < from_space + MEM_SIZE);
}

static inline
bool
in_to_space(char *p)
{
  return (to_space <= p) && (p < to_space + MEM_SIZE);
}

/*
 *  Record organisation:
 *  +----------------+-----------+-----+-----------+------+
 *  | tag (64 bits)  | pointer 1 | ... | pointer n | data |
 *  +----------------+-----------+-----+-----------+------+
 *
 *  If the last bit of the tag is 1, then it contains the following data:
 *  - highermost 32 bits: record size (including tag)
 *  - next 31 bits: number of pointers, i.e. n
 *  If the last bit of the tag is 0, then it is a forward pointer.
 */

typedef union {
  uint64_t as_uint64;
  char *as_forward_pointer;
} tag_t;

static inline
tag_t
get_tag(char *record) {
  tag_t tag;
  memcpy(&tag, record, sizeof(tag_t));
  return tag;
}

static inline
void
set_tag(char *record, tag_t tag) {
  memcpy(record, &tag, sizeof(tag_t));
}

static inline
void*
get_pointer(char *record, int i) {
  void *res;
  char *pi = record + sizeof(tag_t) + i * sizeof(char*);
  memcpy(&res, pi, sizeof(char*));
  return res;
}

static inline
void
set_pointer(char *record, int i, void *ptr) {
  char *pi = record + sizeof(tag_t) + i * sizeof(char*);
  memcpy(pi, &ptr, sizeof(char*));
}

static inline
uint64_t
tag_size(tag_t tag) {
  return tag.as_uint64 >> 32;
}

static inline
uint64_t
tag_pointer_count(tag_t tag) {
  return (tag.as_uint64 & 0xFFFFFFFF) >> 1;
}

static inline
bool
tag_is_fwd_pointer(tag_t tag) {
  return !(tag.as_uint64 & 0x1);
}

/*
 * Allocate size bytes.
 * Returns NULL if memory is full.
 */
__attribute__((always_inline))
char*
gc_alloc(size_t size)
{
  char *chunk = from_space + next_free;
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
static void
copy_record(char *record, char *next)
{
  assert( in_from_space(record) );
  assert( in_to_space(next) );
  tag_t tag = get_tag(record);
  uint64_t size = tag_size(tag);
  memcpy(next, record, size);
  /* forward pointer */
  tag_t fwd = { .as_forward_pointer = next };
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

  char *next;
  next = to_space;

  /* copy roots */

  va_list roots;
  va_start(roots, rootc);
  for (int i = 0; i < rootc; i++) {
    void *root = va_arg(roots, void*);
    assert( root != NULL && in_from_space(root) );
    tag_t tag = get_tag(root);
    copy_record(root, next);
    next += tag_size(tag);
  }
  va_end(roots);

  /* copy reachable */

  char *scan;
  scan = to_space;

  while (scan < next) {
    tag_t tag = get_tag(scan);
    uint64_t ptr_count = tag_pointer_count(tag);

    for (int i = 0; i < ptr_count; i++) {
      void *p = get_pointer(scan, i);
      if (p != NULL && in_from_space(p)) {
        tag_t tag_p = get_tag(p);

        if (!tag_is_fwd_pointer(tag_p)) {
          uint64_t p_size = tag_size(tag_p);
          if (!in_to_space(next + p_size))
            raise_out_of_memory();
          copy_record(p, next);
          next += p_size;
          tag_p = get_tag(p);
        }
        set_pointer(scan, i, tag_p.as_forward_pointer);
      }
    }
    scan += tag_size(tag);
  }

  next_free = next - to_space;
  if (bytes_needed > MEM_SIZE - next_free)
    raise_out_of_memory();

  char *tmp = from_space;
  from_space = to_space;
  to_space = tmp;
}
