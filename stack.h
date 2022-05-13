#ifndef _stack_h_INCLUDED
#define _stack_h_INCLUDED

#include "allocate.h"

#define SIZE(STACK) ((size_t)((STACK).end - (STACK).begin))

#define CAPACITY(STACK) ((size_t)((STACK).allocated - (STACK).begin))

#define EMPTY(STACK) ((STACK).end == (STACK).begin)

#define FULL(STACK) ((STACK).end == (STACK).allocated)

#define INIT(STACK) \
do { \
  (STACK).begin = (STACK).end = (STACK).allocated = 0; \
} while (0)

#define RELEASE(STACK) \
do { \
  free ((STACK).begin); \
  INIT (STACK); \
} while (0)

#define ENLARGE(STACK) \
do { \
  size_t OLD_SIZE = SIZE (STACK); \
  size_t OLD_CAPACITY = CAPACITY (STACK); \
  size_t NEW_CAPACITY = OLD_CAPACITY ? 2*OLD_CAPACITY : 1; \
  size_t NEW_BYTES = NEW_CAPACITY * sizeof *(STACK).begin; \
  (STACK).begin = reallocate_block ((STACK).begin, NEW_BYTES); \
  (STACK).end = (STACK).begin + OLD_SIZE; \
  (STACK).allocated = (STACK).begin + NEW_CAPACITY; \
} while (0)

#define PUSH(STACK,ELEM) \
do { \
  if (FULL (STACK)) \
    ENLARGE (STACK); \
  *(STACK).end++ = (ELEM); \
} while (0)

#define SHRINK_STACK(STACK) \
do { \
  size_t OLD_SIZE = SIZE (STACK); \
  if (!OLD_SIZE) \
    { \
      RELEASE (STACK); \
      break; \
    } \
  size_t OLD_CAPACITY = CAPACITY (STACK); \
  if (OLD_CAPACITY == OLD_SIZE) \
    break; \
  size_t NEW_CAPACITY = OLD_SIZE; \
  size_t NEW_BYTES = NEW_CAPACITY * sizeof *(STACK).begin; \
  (STACK).begin = reallocate_block ((STACK).begin, NEW_BYTES); \
  (STACK).end = (STACK).allocated = (STACK).begin + OLD_SIZE; \
} while (0)

#define CLEAR(STACK) \
do { \
  (STACK).end = (STACK).begin; \
} while (0)

#define TOP(STACK) \
  (assert (!EMPTY (STACK)), (STACK).end[-1])

#define POP(STACK) \
  (assert (!EMPTY (STACK)), *--(STACK).end)

struct unsigneds
{
  unsigned *begin, *end, *allocated;
};

struct buffer
{
  unsigned char *begin, *end, *allocated;
};

#endif
