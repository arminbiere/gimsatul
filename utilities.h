#ifndef _utilities_h_INCLUDED
#define _utilities_h_INCLUDED

#include "options.h"
#include "macros.h"

#include <assert.h>
#include <stdlib.h>

static inline double
average (double a, double b)
{
  return b ? a / b : 0;
}

static inline double
percent (double a, double b)
{
  return average (100 * a, b);
}

double nlogn (uint64_t count);
unsigned gcd (unsigned, unsigned);

static inline void
mark_literal (signed char * marks, unsigned lit)
{
  unsigned idx = IDX (lit);
  assert (!marks[idx]);
  marks[idx] = SGN (lit) ? -1 : 1;
}

static inline void
unmark_literal (signed char * marks, unsigned lit)
{
  unsigned idx = IDX (lit);
  assert (marks[idx]);
  marks[idx] = 0;
}

static inline signed char
marked_literal (signed char * marks, unsigned lit)
{
  unsigned idx = IDX (lit);
  signed char res = marks[idx];
  if (SGN (lit))
    res = -res;
  return res;
}

static inline int
export_literal (unsigned * map, unsigned unsigned_lit)
{
  unsigned mapped_lit;
  if (map)
    {
      unsigned unsigned_idx = IDX (unsigned_lit);
      mapped_lit = map[unsigned_idx];
      if (SGN (unsigned_lit))
	mapped_lit = NOT (mapped_lit);
    }
  else
    mapped_lit = unsigned_lit;
  int signed_lit = mapped_lit / 2 + 1;
  if (SGN (mapped_lit))
    signed_lit *= -1;
  return signed_lit;
}

static inline size_t
cache_lines (void *p, void *q)
{
  if (p == q)
    return 0;
  assert (p >= q);
  size_t bytes = (char *) p - (char *) q;
  size_t res = (bytes + (CACHE_LINE_SIZE - 1)) / CACHE_LINE_SIZE;
  return res;
}

#endif
