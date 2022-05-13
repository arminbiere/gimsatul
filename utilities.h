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

static inline int
export_literal (unsigned unsigned_lit)
{
  int signed_lit = unsigned_lit / 2 + 1;
  if (SGN (unsigned_lit))
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
