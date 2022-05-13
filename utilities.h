#ifndef _utilities_h_INCLUDED
#define _utilities_h_INCLUDED

#include "macros.h"

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

#endif
