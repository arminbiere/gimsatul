#ifndef _clause_h_INCLUDED
#define _clause_h_INCLUDED

#include <stdatomic.h>
#include <stdbool.h>

#ifdef LOGGING
#include <stdint.h>
#endif

struct clause
{
#ifdef LOGGING
  uint64_t id;
#endif
  atomic_ushort shared;
  unsigned char glue;
  bool dirty:1;
  bool garbage:1;
  bool redundant:1;
  bool subsume:1;
  unsigned size;
  unsigned literals[];
};

struct clauses
{
  struct clause **begin, **end, **allocated;
};

#endif
