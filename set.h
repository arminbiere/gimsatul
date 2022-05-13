#ifndef _set_h_INCLUDED
#define _set_h_INCLUDED

#include <stdlib.h>

struct set
{
  size_t size;
  size_t deleted;
  size_t allocated;
  void **table;
};

#endif

