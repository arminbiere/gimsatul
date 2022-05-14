#ifndef _set_h_INCLUDED
#define _set_h_INCLUDED

#include <stdlib.h>

struct set
{
  size_t size;
  size_t deleted;
  size_t allocated;
  void **table;
  struct {
    size_t (*function)(void* state, void* ptr);
    void * state;
  } hash;
};

#define DELETED ((void*) ~(size_t) 0)

void set_insert (struct set *, void *);
void set_remove (struct set *, void *);

#endif
