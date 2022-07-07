#ifndef _heap_h_INCLUDED
#define _heap_h_INCLUDED

#define USE_BINARY_HEAP

#ifdef USE_BINARY_HEAP
#include "stack.h"
#endif

#include <assert.h>
#include <stdbool.h>

struct node
{
  double score;
#ifdef USE_BINARY_HEAP 
  size_t pos;
#else
  struct node *child, *prev, *next;
#endif
};

struct heap
{
  double increment;
  struct node *nodes;
#ifdef USE_BINARY_HEAP
  struct unsigneds stack;
#else
  struct node *root;
#endif
};

/*------------------------------------------------------------------------*/

void pop_heap (struct heap *, struct node *);
void push_heap (struct heap *, struct node *node);
void update_heap (struct heap *, struct node *, double new_score);

/*------------------------------------------------------------------------*/

static inline bool
heap_contains (struct heap *heap, struct node *node)
{
#ifdef USE_BINARY_HEAP
  return node->pos;
#else
  return heap->root == node || node->prev;
#endif
}

#endif
