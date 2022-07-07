#ifndef _heap_h_INCLUDED
#define _heap_h_INCLUDED

#define USE_BINARY_HEAP

#ifdef USE_BINARY_HEAP
#include "stack.h"

#include <limits.h>
#define INVALID_POSITION -1
#endif

#include <assert.h>
#include <stdbool.h>

struct node
{
  double score;
#ifdef USE_BINARY_HEAP 
  int pos;
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
  return node->pos >= 0;
#else
  return heap->root == node || node->prev;
#endif
}

#endif
