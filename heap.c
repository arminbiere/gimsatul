#include "heap.h"

#ifdef USE_BINARY_HEAP

static void
bubble_up (struct heap * heap, unsigned idx)
{
  unsigned * stack = heap->stack.begin;
  struct node * nodes = heap->nodes;
  struct node * node = nodes + idx;
  int idx_pos = node->pos;
  double idx_score = node->score;
  while (idx_pos)
    {
      int parent_pos = (idx_pos - 1) / 2;
      unsigned parent_idx = stack[parent_pos];
      struct node * parent = nodes + parent_idx;
      double parent_score = parent->score;
      if (parent_score >= idx_score)
	break;
      stack[idx_pos] = parent_idx;
      parent->pos = idx_pos;
      idx_pos = parent_pos;
    }
  stack[idx_pos] = idx;
  node->pos = idx_pos;
}

static void
bubble_down (struct heap * heap, unsigned idx)
{
  size_t size = SIZE (heap->stack);
  unsigned * stack = heap->stack.begin;
  struct node * nodes = heap->nodes;
  struct node * node = nodes + idx;
  int idx_pos = node->pos;
  double idx_score = node->score;
  for (;;)
    {
      int child_pos = 2 * idx_pos + 1;
      if (child_pos >= size)
	break;
      unsigned child_idx = stack[child_pos];
      struct node * child = nodes + child_idx;
      double child_score = child->score;
      int sibling_pos = child_pos + 1;
      if (sibling_pos < size)
	{
	  unsigned sibling_idx = stack[sibling_pos];
	  struct node * sibling = nodes + sibling_idx;
	  double sibling_score = sibling->score;
	  if (sibling_score > child_score)
	    {
	      child = sibling;
	      child_idx = sibling_idx;
	      child_pos = sibling_pos;
	      child_score = sibling_score;
	    }
	}
      if (child_score <= idx_score)
	break;
      stack[idx_pos] = child_idx;
      child->pos = idx_pos;
      idx_pos = child_pos;
    }
  stack[idx_pos] = idx;
  node->pos = idx_pos;
}


void
push_heap (struct heap * heap, struct node * node)
{
  unsigned size = SIZE (heap->stack);
  assert (node->pos == INVALID_POSITION);
  node->pos = size;
  unsigned idx = node - heap->nodes;
  PUSH (heap->stack, idx);
  bubble_up (heap, idx);
}

void
pop_heap (struct heap * heap, struct node * node)
{
  assert (!EMPTY (heap->stack));
  assert (!node->pos);
  struct node * nodes = heap->nodes;
  unsigned * stack = heap->stack.begin;
  unsigned idx = node - nodes;
  assert (idx == stack[0]);
  node->pos = INVALID_POSITION;
  unsigned last_idx = POP (heap->stack);
  if (last_idx == idx)
    return;
  struct node * last = nodes + last_idx;
  last->pos = 0;
  stack[0] = last_idx;
  bubble_down (heap, last_idx);
}

void
update_heap (struct heap * heap, struct node * node, double new_score)
{
  assert (node->score < new_score);
  node->score = new_score;
  if (node->pos == INVALID_POSITION)
    return;
  unsigned idx = node - heap->nodes;
  bubble_up (heap, idx);
}

#else

static struct node *
merge_nodes (struct node *a, struct node *b)
{
  if (!a)
    return b;
  if (!b)
    return a;
  assert (a != b);
  struct node *parent, *child;
  if (b->score > a->score)
    parent = b, child = a;
  else
    parent = a, child = b;
  struct node *parent_child = parent->child;
  child->next = parent_child;
  if (parent_child)
    parent_child->prev = child;
  child->prev = parent;
  parent->child = child;
  parent->prev = parent->next = 0;

  return parent;
}

static struct node *
collapse_node (struct node *node)
{
  if (!node)
    return 0;

  struct node *next = node, *tail = 0;

  do
    {
      struct node *a = next;
      assert (a);
      struct node *b = a->next;
      if (b)
	{
	  next = b->next;
	  struct node *tmp = merge_nodes (a, b);
	  assert (tmp);
	  tmp->prev = tail;
	  tail = tmp;
	}
      else
	{
	  a->prev = tail;
	  tail = a;
	  break;
	}
    }
  while (next);

  struct node *res = 0;
  while (tail)
    {
      struct node *prev = tail->prev;
      res = merge_nodes (res, tail);
      tail = prev;
    }

  return res;
}

static void
deheap_node (struct node *node)
{
  assert (node);
  struct node *prev = node->prev;
  struct node *next = node->next;
  assert (prev);
  node->prev = 0;
  if (prev->child == node)
    prev->child = next;
  else
    prev->next = next;
  if (next)
    next->prev = prev;
}

void
pop_heap (struct heap *heap, struct node *node)
{
  struct node *root = heap->root;
  struct node *child = node->child;
  if (root == node)
    heap->root = collapse_node (child);
  else
    {
      deheap_node (node);
      struct node *collapsed = collapse_node (child);
      heap->root = merge_nodes (root, collapsed);
    }
  assert (!heap_contains (heap, node));
}

void
push_heap (struct heap *heap, struct node *node)
{
  assert (!heap_contains (heap, node));
  node->child = 0;
  heap->root = merge_nodes (heap->root, node);
  assert (heap_contains (heap, node));
}

void
update_heap (struct heap *heap, struct node *node, double new_score)
{
  double old_score = node->score;
  assert (old_score <= new_score);
  if (old_score == new_score)
    return;
  node->score = new_score;
  struct node *root = heap->root;
  if (root == node)
    return;
  if (!node->prev)
    return;
  deheap_node (node);
  heap->root = merge_nodes (root, node);
}

#endif
