#include "bump.h"
#include "logging.h"
#include "ring.h"

static void
rescale_variable_scores (struct ring *ring)
{
  struct heap *heap = &ring->heap;
  unsigned stable = ring->stable;
  double max_score = heap->increment[stable];
  struct node *nodes = heap->nodes;
  struct node *end = nodes + ring->size;
  for (struct node * node = nodes; node != end; node++)
    if (node->score > max_score)
      max_score = node->score;
  LOG ("rescaling by maximum score of %g", max_score);
  assert (max_score > 0);
  for (struct node * node = nodes; node != end; node++)
    node->score /= max_score;
  heap->increment[stable] /= max_score;
}

void
bump_variable_score (struct ring *ring, unsigned idx)
{
  struct heap *heap = &ring->heap;
  struct node *node = heap->nodes + idx;
  double old_score = node->score;
  double new_score = old_score + heap->increment[ring->stable];
  LOG ("bumping %s old score %g to new score %g",
       LOGVAR (idx), old_score, new_score);
  update_heap (heap, node, new_score);
  if (new_score > MAX_SCORE)
    rescale_variable_scores (ring);
}

static struct node *
first_active_node (struct ring * ring)
{
  struct heap *heap = &ring->heap;
  struct node * nodes = heap->nodes;
  struct node * end = nodes + ring->size;
  struct node * res = nodes;
  bool * active = ring->active;
  while (res != end)
    {
      unsigned idx = res - nodes;
      if (active [idx])
	return res;
      res++;
    }
  return res;
}

static struct node *
next_active_node (struct ring * ring, struct node * node)
{
  struct heap *heap = &ring->heap;
  struct node * nodes = heap->nodes;
  struct node * end = nodes + ring->size;
  assert (nodes <= node);
  assert (node < end);
  struct node * res = node + 1; 
  bool * active = ring->active;
  while (res != end)
    {
      unsigned idx = res - nodes;
      if (active [idx])
	return res;
      res++;
    }
  return res;
}

#define all_active_nodes(NODE) \
  struct node * NODE = first_active_node (ring), \
              * END_ ## NODE = ring->heap.nodes + ring->size; \
  NODE != END_ ## NODE; \
  NODE = next_active_node (ring, NODE)

void
swap_scores (struct ring *ring)
{
  struct heap *heap = &ring->heap;
  struct node * nodes = heap->nodes;
  double *scores = heap->scores;
  for (all_active_nodes (node))
    {
      double tmp = node->score;
      unsigned idx = node - nodes;
      double * s = scores + idx;
      node->score = *s;
      node->child = node->prev = node->next = 0;
      *s = tmp;
    }
  heap->root = 0;
  for (all_active_nodes (node))
    push_heap (heap, node);
  double tmp = heap->increment[0];
  heap->increment[0] = heap->increment[1];
  heap->increment[1] = tmp;
}

void
bump_score_increment (struct ring *ring)
{
  struct heap *heap = &ring->heap;
  unsigned stable = ring->stable;
  double old_increment = heap->increment[stable];
  double factor = stable ? 1.0 / STABLE_DECAY : 1.0 / FOCUSED_DECAY;
  double new_increment = old_increment * factor;
  LOG ("new increment %g", new_increment);
  heap->increment[stable] = new_increment;
  if (heap->increment[stable] > MAX_SCORE)
    rescale_variable_scores (ring);
}

