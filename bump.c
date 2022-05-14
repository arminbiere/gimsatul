#include "bump.h"
#include "logging.h"
#include "ring.h"

#include <string.h>

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
bump_variable_on_heap (struct ring * ring, unsigned idx)
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

static void
bump_variable_on_queue (struct ring * ring, unsigned idx)
{
  struct queue *queue = &ring->queue;
  struct link *link = queue->links + idx;
#ifdef LOGGING
  uint64_t old_stamp = link->stamp;
#endif
  dequeue (queue, link);
  unsigned lit = LIT (idx);
  bool unassigned = !ring->values[lit];
  enqueue (queue, link, unassigned);
#ifdef LOGGING
  uint64_t new_stamp = link->stamp;
  LOG ("bumping %s old stamp %" PRIu64 " new stamp %" PRIu64,
       LOGVAR (idx), old_stamp, new_stamp);
#endif
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
rebuild_heap (struct ring *ring)
{
  struct heap *heap = &ring->heap;
  struct node * nodes = heap->nodes;
  memset (nodes, 0, ring->size * sizeof *nodes);
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
  if (!ring->stable)
    return;
  struct heap *heap = &ring->heap;
  unsigned stable = ring->stable;
  double old_increment = heap->increment[stable];
  double factor = 1.0 / DECAY;
  double new_increment = old_increment * factor;
  LOG ("new increment %g", new_increment);
  heap->increment[stable] = new_increment;
  if (heap->increment[stable] > MAX_SCORE)
    rescale_variable_scores (ring);
}

static void
sort_analyzed_variable_according_to_stamp (struct ring * ring)
{
  struct link * links = ring->queue.links;
  struct unsigneds * analyzed = &ring->analyzed;
  size_t size = SIZE (*analyzed), count[256];
  unsigned * begin = analyzed->begin;
  unsigned * tmp = allocate_array (size, sizeof *tmp);
  for (size_t i = 0; i != 64; i += 8)
    {
      memset (count, 0, sizeof count);
      for (unsigned * p = begin, * end = p + size; p != end; p++)
        count[(links[*p].stamp >> i) & 255]++;
      size_t pos = 0, delta;
      for (size_t j = 0; j != 256; j++)
	delta = count[j], count[j] = pos, pos += delta;
      assert (pos == size);
      for (unsigned * p = begin, * end = p + size; p != end; p++)
	tmp[count[(links[*p].stamp >> i) & 255]++] = *p;
      SWAP (tmp, begin);
    }
#ifndef NDEBUG
  assert (begin == analyzed->begin);
  assert (tmp != begin);
  for (size_t i = 0; i + 1 < size; i++)
    assert (links[begin[i]].stamp < links[begin[i + 1]].stamp);
#endif
  free (tmp);
}

static void
bump_analyze_variables_on_queue (struct ring * ring)
{
  for (all_elements_on_stack (unsigned, idx, ring->analyzed))
    bump_variable_on_queue (ring, idx);
}

void
sort_and_bump_analyzed_variables_on_queue (struct ring * ring)
{
  sort_analyzed_variable_according_to_stamp (ring);
  bump_analyze_variables_on_queue (ring);
}
