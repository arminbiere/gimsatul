#include "assign.h"
#include "decide.h"
#include "macros.h"
#include "options.h"
#include "random.h"
#include "ring.h"
#include "utilities.h"

signed char
initial_phase (struct ring *ring)
{
  return ring->options.phase ? 1 : -1;
}

static signed char
decide_phase (struct ring *ring, struct variable *v)
{
  signed char phase = 0;
  if (ring->stable)
    phase = v->target;
  if (!phase)
    phase = v->saved;
  if (!phase)
    phase = initial_phase (ring);
  return phase;
}

static unsigned
random_decision (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  bool *active = ring->active;
  unsigned size = ring->size;

  unsigned idx = random_modulo (&ring->random, size);
  unsigned lit = LIT (idx);

  if (!active[idx] || values[lit])
    {
      unsigned delta = random_modulo (&ring->random, size);
      while (gcd (delta, size) != 1)
	if (++delta == size)
	  delta = 1;
      assert (delta < size);
      do
	{
	  idx += delta;
	  if (idx >= size)
	    idx -= size;
	  lit = LIT (idx);
	}
      while (!active[idx] || values[lit]);
    }

  LOG ("random decision %s", LOGVAR (idx));

  return idx;
}

static unsigned
best_decision_on_heap (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  struct heap *heap = &ring->heap;
  struct node *nodes = heap->nodes;

  assert (heap->root);

  unsigned idx;
  for (;;)
    {
      struct node *ruler = heap->root;
      assert (ruler);
      assert (ruler - nodes < ring->size);
      idx = ruler - nodes;
      unsigned lit = LIT (idx);
      if (!values[lit])
	break;
      pop_heap (heap, ruler);
    }

  LOG ("best decision %s on heap with score %g",
       LOGVAR (idx), nodes[idx].score);

  return idx;
}

static unsigned
best_decision_on_queue (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  struct queue *queue = &ring->queue;
  struct link *links = queue->links;
  struct link *search = queue->search;

  unsigned lit, idx;
  for (;;)
    {
      assert (search);
      idx = search - links;
      lit = LIT (idx);
      if (!values[lit])
	break;
      search = search->prev;
    }
  queue->search = search;

  LOG ("best decision %s on queue with stamp %" PRIu64,
       LOGVAR (idx), search->stamp);
  return idx;
}

void
decide (struct ring *ring)
{
  struct context *context = ring->statistics.contexts;
  context += ring->context;
  uint64_t decisions = context->decisions++;

  unsigned idx;
  if (ring->id && decisions < ring->options.random_decisions)
    idx = random_decision (ring);
  else if (ring->stable)
    idx = best_decision_on_heap (ring);
  else
    idx = best_decision_on_queue (ring);

  struct variable *v = ring->variables + idx;
  signed char phase = decide_phase (ring, v);
  unsigned lit = LIT (idx);
  if (phase < 0)
    lit = NOT (lit);

  ring->level++;
  assign_decision (ring, lit);
}
