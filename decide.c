#include "assign.h"
#include "decide.h"
#include "macros.h"
#include "options.h"
#include "random.h"
#include "ring.h"

static signed char
decide_phase (struct ring *ring, struct variable *v)
{
  signed char phase = 0;
  if (ring->stable)
    phase = v->target;
  if (!phase)
    phase = v->saved;
  if (!phase)
    phase = INITIAL_PHASE;
  return phase;
}

static unsigned
gcd (unsigned a, unsigned b)
{
  while (b)
    {
      unsigned r = a % b;
      a = b, b = r;
    }
  return a;
}

static unsigned
random_decision (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  bool * active = ring->active;
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
best_score_decision (struct ring *ring)
{
  assert (ring->unassigned);

  signed char *values = ring->values;
  struct heap *heap = &ring->heap;
  struct node *nodes = heap->nodes;

  assert (heap->root);

  unsigned lit, idx;
  for (;;)
    {
      struct node *ruler = heap->root;
      assert (ruler);
      assert (ruler - nodes < ring->size);
      idx = ruler - nodes;
      lit = LIT (idx);
      if (!values[lit])
	break;
      pop_heap (heap, ruler);
    }
  assert (idx < ring->size);

  LOG ("best score decision %s score %g", LOGVAR (idx), nodes[idx].score);

  return idx;
}

void
decide (struct ring *ring)
{
  struct context *context = ring->statistics.contexts;
  context += ring->context;
  uint64_t decisions = context->decisions++;

  unsigned idx;
  if (ring->id && decisions < RANDOM_DECISIONS)
    idx = random_decision (ring);
  else
    idx = best_score_decision (ring);

  struct variable *v = ring->variables + idx;
  signed char phase = decide_phase (ring, v);
  unsigned lit = LIT (idx);
  if (phase < 0)
    lit = NOT (lit);

  ring->level++;
  assign_decision (ring, lit);
}
