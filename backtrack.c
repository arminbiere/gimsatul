#include "backtrack.h"
#include "message.h"
#include "ring.h"

static void
unassign (struct ring *ring, unsigned lit)
{
#ifdef LOGGING
  ring->level = VAR (lit)->level;
  LOG ("unassign %s", LOGLIT (lit));
#endif
  unsigned not_lit = NOT (lit);
  signed char *values = ring->values;
  values[lit] = values[not_lit] = 0;
  assert (ring->unassigned < ring->size);
  ring->unassigned++;
  unsigned idx = IDX (lit);
  if (ring->stable)
    {
      struct heap *heap = &ring->heap;
      struct node *node = heap->nodes + idx;
      if (!heap_contains (heap, node))
	push_heap (heap, node);
    }
  else
    {
      struct queue *queue = &ring->queue;
      struct link *link = queue->links + idx;
      update_queue_search (queue, link);
    }
}

void
backtrack (struct ring *ring, unsigned new_level)
{
  assert (ring->level > new_level);
  struct ring_trail *trail = &ring->trail;
  unsigned *t = trail->end;
  while (t != trail->begin)
    {
      unsigned lit = t[-1];
      unsigned lit_level = VAR (lit)->level;
      if (lit_level == new_level)
	break;
      unassign (ring, lit);
      t--;
    }
  trail->end = trail->propagate = t;
  assert (trail->export <= trail->propagate);
  assert (trail->iterate <= trail->propagate);
  ring->level = new_level;
}

void
update_best_and_target_phases (struct ring *ring)
{
  if (!ring->stable)
    return;
  unsigned assigned = SIZE (ring->trail);
  if (ring->target < assigned)
    {
      very_verbose (ring, "updating target assigned to %u", assigned);
      ring->target = assigned;
      signed char *q = ring->values;
      for (all_phases (p))
	{
	  signed char tmp = *q;
	  q += 2;
	  if (tmp)
	    p->target = tmp;
	}
    }
  if (ring->best < assigned)
    {
      very_verbose (ring, "updating best assigned to %u", assigned);
      ring->best = assigned;
      signed char *q = ring->values;
      for (all_phases (p))
	{
	  signed char tmp = *q;
	  q += 2;
	  if (tmp)
	    p->best = tmp;
	}
    }
}
