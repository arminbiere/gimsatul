#include "assign.h"
#include "macros.h"
#include "ruler.h"
#include "trace.h"

static void
assign (struct ring *ring, unsigned lit, struct watch *reason)
{
  const unsigned not_lit = NOT (lit);
  unsigned idx = IDX (lit);

  assert (idx < ring->size);
  assert (!ring->values[lit]);
  assert (!ring->values[not_lit]);
  assert (ring->active[idx]);

  assert (ring->unassigned);
  ring->unassigned--;

  ring->values[lit] = 1;
  ring->values[not_lit] = -1;

  unsigned level = ring->level;
  struct variable *v = ring->variables + idx;
  v->saved = SGN (lit) ? -1 : 1;
  v->level = level;
  if (!level)
    {
      if (reason)
	trace_add_unit (&ring->trace, lit);
      v->reason = 0;
      ring->statistics.fixed++;
      if (!ring->pool)
	{
	  struct ruler * ruler = ring->ruler;
	  ruler->statistics.fixed.solving++;
	  ruler->statistics.fixed.total++;
	  assert (ruler->statistics.active);
	  ruler->statistics.active--;
	}
      assert (ring->statistics.active);
      ring->statistics.active--;
      assert (ring->active[idx]);
      ring->active[idx] = false;
    }
  else
    v->reason = reason;

  struct ring_trail *trail = &ring->trail;
  size_t pos = trail->end - trail->begin;
  assert (pos < ring->size);
  trail->pos[idx] = pos;
  *trail->end++ = lit;
}

void
assign_with_reason (struct ring *ring, unsigned lit, struct watch *reason)
{
  assert (reason);
  assign (ring, lit, reason);
  LOGWATCH (reason, "assign %s with reason", LOGLIT (lit));
}

void
assign_ring_unit (struct ring *ring, unsigned unit)
{
  assert (!ring->level);
  assign (ring, unit, 0);
  LOG ("assign %s unit", LOGLIT (unit));
}

void
assign_decision (struct ring *ring, unsigned decision)
{
  assert (ring->level);
  assign (ring, decision, 0);
  LOG ("assign %s decision score %g",
       LOGLIT (decision), ring->queue.nodes[IDX (decision)].score);
}

