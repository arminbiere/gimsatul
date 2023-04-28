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
  assert (!ring->inactive[idx]);

  assert (ring->unassigned);
  ring->unassigned--;

  ring->values[lit] = 1;
  ring->values[not_lit] = -1;

  if (ring->context != PROBING_CONTEXT)
    ring->phases[idx].saved = SGN (lit) ? -1 : 1;

  struct variable *v = ring->variables + idx;
  unsigned level = ring->level;
  v->level = level;

  if (!level)
    {
      if (reason)
	trace_add_unit (&ring->trace, lit);
      v->reason = 0;
      ring->statistics.fixed++;
      assert (ring->statistics.active);
      ring->statistics.active--;
      assert (!ring->inactive[idx]);
      ring->inactive[idx] = true;
    }
  else {
    if (is_binary_pointer (reason)) {
      unsigned other = other_pointer (reason);
      unsigned other_idx = IDX (other);
      struct variable *u = ring->variables + other_idx;
      if (is_binary_pointer (u->reason)) {
	bool redundant = redundant_pointer (reason) ||
	                 redundant_pointer (u->reason);
	reason = tag_binary (redundant, lit, other_pointer (u->reason));
	LOGWATCH (reason, "jumping %s reason", LOGLIT (lit));
      }
    }
    v->reason = reason;
  }

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
#ifdef LOGGING
  if (ring->context == WALK_CONTEXT)
    LOG ("assign %s decision warm-up", LOGLIT (decision));
  else if (ring->context == PROBING_CONTEXT)
    LOG ("assign %s decision probe", LOGLIT (decision));
  else
    {
      assert (ring->context == SEARCH_CONTEXT);
      if (ring->stable)
	LOG ("assign %s decision score %g",
	     LOGLIT (decision), ring->heap.nodes[IDX (decision)].score);
      else
	LOG ("assign %s decision stamp %" PRIu64,
	     LOGLIT (decision), ring->queue.links[IDX (decision)].stamp);
    }
#endif
}
