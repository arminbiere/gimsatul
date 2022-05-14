#include "analyze.h"
#include "export.h"
#include "propagate.h"
#include "report.h"
#include "restart.h"
#include "ruler.h"
#include "search.h"

#include <assert.h>

static void
iterate (struct ring *ring)
{
  assert (ring->iterating);
  assert (!ring->level);
  struct ring_trail *trail = &ring->trail;
  assert (trail->end == trail->propagate);
  assert (trail->iterate < trail->propagate);
  size_t new_units = trail->propagate - trail->iterate;
  very_verbose (ring, "iterating %zu units", new_units);
  ring->iterating = false;
  report (ring, 'i');
  export_units (ring);
  trail->iterate = trail->propagate;
}

static void
start_search (struct ring *ring)
{
  START (ring, search);
  assert (!ring->stable);
  START (ring, focused);
  report (ring, '{');
}

static void
stop_search (struct ring *ring, int res)
{
  if (ring->stable)
    {
      report (ring, ']');
      STOP (ring, stable);
    }
  else
    {
      report (ring, '}');
      STOP (ring, focused);
    }
  if (res == 10)
    report (ring, '1');
  else if (res == 20)
    report (ring, '0');
  else
    report (ring, '?');
  STOP (ring, search);
}

static bool
conflict_limit_hit (struct ring *ring)
{
  long limit = ring->limits.conflicts;
  if (limit < 0)
    return false;
  uint64_t conflicts = SEARCH_CONFLICTS;
  if (conflicts < (unsigned long) limit)
    return false;
  verbose (ring, "conflict limit %ld hit at %" PRIu64 " conflicts", limit,
	   conflicts);
  return true;
}

static bool
terminate_ring (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
#ifdef NFASTPATH
  if (pthread_mutex_lock (&ruler->locks.terminate))
    fatal_error ("failed to acquire terminate lock");
#endif
  bool res = ruler->terminate;
#ifdef NFASTPATH
  if (pthread_mutex_unlock (&ruler->locks.terminate))
    fatal_error ("failed to release terminate lock");
#endif
  return res;
}

static bool
walk_initially (struct ring * ring)
{
  return !ring->statistics.walked && ring->ruler->options.walk_initially;
}

int
solve (struct ring *ring)
{
  start_search (ring);
  int res = ring->inconsistent ? 20 : 0;
  while (!res)
    {
      struct watch *conflict = ring_propagate (ring, true);
      if (conflict)
	{
	  if (!analyze (ring, conflict))
	    res = 20;
	}
      else if (!ring->unassigned)
	set_satisfied (ring), res = 10;
      else if (ring->iterating)
	iterate (ring);
      else if (terminate_ring (ring))
	break;
      else if (walk_initially (ring))
	local_search (ring);
#if 0
      else if (!ring->statistics.reductions)
	reduce (ring);
#endif
      else if (conflict_limit_hit (ring))
	break;
      else if (reducing (ring))
	reduce (ring);
      else if (restarting (ring))
	restart (ring);
      else if (switching_mode (ring))
	switch_mode (ring);
      else if (rephasing (ring))
	rephase (ring);
      else if (!import_shared (ring))
	decide (ring);
      else if (ring->inconsistent)
	res = 20;
    }
  stop_search (ring, res);
  return res;
}

void
warming_up_saved_phases (struct ring *ring)
{
  assert (!ring->level);
  assert (ring->trail.propagate == ring->trail.end);
  uint64_t decisions = 0, conflicts = 0;
  while (ring->unassigned)
    {
      decisions++;
      decide (ring);
      if (!ring_propagate (ring, false))
	conflicts++;
    }
  if (ring->level)
    backtrack (ring, 0);
  verbose (ring,
	   "warmed-up phases with %" PRIu64 " decisions and %" PRIu64
	   " conflicts", decisions, conflicts);
}
