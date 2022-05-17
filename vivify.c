#include "assign.h"
#include "backtrack.h"
#include "message.h"
#include "propagate.h"
#include "report.h"
#include "ring.h"
#include "search.h"
#include "utilities.h"
#include "vivify.h"

#include <inttypes.h>

static size_t
reschedule_vivification_candidates (struct ring * ring,
                                    struct watches * candidates)
{
  assert (EMPTY (*candidates));
  for (all_watches (watch, ring->watches))
    if (watch->vivify && !watch->garbage)
      PUSH (*candidates, watch);
  return SIZE (*candidates);
}

static size_t
schedule_vivification_candidates (struct ring * ring,
                                  struct watches * candidates)
{
  for (all_watches (watch, ring->watches))
    if (!watch->vivify && watched_vivification_candidate (watch))
      PUSH (*candidates, watch);
  return SIZE (*candidates);
}

void
vivify_clauses (struct ring * ring)
{
  if (ring->inconsistent)
    return;
  struct watches * watches = &ring->watches;
  if (EMPTY (*watches))
    return;
  START (ring, vivify);
  assert (SEARCH_TICKS >= ring->last.probing);
  uint64_t delta_search_ticks = SEARCH_TICKS - ring->last.probing;
  uint64_t delta_probing_ticks = VIVIFY_EFFORT * delta_search_ticks;
  verbose (ring, "vivification effort of %" PRIu64 " = %g * %" PRIu64
           " search ticks", delta_probing_ticks, (double) VIVIFY_EFFORT,
	   delta_search_ticks);
  uint64_t probing_ticks_before = PROBING_TICKS;
  uint64_t limit = probing_ticks_before + delta_probing_ticks;
  size_t implied = 0, strengthened = 0, tried = 0, vivified = 0;
  struct watches candidates;
  INIT (candidates);
  size_t rescheduled = reschedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "rescheduling %zu vivification candidates",
                rescheduled);
  size_t scheduled = schedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "scheduled %zu vivification candidates in total",
                scheduled);
  signed char * values = ring->values;
  struct watch ** begin = candidates.begin;
  struct watch ** end = candidates.end;
  struct watch ** p = begin;
  while (p != end)
    {
      if (PROBING_TICKS > limit)
	break;
      if (terminate_ring (ring))
	break;
      tried++;
      assert (!ring->level);
      struct watch * watch = *p++;
      assert (!binary_pointer (watch));
      assert (watched_vivification_candidate (watch));
      watch->vivify = false;
      struct clause * clause = watch->clause;
      for (all_literals_in_clause (lit, clause))
	{
	  const unsigned idx = IDX (lit);
	  struct variable * v = ring->variables + idx;
	  signed char value = values[lit];
	  if (value > 0)
	    {
	      if (v->level)
		{
	     IMPLIED:
		  LOGWATCH (watch, "vivification implied");
		  ring->statistics.vivified++;
		  ring->statistics.implied++;
		  vivified++;
		  implied++;
		}
	      else
		LOGWATCH (watch, "root-level satisfied");
	      mark_garbage_watch (ring, watch);
	      break;
	    }
	  else if (value < 0)
	    {
	      if (v->level)
		{
		  ring->statistics.vivified++;
		  strengthened++;
		}
	      break;
	    }
	  else
	    {
	      ring->level++;
	      ring->statistics.contexts[PROBING_CONTEXT].decisions++;
	      unsigned not_lit = NOT (lit);
	      LOG ("assuming %s", LOGLIT (not_lit));
	      assign_decision (ring, not_lit);
	      if (ring_propagate (ring, false, watch))
		goto IMPLIED;
	    }
	}
      if (ring->level)
	backtrack (ring, 0);
    }
  if (p != end && !(*p)->vivify)
    while (p != end)
      (*p++)->vivify = true;
  RELEASE (candidates);
  very_verbose (ring,
                "vivified %zu clauses %.0f%% from %zu tried %.0f%% "
                "after %" PRIu64 " ticks (%s)",
                vivified, percent (vivified, tried),
		tried, percent (tried, scheduled),
		PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));
  very_verbose (ring, "implied %zu clauses %.0f%% of vivified "
                "and strengthened %zu clauses %.0f%%",
		implied, percent (implied, vivified),
		strengthened, percent (strengthened, vivified));
  report (ring, 'v');
  STOP (ring, vivify);
}
