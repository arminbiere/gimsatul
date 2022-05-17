#include "message.h"
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
  size_t subsumed = 0, strengthened = 0, tried = 0, vivified = 0;
  struct watches candidates;
  INIT (candidates);
  size_t rescheduled = reschedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "rescheduling %zu vivification candidates",
                rescheduled);
  size_t scheduled = schedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "scheduled %zu vivification candidates in total",
                scheduled);
  struct watch ** begin = candidates.begin;
  struct watch ** end = candidates.end;
  struct watch ** p = begin;
  while (p != end)
    {
      if (PROBING_TICKS > limit)
	break;
      if (terminate_ring (ring))
	break;
      struct watch * watch = *p++;
#if 1
      if (2*tried >= scheduled)
	break;
#endif
      assert (watched_vivification_candidate (watch));
      watch->vivify = false;
      tried++;
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
  very_verbose (ring, "subsumed %zu clauses %.0f%% of vivified "
                "and strengthened %zu clauses %.0f%%",
		subsumed, percent (subsumed, vivified),
		strengthened, percent (strengthened, vivified));
  report (ring, 'v');
  STOP (ring, vivify);
}
