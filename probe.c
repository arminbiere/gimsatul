#include "assign.h"
#include "backtrack.h"
#include "message.h"
#include "probe.h"
#include "propagate.h"
#include "search.h"
#include "report.h"
#include "ring.h"
#include "utilities.h"

#include <inttypes.h>

bool
probing (struct ring * ring)
{
  return SEARCH_CONFLICTS > ring->limits.probing;
}

int
probe (struct ring * ring)
{
  assert (ring->size);
  STOP_SEARCH_AND_START (probing);
  assert (ring->context == SEARCH_CONTEXT);
  ring->context = PROBING_CONTEXT;
  struct ring_statistics * statistics = &ring->statistics;
  statistics->probings++;
  if (ring->level)
    backtrack (ring, 0);
  assert (SEARCH_TICKS >= ring->last.probing);
  uint64_t delta_search_ticks = SEARCH_TICKS - ring->last.probing;
  uint64_t delta_probing_ticks = PROBING_EFFORT * delta_search_ticks;
  verbose (ring, "probing effort of %" PRIu64 " = %g * %" PRIu64
           " search ticks", delta_probing_ticks, (double) PROBING_EFFORT,
	   delta_search_ticks);
  uint64_t probing_ticks_before = PROBING_TICKS;
  uint64_t limit = probing_ticks_before + delta_probing_ticks;
  bool * active = ring->active;
  unsigned start = INVALID;
  unsigned max_lit = 2*ring->size;
  unsigned probe = ring->probe;
  if (probe >= max_lit)
    probe = 0;
  unsigned failed = 0, probed = 0;
  unsigned * stamps = allocate_and_clear_array (max_lit, sizeof *stamps);
  while (PROBING_TICKS <= limit)
    {
      assert (!ring->inconsistent);
      while (probe != start &&
	     (!active[IDX (probe)] || stamps[probe] == failed + 1))
	{
	  if (start == INVALID)
	    start = probe;
	  if (++probe == max_lit)
	    probe = 0;
	}
      if (!probed)
	very_verbose (ring, "probing starts at literal %d",
		      export_literal (probe));
      if (terminate_ring (ring))
	break;
      if (probe == start)
	break;
      if (start == INVALID)
	start = probe;
      assert (!ring->values[probe]);
      ring->statistics.contexts[PROBING_CONTEXT].decisions++;
      assert (!ring->level);
      ring->level = 1;
      probed++;
      LOG ("probing literal %s", LOGLIT (probe));
      assign_decision (ring, probe);
      struct ring_trail * trail = &ring->trail;
      unsigned * saved = trail->propagate;
      assert (saved + 1 == trail->end);
      bool ok = !ring_propagate (ring, false, 0);
      if (ok)
	{
	  unsigned * end = trail->end;
	  LOG ("stamping %zu literals not to be probed",
	       end - saved);
	  assert (failed < UINT_MAX);
	  unsigned stamp = failed + 1;
          for (unsigned * p = saved; p != end; p++)
	    stamps[*p] = stamp;
	}
      backtrack (ring, 0);
      assert (!ring->level);
      if (!ok)
	{
          LOG ("failed literal %s", LOGLIT (probe));
	  ring->statistics.failed++;
	  failed++;
	  unsigned unit = NOT (probe);
	  trace_add_unit (&ring->trace, unit);
	  assign_ring_unit (ring, unit);
	  if (ring_propagate (ring, false, 0))
	    {
	      set_inconsistent (ring,
		"propagating of failed literal yields empty clause");
	      break;
	    }
	}
      if (++probe == max_lit)
	probe = 0;
    }
  free (stamps);
  very_verbose (ring, "probing ends at literal %d after %" PRIu64
                " ticks (%s)", export_literal (probe),
		PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));
  ring->probe = probe;
  struct ring_limits * limits = &ring->limits;
  limits->probing = SEARCH_CONFLICTS;
  limits->probing += PROBING_INTERVAL * nlogn (statistics->probings);
  verbose (ring, "probed %u literals %.0f%% and "
           "found %u failed literals %.0f%%", probed,
	   percent (probed, max_lit), failed, percent (failed, probed));
  verbose (ring, "next probing limit at %" PRIu64 " conflicts",
	   limits->probing);
  report (ring, 'p');
  assert (ring->context == PROBING_CONTEXT);
  ring->context = SEARCH_CONTEXT;
  ring->last.probing = SEARCH_TICKS;
  STOP_AND_START_SEARCH (probing);
  return ring->inconsistent ? 20 : 0;
}
