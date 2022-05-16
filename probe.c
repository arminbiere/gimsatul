#include "assign.h"
#include "backtrack.h"
#include "message.h"
#include "probe.h"
#include "propagate.h"
#include "search.h"
#include "report.h"
#include "ring.h"
#include "utilities.h"

#if 1
#include "cover.h"
#endif

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
  signed char * values = ring->values;
  bool * active = ring->active;
  unsigned start = INVALID;
  unsigned max_lit = 2*ring->size;
  unsigned probe = ring->probe;
  if (probe >= max_lit)
    probe = 0;
  unsigned failed = 0, lifted = 0, probed = 0, last = INVALID;
  unsigned * stamps = allocate_and_clear_array (max_lit, sizeof *stamps);
  struct unsigneds lift;
  INIT (lift);
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
	  unsigned not_probe = NOT (probe);
	  if (last == not_probe)
	    {
	      assert (probe & 1);
	      unsigned * q = lift.begin;
	      for (unsigned * p = q; p != lift.end; p++)
		if (values[*p] > 0)
		  *q++ = *p;
	      lift.end = q;
	    }
	  else if (!EMPTY (lift))
	    CLEAR (lift);
	  if (EMPTY (lift))
	    {
	      unsigned * end = trail->end;
	      LOG ("stamping %zu literals not to be probed",
		   end - saved);
	      assert (failed < UINT_MAX);
	      unsigned stamp = failed + 1;
	      for (unsigned * p = saved; p != end; p++)
		stamps[*p] = stamp;
	      if (!(probe & 1))
		{
		  CLEAR (lift);
		  assert (saved < end);
		  for (unsigned * p = saved + 1; p != end; p++)
		    PUSH (lift, *p);
		}
	    }
	  else
	    {
	      assert (probe & 1);
	      assert (last == NOT (probe));
	      backtrack (ring, 0);
	      for (unsigned * p = lift.begin; p != lift.end; p++)
		{
		  unsigned unit = *p;
		  signed char value = values[unit];
		  if (value > 0)
		    continue;
		  if (value < 0)
		    {
		      trace_add_empty (&ring->trace);
		      set_inconsistent (ring,
			"falsified lifted literal yields empty clause");
		      break;
		    }
		  LOG ("lifted literal %s", LOGLIT (unit));
		  ring->statistics.lifted++;
		  lifted++;
		  trace_add_binary (&ring->trace, not_probe, unit);
		  trace_add_binary (&ring->trace, probe, unit);
		  trace_add_unit (&ring->trace, unit);
		  trace_delete_binary (&ring->trace, not_probe, unit);
		  trace_delete_binary (&ring->trace, probe, unit);
		  assign_ring_unit (ring, unit);
		  if (ring_propagate (ring, false, 0))
		    {
		      trace_add_empty (&ring->trace);
		      set_inconsistent (ring,
			"propagating of lifted literal yields empty clause");
		      break;
		    }
		}
	      CLEAR (lift);
	      assert (ok);
	      if (ring->inconsistent)
		break;
	    }
	}
      if (ring->level)
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
	      trace_add_empty (&ring->trace);
	      set_inconsistent (ring,
		"propagating of failed literal yields empty clause");
	      break;
	    }
	}
      last = probe;
      if (++probe == max_lit)
	probe = 0;
    }
  RELEASE (lift);
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
           "found %u failed literals %.0f%% lifted %u", probed,
	   percent (probed, max_lit), failed,
	   percent (failed, probed), lifted);
  verbose (ring, "next probing limit at %" PRIu64 " conflicts",
	   limits->probing);
  report (ring, 'p');
  assert (ring->context == PROBING_CONTEXT);
  ring->context = SEARCH_CONTEXT;
  ring->last.probing = SEARCH_TICKS;
  STOP_AND_START_SEARCH (probing);
  return ring->inconsistent ? 20 : 0;
}
