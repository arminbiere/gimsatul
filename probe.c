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
  struct ring_limits * limits = &ring->limits;
  statistics->probings++;
  if (ring->level)
    backtrack (ring, 0);
  assert (SEARCH_TICKS >= ring->last.probing);
  uint64_t ticks = SEARCH_TICKS - ring->last.probing;
  uint64_t limit = PROBING_EFFORT * ticks;
  verbose (ring, "probing effort of %" PRIu64 " = %g * %" PRIu64
           " search ticks", ticks, (double) PROBING_EFFORT, limit);
  bool * active = ring->active;
  unsigned start = INVALID;
  unsigned max_lit = 2*ring->size;
  unsigned probe = ring->probe;
  if (probe >= max_lit)
    probe = 0;
  very_verbose (ring, "probing starts at literal %d",
                export_literal (probe));
  unsigned failed = 0;
  while (!ring->inconsistent &&
         PROBING_TICKS <= limit && !terminate_ring (ring))
    {
      while (probe != start && !active[IDX (probe)])
	{
	  if (start == INVALID)
	    start = probe;
	  if (++probe == max_lit)
	    probe = 0;
	}
      if (probe == start)
	break;
      if (start == INVALID)
	start = probe;
      assert (!ring->values[probe]);
      ring->statistics.contexts[PROBING_CONTEXT].decisions++;
      ring->level = 1;
      LOG ("probing literal %s", LOGLIT (probe));
      assign_decision (ring, probe);
      bool ok = !ring_propagate (ring, false, 0);
      backtrack (ring, 0);
      if (!ok)
	{
	  failed++;
	  ring->statistics.failed++;
          LOG ("failed literal %s", LOGLIT (probe));
	  unsigned unit = NOT (probe);
	  trace_add_unit (&ring->trace, unit);
	  assign_ring_unit (ring, unit);
	  if (ring_propagate (ring, false, 0))
	    set_inconsistent (ring,
	      "propagating negation of failed literal failed");
	}
      if (++probe == max_lit)
	probe = 0;
    }
  very_verbose (ring, "probing ends at literal %d",
                export_literal (probe));
  ring->probe = probe;
  limits->probing = SEARCH_CONFLICTS;
  limits->probing += PROBING_INTERVAL * nlogn (statistics->probings);
  verbose (ring, "found %u failed literals", failed);
  verbose (ring, "next probing limit at %" PRIu64 " conflicts",
	   limits->probing);
  report (ring, 'p');
  assert (ring->context == PROBING_CONTEXT);
  ring->context = SEARCH_CONTEXT;
  ring->last.probing = SEARCH_TICKS;
  STOP_AND_START_SEARCH (probing);
  return 0;
}
