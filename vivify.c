#include "message.h"
#include "report.h"
#include "ring.h"
#include "vivify.h"

#include <inttypes.h>

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
  uint64_t delta_probing_ticks = FAILED_EFFORT * delta_search_ticks;
  verbose (ring, "vivification effort of %" PRIu64 " = %g * %" PRIu64
           " search ticks", delta_probing_ticks, (double) FAILED_EFFORT,
	   delta_search_ticks);
  uint64_t probing_ticks_before = PROBING_TICKS;
  uint64_t limit = probing_ticks_before + delta_probing_ticks;
  size_t subsumed = 0, strengthened = 0;
  very_verbose (ring, "vivification subsumed %zu and strengthened %zu "
                "clauses after %" PRIu64 " ticks (%s)", subsumed,
		strengthened, PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));
  report (ring, 'v');
  STOP (ring, vivify);
}
