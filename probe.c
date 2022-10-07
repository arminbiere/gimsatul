#include "assign.h"
#include "backtrack.h"
#include "fail.h"
#include "message.h"
#include "probe.h"
#include "ring.h"
#include "scale.h"
#include "utilities.h"
#include "vivify.h"

#include <inttypes.h>

bool
probing (struct ring *ring)
{
  if (!ring->options.probe)
    return false;
  if (ring->statistics.reductions < ring->limits.probe.reductions)
    return false;
  return SEARCH_PROGRESS > ring->limits.probe.progress;
}

int
probe (struct ring *ring)
{
  assert (ring->size);
  assert (ring->options.probe);
  STOP_SEARCH_AND_START (probe);
  assert (ring->context == SEARCH_CONTEXT);
  ring->context = PROBING_CONTEXT;
  ring->statistics.probings++;
  if (ring->level)
    backtrack (ring, 0);
  failed_literal_probing (ring);
  vivify_clauses (ring);
  ring->context = SEARCH_CONTEXT;
  ring->last.probing = SEARCH_TICKS;
  struct ring_statistics *statistics = &ring->statistics;
  struct ring_limits *limits = &ring->limits;
  uint64_t base = ring->options.probe_interval;
  uint64_t interval = base * nlogn (statistics->probings);
  uint64_t scaled = scale_interval (ring, "probe", interval);
  limits->probe.progress = SEARCH_PROGRESS + scaled;
  limits->probe.reductions = statistics->reductions + 1;
  very_verbose (ring, "new probe limit at %" PRIu64 " after %" PRIu64,
		limits->probe.progress, scaled);
  STOP_AND_START_SEARCH (probe);
  return ring->inconsistent ? 20 : 0;
}
