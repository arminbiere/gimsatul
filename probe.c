#include "assign.h"
#include "backtrack.h"
#include "fail.h"
#include "probe.h"
#include "ring.h"
#include "vivify.h"
#include "utilities.h"

bool
probing (struct ring * ring)
{
  if (!ring->options->probe)
    return false;
  return SEARCH_CONFLICTS > ring->limits.probing;
}

int
probe (struct ring * ring)
{
  assert (ring->size);
  assert (ring->options->probe);
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
  struct ring_statistics * statistics = &ring->statistics;
  struct ring_limits * limits = &ring->limits;
  limits->probing = SEARCH_CONFLICTS;
  limits->probing += PROBING_INTERVAL * nlogn (statistics->probings);
  STOP_AND_START_SEARCH (probe);
  return ring->inconsistent ? 20 : 0;
}
