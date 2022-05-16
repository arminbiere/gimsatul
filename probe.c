#include "assign.h"
#include "backtrack.h"
#include "failed.h"
#include "probe.h"
#include "ring.h"

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
  ring->statistics.probings++;
  if (ring->level)
    backtrack (ring, 0);
  failed_literal_probing (ring);
  ring->context = SEARCH_CONTEXT;
  ring->last.probing = SEARCH_TICKS;
  STOP_AND_START_SEARCH (probing);
  return ring->inconsistent ? 20 : 0;
}
