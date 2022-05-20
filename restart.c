#include "backtrack.h"
#include "message.h"
#include "options.h"
#include "restart.h"
#include "report.h"
#include "ring.h"

#include <inttypes.h>

bool
restarting (struct ring *ring)
{
  if (!ring->level)
    return false;
  struct ring_limits *l = &ring->limits;
  if (!ring->stable)
    {
      struct averages *a = ring->averages;
      if (a->glue.fast.value <= RESTART_MARGIN * a->glue.slow.value)
	return false;
    }
  return l->restart < SEARCH_CONFLICTS;
}

void
restart (struct ring *ring)
{
  struct ring_statistics *statistics = &ring->statistics;
  statistics->restarts++;
  verbose (ring, "restart %" PRIu64 " at %" PRIu64 " conflicts",
	   statistics->restarts, SEARCH_CONFLICTS);
  update_best_and_target_phases (ring);
  backtrack (ring, 0);
  struct ring_limits *limits = &ring->limits;
  limits->restart = SEARCH_CONFLICTS;
  if (ring->stable)
    {
      struct reluctant *reluctant = &ring->reluctant;
      uint64_t u = reluctant->u, v = reluctant->v;
      if ((u & -u) == v)
	u++, v = 1;
      else
	v *= 2;
      limits->restart += STABLE_RESTART_INTERVAL * v;
      reluctant->u = u, reluctant->v = v;
    }
  else
    limits->restart += FOCUSED_RESTART_INTERVAL;
  verbose (ring, "next restart limit at %" PRIu64 " conflicts",
	   limits->restart);
  if (verbosity > 0)
    report (ring, 'r');
}
