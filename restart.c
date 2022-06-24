#include "backtrack.h"
#include "message.h"
#include "options.h"
#include "restart.h"
#include "report.h"
#include "ring.h"
#include "utilities.h"

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
  very_verbose (ring, "restart %" PRIu64 " at %" PRIu64 " conflicts",
		statistics->restarts, SEARCH_CONFLICTS);
  update_best_and_target_phases (ring);
  backtrack (ring, 0);
  struct ring_limits *limits = &ring->limits;
  uint64_t interval;
  if (ring->stable)
    {
      struct reluctant *reluctant = &ring->reluctant;
      uint64_t u = reluctant->u, v = reluctant->v;
      if ((u & -u) == v)
	u++, v = 1;
      else
	v *= 2;
      interval = STABLE_RESTART_INTERVAL * v;
      reluctant->u = u, reluctant->v = v;
    }
  else
    interval = FOCUSED_RESTART_INTERVAL + logn (statistics->restarts) - 1;
  limits->restart = SEARCH_CONFLICTS + interval;
  very_verbose (ring, "next restart limit at %" PRIu64
                " after %" PRIu64 " conflicts",
		limits->restart, interval);
  verbose_report (ring, 'r', 1);
}
