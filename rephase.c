#include "backtrack.h"
#include "decide.h"
#include "message.h"
#include "rephase.h"
#include "report.h"
#include "search.h"
#include "ring.h"
#include "walk.h"

#include <inttypes.h>
#include <math.h>

static char
rephase_walk (struct ring *ring)
{
  local_search (ring);
  for (all_phases (p))
    p->target = p->saved;
  return 'W';
}

static char
rephase_best (struct ring *ring)
{
  for (all_phases (p))
    p->target = p->saved = p->best;
  return 'B';
}

static char
rephase_inverted (struct ring *ring)
{
  for (all_phases (p))
    p->target = p->saved = -initial_phase (ring);
  return 'I';
}

static char
rephase_original (struct ring *ring)
{
  for (all_phases (p))
    p->target = p->saved = initial_phase (ring);
  return 'O';
}

bool
rephasing (struct ring *ring)
{
  if (!ring->options.rephase)
    return false;
  return ring->stable && SEARCH_CONFLICTS > ring->limits.rephase;
}

// *INDENT-OFF*

static char (*schedule[])(struct ring *) =
{
  rephase_original, rephase_best, rephase_walk,
  rephase_inverted, rephase_best, rephase_walk,
};

// *INDENT-ON*

void
rephase (struct ring *ring)
{
  if (ring->level)
    backtrack (ring, 0);
  struct ring_statistics *statistics = &ring->statistics;
  struct ring_limits *limits = &ring->limits;
  uint64_t rephased = ++statistics->rephased;
  size_t size_schedule = sizeof schedule / sizeof *schedule;
  char type = schedule[rephased % size_schedule] (ring);
  verbose (ring, "resetting number of target assigned %u", ring->target);
  ring->target = 0;
  if (type == 'B')
    {
      verbose (ring, "resetting number of best assigned %u", ring->best);
      ring->best = 0;
    }
  limits->rephase = SEARCH_CONFLICTS;
  uint64_t interval = ring->options.rephase_interval;
  limits->rephase += interval * rephased * sqrt (rephased);
  very_verbose (ring, "next rephase limit at %" PRIu64 " conflicts",
		limits->rephase);
  report (ring, type);
}
