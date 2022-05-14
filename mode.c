#include "bump.h"
#include "mode.h"
#include "options.h"
#include "report.h"
#include "ring.h"

static void
switch_to_focused_mode (struct ring *ring)
{
  assert (ring->stable);
  report (ring, ']');
  STOP (ring, stable);
  ring->stable = false;
  START (ring, focused);
  report (ring, '{');
  struct ring_limits *limits = &ring->limits;
  limits->restart = SEARCH_CONFLICTS + FOCUSED_RESTART_INTERVAL;
}

static void
switch_to_stable_mode (struct ring *ring)
{
  assert (!ring->stable);
  report (ring, '}');
  STOP (ring, focused);
  ring->stable = true;
  START (ring, stable);
  report (ring, '[');
  struct ring_limits *limits = &ring->limits;
  limits->restart = SEARCH_CONFLICTS + STABLE_RESTART_INTERVAL;
  ring->reluctant.u = ring->reluctant.v = 1;
}

bool
switching_mode (struct ring *ring)
{
  struct ring_limits *l = &ring->limits;
  if (ring->statistics.switched)
    return SEARCH_TICKS > l->mode;
  else
    return SEARCH_CONFLICTS > l->mode;
}

static uint64_t
square (uint64_t n)
{
  assert (n);
  return n * n;
}

void
switch_mode (struct ring *ring)
{
  struct ring_statistics *s = &ring->statistics;
  struct intervals *i = &ring->intervals;
  struct ring_limits *l = &ring->limits;
  if (!s->switched++)
    {
      i->mode = SEARCH_TICKS;
      verbose (ring, "determined mode switching ticks interval %" PRIu64,
	       i->mode);
    }
  if (ring->stable)
    switch_to_focused_mode (ring);
  else
    switch_to_stable_mode (ring);
  swap_scores (ring);
  l->mode = SEARCH_TICKS + square (s->switched / 2 + 1) * i->mode;
  verbose (ring, "next mode switching limit at %" PRIu64 " ticks", l->mode);
}
