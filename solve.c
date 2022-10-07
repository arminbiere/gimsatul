#include "solve.h"
#include "search.h"
#include "message.h"
#include "ruler.h"
#include "scale.h"

#include <stdio.h>
#include <inttypes.h>

static void *
solve_routine (void *ptr)
{
  struct ring *ring = ptr;
  int res = search (ring);
  assert (ring->status == res);
  (void) res;
  return ring;
}

static void
start_running_ring (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  assert (ruler->threads);
  pthread_t *thread = ruler->threads + ring->id;
  if (pthread_create (thread, 0, solve_routine, ring))
    fatal_error ("failed to create solving thread %u", ring->id);
#if 1
  int sched_getcpu (void);
  message (ring, "sched_getcpu: cpu=%08x", sched_getcpu ());
#endif
}

static void
stop_running_ring (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  assert (ruler->threads);
  pthread_t *thread = ruler->threads + ring->id;
  if (pthread_join (*thread, 0))
    fatal_error ("failed to join solving thread %u", ring->id);
}

static void
set_ring_limits (struct ring *ring, long long conflicts)
{
  if (ring->inconsistent)
    return;
  assert (!ring->stable);
  assert (!SEARCH_CONFLICTS);
  struct ring_limits *limits = &ring->limits;
  if (ring->options.portfolio)
    {
      switch (ring->id % 3)
	{
	case 1:
	  ring->options.switch_mode = false;
	  ring->options.focus_initially = false;
	  break;
	case 2:
	  ring->options.switch_mode = false;
	  ring->options.focus_initially = true;
	  break;
	}

      if (ring->id & 1)
	ring->options.phase ^= 1;

      if (ring->id & 2)
	ring->options.bump_reasons ^= 1;
    }
  else
    very_verbose (ring, "keeping global options");

  if (ring->options.switch_mode)
    {
      if (ring->options.focus_initially)
	verbose (ring, "starting in focused mode");
      else
	verbose (ring, "starting in stable mode");
    }
  else
    {
      if (ring->options.focus_initially)
	verbose (ring, "only running in focused mode");
      else
	verbose (ring, "only running in stable mode");
    }
  limits->mode = ring->options.switch_interval;
  if (ring->options.switch_mode)
    verbose (ring, "initial mode switching interval of %" PRIu64 " conflicts",
	     limits->mode);

  if (ring->options.phase)
    verbose (ring, "initial 'true' decision phase");
  else
    verbose (ring, "initial 'false' decision phase");

  if (ring->options.bump_reasons)
    verbose (ring, "bumping reasons clauses literals additionally");
  else
    verbose (ring, "no extra bumping of literals in reason clauses");

  limits->reduce = ring->options.reduce_interval;
  limits->restart = FOCUSED_RESTART_INTERVAL;
  limits->rephase = ring->options.rephase_interval;

  verbose (ring, "reduce interval of %" PRIu64 " conflicts", limits->reduce);
  verbose (ring, "restart interval of %" PRIu64 " conflicts",
	   limits->restart);
  verbose (ring, "rephase interval of %" PRIu64 " conflicts",
	   limits->rephase);

  {
    uint64_t interval = ring->options.probe_interval;
    uint64_t scaled = scale_interval (ring, "probe", interval);
    verbose (ring, "probe limit of %" PRIu64, scaled);
    limits->probe.progress = scaled;
  }

  if (!ring->id)
    {
      uint64_t interval = ring->options.simplify_interval;
      uint64_t scaled = scale_interval (ring, "simplify", interval);
      verbose (ring, "simplify limit of %" PRIu64 " conflicts", scaled);
      limits->simplify = scaled;
    }

  if (conflicts >= 0)
    {
      limits->conflicts = conflicts;
      verbose (ring, "conflict limit set to %lld conflicts", conflicts);
    }
}

struct ring *
solve_rings (struct ruler *ruler)
{
  if (ruler->terminate)
    return ruler->winner;
#ifndef QUIET
  double start_solving = START (ruler, solve);
#endif
  assert (!ruler->solving);
  ruler->solving = true;
  size_t threads = SIZE (ruler->rings);
  long long conflicts = ruler->options.conflicts;
  if (verbosity >= 0)
    {
      printf ("c\n");
      if (conflicts >= 0)
	printf ("c conflict limit %lld\n", conflicts);
      fflush (stdout);
    }
  for (all_rings (ring))
    set_ring_limits (ring, conflicts);
  message (0, 0);
  if (threads > 1)
    {
      for (all_rings (ring))
	ring->probe = ring->id * (ruler->compact / threads);

      message (0, "starting and running %zu ring threads", threads);

#define BARRIER(NAME) \
      init_barrier (&ruler->barriers.NAME, #NAME, threads);
      BARRIERS
#undef BARRIER
// *INDENT-OFF*

      for (all_rings (ring))
	start_running_ring (ring);

      for (all_rings (ring))
	stop_running_ring (ring);

// *INDENT-ON*
    }
  else
    {
      message (0, "running single ring in main thread");
      struct ring *ring = first_ring (ruler);
      solve_routine (ring);
    }
  assert (ruler->solving);
  ruler->solving = false;
#ifndef QUIET
  double end_solving = STOP (ruler, solve);
  verbose (0, "finished solving using %zu threads in %.2f seconds",
	   threads, end_solving - start_solving);
#endif
  return (struct ring *) ruler->winner;
}
