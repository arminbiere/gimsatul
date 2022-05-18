#include "solve.h"
#include "search.h"
#include "message.h"
#include "ruler.h"

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
  limits->mode = MODE_INTERVAL;
  limits->probe = ring->options.probe_interval;
  limits->reduce = ring->options.reduce_interval;
  limits->restart = FOCUSED_RESTART_INTERVAL;
  limits->rephase = REPHASE_INTERVAL;
  verbose (ring, "reduce interval of %" PRIu64 " conflicts", limits->reduce);
  verbose (ring, "restart interval of %" PRIu64 " conflicts", limits->restart);
  verbose (ring, "probe interval of %" PRIu64 " conflicts", limits->probe);
  verbose (ring, "initial mode switching interval of %" PRIu64 " conflicts",
	   limits->mode);
  if (conflicts >= 0)
    {
      limits->conflicts = conflicts;
      verbose (ring, "conflict limit set to %lld conflicts", conflicts);
    }
}

struct ring *
solve_rings (struct ruler *ruler)
{
  double start_solving = START (ruler, solve);
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
  if (threads > 1)
    {
      unsigned delta = ruler->size / threads;
      unsigned probe = 0;
      for (all_rings (ring))
	{
	  ring->probe = probe;
	  probe += delta;
	}
      message (0, "starting and running %zu ring threads", threads);

      for (all_rings (ring))
	start_running_ring (ring);

      for (all_rings (ring))
	stop_running_ring (ring);
    }
  else
    {
      message (0, "running single ring in main thread");
      struct ring *ring = first_ring (ruler);
      solve_routine (ring);
    }
  assert (ruler->solving);
  ruler->solving = false;
  double end_solving = STOP (ruler, solve);
  verbose (0, "finished solving using %zu threads in %.2f seconds",
           threads, end_solving - start_solving);
  return (struct ring *) ruler->winner;
}
