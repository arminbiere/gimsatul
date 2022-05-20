#include "message.h"
#include "report.h"
#include "ring.h"
#include "utilities.h"

#include <stdio.h>
#include <inttypes.h>

static volatile uint64_t reported;

void
report (struct ring *ring, char type)
{
  if (verbosity < 0)
    return;

  struct ring_statistics *s = &ring->statistics;
  struct averages *a = ring->averages + ring->stable;

  acquire_message_lock ();

  double t = wall_clock_time ();
  double m = current_resident_set_size () / (double) (1 << 20);
  uint64_t conflicts = s->contexts[SEARCH_CONTEXT].conflicts;
  unsigned active = s->active;

  bool header = !(atomic_fetch_add (&reported, 1) % 20);

  if (header)
    printf ("c\nc       seconds MB level reductions restarts "
	    "conflicts redundant trail glue irredundant variables\nc\n");

  PRINTLN ("%c %7.2f %4.0f %5.0f %6" PRIu64 " %9" PRIu64 " %11" PRIu64
	   " %9zu %3.0f%% %6.1f %9zu %9u %3.0f%%", type, t, m,
	   a->level.value, s->reductions, s->restarts, conflicts,
	   s->redundant, a->trail.value, a->glue.slow.value, s->irredundant,
	   active, percent (active, ring->size));

  fflush (stdout);

  release_message_lock ();
}
