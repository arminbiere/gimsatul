#include "backtrack.h"
#include "decide.h"
#include "message.h"
#include "propagate.h"
#include "ruler.h"
#include "warm.h"

#include <inttypes.h>

void
warming_up_saved_phases (struct ring *ring)
{
  if (!ring->options.warm_up_walking)
    return;
  assert (!ring->level);
  assert (ring->trail.propagate == ring->trail.end);
  uint64_t decisions = 0, conflicts = 0;
  volatile bool *terminate = &ring->ruler->terminate;
  while (ring->unassigned && !*terminate)
    {
      decisions++;
      decide (ring);
      if (ring_propagate (ring, false, 0))
	conflicts++;
    }
  if (ring->level)
    backtrack (ring, 0);
  verbose (ring,
	   "warmed-up phases with %" PRIu64 " decisions and %" PRIu64
	   " conflicts", decisions, conflicts);
}
