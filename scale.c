#include "ring.h"
#include "scale.h"
#include "message.h"
#include "utilities.h"

#include <assert.h>
#include <inttypes.h>

uint64_t
scale_interval (struct ring * ring, const char * name, uint64_t interval)
{
  uint64_t reference = ring->statistics.irredundant;
  double f = logn (reference);
  double ff = f * f;
  uint64_t scaled = ff * interval;
  // *INDENT-OFF*
  very_verbose (ring, "scaled %s interval %" PRIu64
                " = %g * %" PRIu64
                " = %g^2 * %" PRIu64
                " = log10^2(%" PRIu64 ") * %" PRIu64,
                name, scaled, ff, interval, f, interval, reference, interval);
  // *INDENT-ON*
  (void) name;
  return scaled;
}
