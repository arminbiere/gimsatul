#include "utilities.h"

#include <math.h>

static double
logn (uint64_t count)
{
  assert (count);
  return log10 (count + 9);
}

double
nlogn (uint64_t count)
{
  return count * logn (count);
}
