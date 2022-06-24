#include "utilities.h"

#include <math.h>

double
logn (uint64_t count)
{
  assert (count > 0);
  double res = log10 (count + 9);
  assert (res >= 1);
  return res;
}

double
nlogn (uint64_t count)
{
  return count * logn (count);
}

unsigned
gcd (unsigned a, unsigned b)
{
  while (b)
    {
      unsigned r = a % b;
      a = b, b = r;
    }
  return a;
}
