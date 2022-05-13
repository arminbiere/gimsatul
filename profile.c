#include "profile.h"

#include <assert.h>

double
start_profile (struct profile *profile, double time)
{
  double volatile *p = &profile->start;
  assert (*p < 0);
  *p = time;
  return time;
}

double
stop_profile (struct profile *profile, double time)
{
  double volatile *p = &profile->start;
  double delta = time - *p;
  *p = -1;
  profile->time += delta;
  return time;
}
