#ifndef _profile_h_INCLUDED
#define _profile_h_INCLUDED

#include "system.h"

#include <assert.h>
#include <string.h>

struct profile
{
  const char *name;
  volatile double start;
  volatile double time;
};

/*------------------------------------------------------------------------*/

#define START(OWNER,NAME) \
  start_profile (&OWNER->profiles.NAME, current_time ())

#define STOP(OWNER,NAME) \
  stop_profile (&OWNER->profiles.NAME, current_time ())

#define MODE_PROFILE \
  (ring->stable ? &ring->profiles.stable : &ring->profiles.focused)

#define STOP_SEARCH_AND_START(NAME) \
do { \
  double t = current_time (); \
  stop_profile (MODE_PROFILE, t); \
  stop_profile (&ring->profiles.search, t); \
  start_profile (&ring->profiles.NAME, t); \
} while (0)

#define STOP_AND_START_SEARCH(NAME) \
do { \
  double t = current_time (); \
  stop_profile (&ring->profiles.NAME, t); \
  start_profile (&ring->profiles.search, t); \
  start_profile (MODE_PROFILE, t); \
} while (0)

#define INIT_PROFILE(OWNER,NAME) \
do { \
  struct profile * profile = &OWNER->profiles.NAME; \
  profile->start = -1; \
  profile->name = #NAME; \
} while (0)

/*------------------------------------------------------------------------*/

double start_profile (struct profile *, double time);
double stop_profile (struct profile *, double time);

/*------------------------------------------------------------------------*/

static inline void
flush_profile (double time, struct profile *profile)
{
  double volatile *p = &profile->start;
  assert (*p >= 0);
  double delta = time - *p;
  *p = time;
  profile->time += delta;
}

static inline int
cmp_profiles (struct profile *a, struct profile *b)
{
  if (!a)
    return -1;
  if (!b)
    return -1;
  if (a->time < b->time)
    return -1;
  if (a->time > b->time)
    return 1;
  return strcmp (b->name, a->name);
}

#endif
