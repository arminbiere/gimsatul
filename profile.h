#ifndef _profile_h_INCLUDED
#define _profile_h_INCLUDED

#include "system.h"

struct profile
{
  const char *name;
  volatile double start;
  volatile double time;
};

struct ring_profiles
{
  struct profile fail;
  struct profile focus;
  struct profile probe;
  struct profile search;
  struct profile stable;
  struct profile vivify;
  struct profile walk;

  struct profile solve;
};

struct ruler_profiles
{
  struct profile clone;
  struct profile eliminate;
  struct profile deduplicate;
  struct profile parse;
  struct profile solve;
  struct profile simplify;
  struct profile substitute;
  struct profile subsume;

  struct profile total;
};

/*------------------------------------------------------------------------*/

#define START(OWNER,NAME) \
  start_profile (&OWNER->profiles.NAME, current_time ())

#define STOP(OWNER,NAME) \
  stop_profile (&OWNER->profiles.NAME, current_time ())

#define MODE_PROFILE \
  (ring->stable ? &ring->profiles.stable : &ring->profiles.focus)

#define STOP_SEARCH() \
do { \
  double t = current_time (); \
  stop_profile (MODE_PROFILE, t); \
  stop_profile (&ring->profiles.search, t); \
} while (0)

#define START_SEARCH() \
do { \
  double t = current_time (); \
  start_profile (&ring->profiles.search, t); \
  start_profile (MODE_PROFILE, t); \
} while (0)

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

#endif
