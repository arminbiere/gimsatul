#ifndef _profile_h_INCLUDED
#define _profile_h_INCLUDED

struct profile
{
  const char *name;
  volatile double start;
  volatile double time;
};

#endif
