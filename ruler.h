#ifndef _ruler_h_INCLUDED
#define _ruler_h_INCLUDED

#include "profile.h"
#include "clause.h"
#include "ring.h"

#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>

struct ruler_profiles
{
  struct profile cloning;
  struct profile eliminating;
  struct profile deduplicating;
  struct profile parsing;
  struct profile solving;
  struct profile simplifying;
  struct profile substituting;
  struct profile subsuming;

  struct profile total;
};

struct ruler_trail
{
  unsigned *begin;
  unsigned *propagate;
  unsigned *volatile end;
};

struct ruler_locks
{
  pthread_mutex_t rings;
  pthread_mutex_t units;
#ifdef NFASTPATH
  pthread_mutex_t terminate;
  pthread_mutex_t winner;
#endif
};

struct ruler_last
{
  unsigned fixed;
  uint64_t garbage;
};

struct ruler_limits
{
  uint64_t elimination;
  uint64_t subsumption;
};

struct ruler_statistics
{
  uint64_t garbage;
  uint64_t binaries;
  unsigned active;
  unsigned original;
  unsigned deduplicated;
  unsigned eliminated;
  unsigned definitions;
  unsigned strengthened;
  unsigned subsumed;
  unsigned substituted;
  unsigned selfsubsumed;
  struct
  {
    uint64_t elimination;
    uint64_t subsumption;
  } ticks;
  struct {
    unsigned simplifying;
    unsigned solving;
    unsigned total;
  } fixed;
};

struct ruler
{
  unsigned size;
  volatile bool terminate;
  bool eliminating;
  bool inconsistent;
  bool simplifying;
  bool solving;
  bool subsuming;
  struct ruler_locks locks;
  struct rings rings;
  pthread_t *threads;
  struct ring *volatile winner;
  volatile signed char *values;
  signed char *marks;
  bool *eliminated;
  bool *eliminate;
  bool *subsume;
  struct clauses *occurrences;
  struct clauses clauses;
  struct unsigneds resolvent;
  struct clauses gate[2], nogate[2];
  struct unsigneds extension;
  struct ruler_trail units;
  struct buffer buffer;
  struct ruler_profiles profiles;
  struct ruler_statistics statistics;
  struct ruler_limits limits;
  struct ruler_last last;
};

#endif
