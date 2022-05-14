#ifndef _ruler_h_INCLUDED
#define _ruler_h_INCLUDED

#include "options.h"
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
  struct unsigneds * original;
  struct clauses gate[2], nogate[2];
  struct unsigneds extension;
  struct ruler_trail units;
  struct trace trace;
  struct ruler_profiles profiles;
  struct ruler_statistics statistics;
  struct ruler_limits limits;
  struct options options;
  struct ruler_last last;
};

/*------------------------------------------------------------------------*/

#define OCCURRENCES(LIT) (ruler->occurrences[LIT])

/*------------------------------------------------------------------------*/

#define all_rings(RING) \
  all_pointers_on_stack(struct ring, RING, ruler->rings)

#define all_ruler_indices(IDX) \
  unsigned IDX = 0, END_ ## IDX = ruler->size; \
  IDX != END_ ## IDX; \
  ++IDX

#define all_ruler_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*ruler->size; \
  LIT != END_ ## LIT; \
  ++LIT

#define all_positive_ruler_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*ruler->size; \
  LIT != END_ ## LIT; \
  LIT += 2

/*------------------------------------------------------------------------*/

struct ruler * new_ruler (size_t size, struct options *);
void delete_ruler (struct ruler *);

void new_ruler_binary_clause (struct ruler *, unsigned, unsigned);
void assign_ruler_unit (struct ruler *, unsigned unit);

void connect_large_clause (struct ruler *, struct clause *);

void disconnect_literal (struct ruler *, unsigned, struct clause *);

void disconnect_and_delete_clause (struct ruler *,
                                   struct clause *, unsigned except);

void disconnect_and_delete_clauses (struct ruler *,
                                    struct clauses *, unsigned except);

void push_ring (struct ruler *, struct ring *);
void detach_ring (struct ring *);
void set_winner (struct ring *);

void print_ruler_profiles (struct ruler *);

/*------------------------------------------------------------------------*/

static inline void
connect_literal (struct ruler * ruler, unsigned lit, struct clause * clause)
{
  PUSH (OCCURRENCES (lit), clause);
}

static inline struct ring *
first_ring (struct ruler *ruler)
{
  assert (!EMPTY (ruler->rings));
  return ruler->rings.begin[0];
}

#endif
