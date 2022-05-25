#ifndef _ruler_h_INCLUDED
#define _ruler_h_INCLUDED

#include "barrier.h"
#include "clause.h"
#include "options.h"
#include "profile.h"
#include "ring.h"

#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>

struct ruler_trail
{
  unsigned *begin;
  unsigned *propagate;
  unsigned *volatile end;
};

#define LOCKS \
  LOCK (rings) \
  LOCK (simplify) \
  LOCK (terminate) \
  LOCK (units) \
  LOCK (winner) \

struct ruler_locks
{
#define LOCK(NAME) \
  pthread_mutex_t NAME;
  LOCKS
#undef LOCK
};

#define BARRIERS \
  BARRIER (copy) \
  BARRIER (end) \
  BARRIER (import) \
  BARRIER (run) \
  BARRIER (start) \
  BARRIER (unclone) \

struct ruler_barriers
{
#define BARRIER(NAME) \
  struct barrier NAME;
  BARRIERS
#undef BARRIER
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

struct ruler
{
  unsigned size;
  unsigned compact;
  volatile bool terminate;
  volatile bool simplify;
  bool eliminating;
  bool inconsistent;
  bool simplifying;
  bool solving;
  bool subsuming;
  struct ruler_locks locks;
  struct ruler_barriers barriers;
  struct rings rings;
  pthread_t *threads;
  struct ring *volatile winner;
  volatile signed char *values;
  struct clauses *occurrences;
  struct clauses clauses;
  struct unsigneds *original;
  struct unsigneds extension[2];
  struct ruler_trail units;
  unsigned *map;
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
  unsigned IDX = 0, END_ ## IDX = ruler->compact; \
  IDX != END_ ## IDX; \
  ++IDX

#define all_ruler_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*ruler->compact; \
  LIT != END_ ## LIT; \
  ++LIT

#define all_positive_ruler_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*ruler->compact; \
  LIT != END_ ## LIT; \
  LIT += 2

#if 0

#define BEGIN_BARRIERS \
  ((struct barrier *) &ruler->barriers)

#define END_BARRIERS \
  ((struct barrier*) ((char *) &ruler->barriers + sizeof ruler->barriers))

#define all_barriers(B) \
  struct barrier * B = BEGIN_BARRIERS; B != END_BARRIERS; B++

#endif

/*------------------------------------------------------------------------*/

struct ruler *new_ruler (size_t size, struct options *);
void delete_ruler (struct ruler *);

void flush_large_clause_occurrences (struct ruler *);

void new_ruler_binary_clause (struct ruler *, unsigned, unsigned);
void assign_ruler_unit (struct ruler *, unsigned unit);

void connect_large_clause (struct ruler *, struct clause *);

void disconnect_literal (struct ruler *, unsigned, struct clause *);

void push_ring (struct ruler *, struct ring *);
void detach_ring (struct ring *);
void set_winner (struct ring *);

void set_terminate (struct ruler *ruler);

void print_ruler_profiles (struct ruler *);

/*------------------------------------------------------------------------*/

static inline void
connect_literal (struct ruler *ruler, unsigned lit, struct clause *clause)
{
  PUSH (OCCURRENCES (lit), clause);
}

struct ring *first_ring (struct ruler *);

#endif
