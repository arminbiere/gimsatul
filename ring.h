#ifndef _ring_h_INCLUDED
#define _ring_h_INCLUDED

#include "average.h"
#include "clause.h"
#include "heap.h"
#include "logging.h"
#include "macros.h"
#include "options.h"
#include "profile.h"
#include "queue.h"
#include "stack.h"
#include "statistics.h"
#include "tagging.h"
#include "trace.h"
#include "variable.h"
#include "watches.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

struct ruler;

struct reluctant
{
  uint64_t u, v;
};

struct ring_limits
{
  uint64_t mode;
  uint64_t probing;
  uint64_t reduce;
  uint64_t rephase;
  uint64_t restart;
  long long conflicts;
};

struct intervals
{
  uint64_t mode;
};

struct averages
{
  struct
  {
    struct average fast;
    struct average slow;
  } glue;
  struct average level;
  struct average trail;
};

struct ring_last
{
  unsigned fixed;
  uint64_t probing;
  uint64_t walk;
};

struct ring_trail
{
  unsigned *begin, *end, *pos;
  unsigned *propagate, *iterate;
  unsigned *export;
};

#define BINARY_SHARED 0
#define GLUE1_SHARED 1
#define TIER1_SHARED 2
#define TIER2_SHARED 3
#define SIZE_SHARED 4

#define ALLOCATED_SHARED \
  (CACHE_LINE_SIZE / sizeof (struct clause *))

struct pool
{
  struct clause *volatile share[ALLOCATED_SHARED];
};

struct ring
{
  unsigned id;
  unsigned threads;
  struct ruler *ruler;
  struct pool *pool;
  volatile int status;
  unsigned *units;
  bool inconsistent;
  bool iterating;
  bool stable;
  unsigned size;
  unsigned level;
  unsigned probe;
  unsigned context;
  unsigned unassigned;
  unsigned target;
  unsigned best;
  bool *used;
  signed char *values;
  signed char *marks;
  bool *active;
  struct variable *variables;
  struct watches watches;
  size_t vivify;
  struct references *references;
  struct unsigneds levels;
  struct heap heap;
  struct queue queue;
  struct unsigneds clause;
  struct unsigneds analyzed;
  struct unsigneds minimize;
  struct ring_trail trail;
  struct ring_limits limits;
  struct trace trace;
  struct intervals intervals;
  struct averages averages[2];
  struct reluctant reluctant;
  struct ring_statistics statistics;
  struct ring_profiles profiles;
  struct ring_last last;
  uint64_t random;
};

struct rings
{
  struct ring **begin, **end, **allocated;
};

/*------------------------------------------------------------------------*/

#define VAR(LIT) (ring->variables + IDX (LIT))
#define REFERENCES(LIT) (ring->references[LIT])

/*------------------------------------------------------------------------*/

#define all_ring_indices(IDX) \
  unsigned IDX = 0, END_ ## IDX = ring->size; \
  IDX != END_ ## IDX; \
  ++IDX

#define all_ring_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*ring->size; \
  LIT != END_ ## LIT; \
  ++LIT

#define all_variables(VAR) \
  struct variable * VAR = ring->variables, \
                  * END_ ## VAR = VAR + ring->size; \
  (VAR != END_ ## VAR); \
  ++ VAR

#define all_averages(AVG) \
  struct average * AVG = (struct average*) &ring->averages, \
  * END_ ## AVG = (struct average*) ((char*) AVG + sizeof ring->averages); \
  AVG != END_ ## AVG; \
  ++AVG

/*------------------------------------------------------------------------*/

struct ring * new_ring (struct ruler *);
void delete_ring (struct ring *);

void init_pool (struct ring *, unsigned threads);

void mark_satisfied_ring_clauses_as_garbage (struct ring *);

void inc_clauses (struct ring *ring, bool redundant);
void dec_clauses (struct ring *ring, bool redundant);

void set_inconsistent (struct ring *, const char *msg);
void set_satisfied (struct ring *);

void print_ring_profiles (struct ring *);

/*------------------------------------------------------------------------*/

static inline void
watch_literal (struct ring *ring, unsigned lit, struct watch *watch)
{
  LOGWATCH (watch, "watching %s in", LOGLIT (lit));
  PUSH (REFERENCES (lit), watch);
}

#endif
