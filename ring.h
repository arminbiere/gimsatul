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

struct ring_profiles
{
  struct profile failed;
  struct profile focused;
  struct profile probing;
  struct profile search;
  struct profile stable;
  struct profile vivify;
  struct profile walk;

  struct profile solving;
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

struct context
{
  uint64_t propagations;
  uint64_t ticks;
  uint64_t conflicts;
  uint64_t decisions;
};

#define SEARCH_CONTEXT 0
#define PROBING_CONTEXT 1
#define WALK_CONTEXT 2
#define SIZE_CONTEXTS 3

struct ring_statistics
{
  uint64_t flips;
  uint64_t probings;
  uint64_t reductions;
  uint64_t rephased;
  uint64_t restarts;
  uint64_t switched;
  uint64_t walked;

  struct context contexts[SIZE_CONTEXTS];

  struct
  {
    uint64_t learned;
    uint64_t deduced;
    uint64_t minimized;
    uint64_t shrunken;
  } literals;

  unsigned active;
  unsigned failed;
  unsigned fixed;
  unsigned lifted;

  size_t irredundant;
  size_t redundant;

  struct
  {
    uint64_t units;
    uint64_t binary;
    uint64_t clauses;
    uint64_t glue1;
    uint64_t tier1;
    uint64_t tier2;
    uint64_t tier3;
  } learned;

  struct
  {
    uint64_t units;
    uint64_t binary;
    uint64_t clauses;
    uint64_t glue1;
    uint64_t tier1;
    uint64_t tier2;
  } exported, imported;
};

#define SEARCH_CONFLICTS \
  ring->statistics.contexts[SEARCH_CONTEXT].conflicts

#define SEARCH_TICKS \
  ring->statistics.contexts[SEARCH_CONTEXT].ticks

#define PROBING_TICKS \
  ring->statistics.contexts[PROBING_CONTEXT].ticks

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
