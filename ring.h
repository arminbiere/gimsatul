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
  uint64_t probe;
  uint64_t reduce;
  uint64_t rephase;
  uint64_t restart;
  uint64_t simplify;
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
  uint64_t reduce;
  uint64_t walk;
};

struct ring_trail
{
  unsigned *begin, *end, *pos;
  unsigned *propagate, *iterate;
  unsigned *export;
};

#define BINARY_SHARED 0
#define SIZE_SHARED 16

struct pool
{
  atomic_uintptr_t share[SIZE_SHARED];
};

struct ring
{
  unsigned id;
  unsigned threads;
  unsigned import;
  struct pool *pool;
  unsigned *units;
  struct ruler *ruler;

  volatile int status;

  bool inconsistent;
  bool stable;

  signed char iterating;

  unsigned best;
  unsigned context;
  unsigned level;
  unsigned probe;
  unsigned size;
  unsigned target;
  unsigned unassigned;

  signed char *marks;
  signed char *values;

  bool *inactive;
  bool *used;

  struct unsigneds analyzed;
  struct unsigneds clause;
  struct unsigneds levels;
  struct unsigneds minimize;

  struct references *references;
  struct ring_trail trail;
  struct variable *variables;

  struct heap heap;
  struct phases *phases;
  struct queue queue;

  unsigned tier2;
  unsigned redundant;
  struct watchers watchers;
  struct clauses saved;

  struct trace trace;

  struct averages averages[2];
  struct intervals intervals;
  struct ring_last last;
  struct ring_limits limits;
  struct options options;
  struct reluctant reluctant;
  struct ring_profiles profiles;
  struct ring_statistics statistics;

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

#define all_phases(PHASE) \
  struct phases * PHASE = ring->phases, \
                  * END_ ## PHASE = PHASE + ring->size; \
  (PHASE != END_ ## PHASE); \
  ++PHASE

#define all_averages(AVG) \
  struct average * AVG = (struct average*) &ring->averages, \
  * END_ ## AVG = (struct average*) ((char*) AVG + sizeof ring->averages); \
  AVG != END_ ## AVG; \
  ++AVG

#define all_watchers(WATCHER) \
  struct watcher * WATCHER = ring->watchers.begin + 1, \
                  * END_ ## WATCHER = ring->watchers.end; \
  (WATCHER != END_ ## WATCHER); \
  ++WATCHER

#define all_redundant_watchers(WATCHER) \
  struct watcher * WATCHER = ring->watchers.begin + ring->redundant, \
                  * END_ ## WATCHER = ring->watchers.end; \
  (WATCHER != END_ ## WATCHER); \
  ++WATCHER

/*------------------------------------------------------------------------*/

void init_ring (struct ring *);
void release_ring (struct ring *, bool keep_values);

struct ring *new_ring (struct ruler *);
void delete_ring (struct ring *);

void init_pool (struct ring *, unsigned threads);

void mark_satisfied_watchers_as_garbage (struct ring *);

void inc_clauses (struct ring *ring, bool redundant);
void dec_clauses (struct ring *ring, bool redundant);

void set_inconsistent (struct ring *, const char *msg);
void set_satisfied (struct ring *);

void print_ring_profiles (struct ring *);

/*------------------------------------------------------------------------*/

static inline unsigned
watcher_to_index (struct ring *ring, struct watcher *watcher)
{
  assert (ring->watchers.begin <= watcher);
  assert (watcher < ring->watchers.end);
  size_t idx = watcher - ring->watchers.begin;
  assert (idx <= MAX_WATCHER_INDEX);
  assert (idx <= UINT_MAX);
  return idx;
}

static inline struct watcher *
index_to_watcher (struct ring *ring, unsigned idx)
{
  return &PEEK (ring->watchers, idx);
}


static inline struct watcher *
get_watcher (struct ring *ring, struct watch *watch)
{
  assert (!is_binary_pointer (watch));
  size_t idx = index_pointer (watch);
  return &PEEK (ring->watchers, idx);
}

static inline struct clause *
get_clause (struct ring *ring, struct watch *watch)
{
  assert (watch);
  return get_watcher (ring, watch)->clause;
}

/*------------------------------------------------------------------------*/

static inline void
push_watch (struct ring *ring, unsigned lit, struct watch *watch)
{
  LOGWATCH (watch, "watching %s in", LOGLIT (lit));
  PUSH (REFERENCES (lit), watch);
}

static inline void
watch_literal (struct ring *ring,
	       unsigned lit, unsigned other, struct watcher *watcher)
{
  unsigned idx = watcher_to_index (ring, watcher);
  struct watch *watch = tag_index (watcher->redundant, idx, other);
  push_watch (ring, lit, watch);
}

/*------------------------------------------------------------------------*/

#endif
