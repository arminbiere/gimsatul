#ifndef _ring_h_INCLUDED
#define _ring_h_INCLUDED

#include "options.h"
#include "profile.h"
#include "queue.h"
#include "stack.h"
#include "watches.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

struct ruler;

struct average
{
  double value, biased, exp;
};

struct reluctant
{
  uint64_t u, v;
};

struct ring_limits
{
  uint64_t mode;
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
  struct profile focused;
  struct profile search;
  struct profile stable;
  struct profile walk;

  struct profile solving;
};

struct ring_last
{
  unsigned fixed;
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
  uint64_t conflicts;
  uint64_t decisions;
  uint64_t propagations;
  uint64_t ticks;
};

#define SEARCH_CONTEXT 0
#define WALK_CONTEXT 1
#define SIZE_CONTEXTS 2

struct ring_statistics
{
  uint64_t flips;
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
  unsigned fixed;

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
  unsigned context;
  unsigned level;
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
  struct queue queue;
  struct unsigneds clause;
  struct unsigneds analyzed;
  struct ring_trail trail;
  struct ring_limits limits;
  struct buffer buffer;
  struct intervals intervals;
  struct averages averages[2];
  struct reluctant reluctant;
  struct ring_statistics statistics;
  struct ring_profiles profiles;
  struct ring_last last;
  uint64_t random;
};

/*------------------------------------------------------------------------*/

void print_line_without_acquiring_lock (struct ring *, const char *, ...)
__attribute__((format (printf, 2, 3)));

void message (struct ring *ring, const char *, ...)
  __attribute__((format (printf, 2, 3)));

#define PRINTLN(...) \
  print_line_without_acquiring_lock (ring, __VA_ARGS__)

/*------------------------------------------------------------------------*/

#endif
