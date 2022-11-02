#ifndef _statistics_h_INCLUDED
#define _statistics_h_INCLUDED

#include <stdint.h>

/*------------------------------------------------------------------------*/

struct ring;
struct ruler;

/*------------------------------------------------------------------------*/

#ifdef METRICS
#define SIZE_VISITS 16
#endif

struct context
{
  uint64_t ticks;
  uint64_t propagations;
  uint64_t conflicts;
  uint64_t decisions;
#ifdef METRICS
  uint64_t visits[SIZE_VISITS];
#endif
};

struct ring_statistics
{
  uint64_t flips;
  uint64_t probings;
  uint64_t reductions;
  uint64_t rephased;
  uint64_t restarts;
  uint64_t simplifications;
  uint64_t switched;
  uint64_t walked;

#define SEARCH_CONTEXT 0
#define PROBING_CONTEXT 1
#define WALK_CONTEXT 2
#define SIZE_CONTEXTS 3

  struct context contexts[SIZE_CONTEXTS];

  struct
  {
    uint64_t learned;
#ifdef METRICS
    uint64_t deduced;
    uint64_t minimized;
    uint64_t shrunken;
#endif
  } literals;

  unsigned active;
  unsigned failed;
  unsigned fixed;
  unsigned lifted;

  size_t irredundant;
  size_t redundant;

  struct
  {
    uint64_t tried;
    uint64_t reused;
    uint64_t succeeded;
  } vivify;

  struct
  {
    uint64_t heap;
    uint64_t negative;
    uint64_t positive;
    uint64_t queue;
    uint64_t random;
  } decisions;

  uint64_t random_sequences;

#define SIZE_GLUE_STATISTICS 16

  uint64_t diverged;

  struct
  {
    uint64_t units;
    uint64_t clauses;
    uint64_t binaries;
    uint64_t tier1, tier2, tier3;
#ifdef METRICS
    uint64_t glue[SIZE_GLUE_STATISTICS];
#endif
  } learned, exported, imported, shared;

  struct
  {
    struct
    {
      uint64_t checked;
      uint64_t succeeded;
    } binary, large;
  } subsumed;
};

#ifdef METRICS

#define ADD_CLAUSE_METRICS(NAME,INC,GLUE,SIZE) \
do { \
  if ((GLUE) < SIZE_GLUE_STATISTICS) \
    S->NAME.glue[(GLUE)] += (INC); \
  else \
    S->NAME.glue[0] += (INC); \
} while (0)

#else

#define ADD_CLAUSE_METRICS(...) do { } while (0)

#endif

#define ADD_CLAUSE_STATISTICS(NAME,INC,GLUE,SIZE) \
do { \
  struct ring_statistics * S = &ring->statistics; \
  if ((SIZE) == 1) \
    { \
      /* NOTE: units are NOT clauses */ \
      assert (!(GLUE)); \
      S->NAME.units += (INC); \
    } \
  else \
    { \
      assert ((GLUE) > 0); \
      assert ((SIZE) > 1); \
      S->NAME.clauses += (INC); \
      if ((SIZE) == 2) \
	{ \
          /* NOTE: binaries ARE clauses */ \
          /* NOTE: binaries ARE tier1 clauses too */ \
	  assert ((GLUE) == 1); \
	  S->NAME.binaries += (INC); \
	} \
      if ((GLUE) <= TIER1_GLUE_LIMIT) \
	S->NAME.tier1 += (INC); \
      else if ((GLUE) <= TIER2_GLUE_LIMIT) \
	S->NAME.tier2 += (INC); \
      else \
	S->NAME.tier3 += (INC); \
      ADD_CLAUSE_METRICS (NAME, (INC), (GLUE), (SIZE)); \
    } \
} while (0)

#define INC_UNIT_CLAUSE_STATISTICS(NAME) \
  ADD_CLAUSE_STATISTICS (NAME, 1, 0, 1)

#define INC_CLAUSE_STATISTICS(NAME,GLUE,SIZE) \
  ADD_CLAUSE_STATISTICS (NAME, 1, (GLUE), (SIZE))

#define ADD_BINARY_CLAUSE_STATISTICS(NAME,INC) \
  ADD_CLAUSE_STATISTICS (NAME, (INC), 1, 2)

#define ADD_LARGE_CLAUSE_STATISTICS(NAME,INC,GLUE) \
  ADD_CLAUSE_STATISTICS (NAME, (INC), (GLUE), 3)

#define INC_BINARY_CLAUSE_STATISTICS(NAME) \
  ADD_BINARY_CLAUSE_STATISTICS (NAME, 1)

#define INC_LARGE_CLAUSE_STATISTICS(NAME,GLUE) \
  ADD_LARGE_CLAUSE_STATISTICS (NAME, 1, (GLUE))

#define SEARCH_CONFLICTS \
  ring->statistics.contexts[SEARCH_CONTEXT].conflicts

#define SEARCH_DECISIONS \
  ring->statistics.contexts[SEARCH_CONTEXT].decisions

#define SEARCH_TICKS \
  ring->statistics.contexts[SEARCH_CONTEXT].ticks

#define PROBING_TICKS \
  ring->statistics.contexts[PROBING_CONTEXT].ticks

struct ruler_statistics
{
  uint64_t garbage;
  uint64_t binaries;
  unsigned active;
  unsigned original;
  uint64_t deduplicated;
  unsigned eliminated;
  unsigned definitions;
  uint64_t strengthened;
  uint64_t subsumed;
  uint64_t substituted;
  uint64_t selfsubsumed;
  uint64_t simplifications;
  size_t weakened;
  struct
  {
    uint64_t elimination;
    uint64_t subsumption;
  } ticks;
  struct
  {
    unsigned simplifying;
    unsigned solving;
    unsigned total;
  } fixed;
};

/*------------------------------------------------------------------------*/
#ifndef QUIET

void print_ring_statistics (struct ring *);
void print_ruler_statistics (struct ruler *);

#endif
/*------------------------------------------------------------------------*/

#endif
