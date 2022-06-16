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
    uint64_t strengthened;
    uint64_t succeeded;
    uint64_t implied;
  } vivify;

#define SIZE_GLUE_STATISTICS 16

  struct
  {
    uint64_t FIXunits;
    uint64_t FIXclauses;
    uint64_t FIXbinaries;
    uint64_t FIXtier1, FIXtier2, FIXtier3;
    uint64_t FIXglue[SIZE_GLUE_STATISTICS];
  } learned, exported, imported;
};

#define INC_CLAUSE_STATISTICS(NAME,GLUE,SIZE) \
do { \
  struct ring_statistics * S = &ring->statistics; \
  if ((SIZE) == 1) \
    { \
      /* NOTE: units are NOT clauses */ \
      assert (!(GLUE)); \
      S->NAME.FIXunits++; \
    } \
  else \
    { \
      assert ((GLUE) > 0); \
      assert ((SIZE) > 1); \
      S->NAME.FIXclauses++; \
      if ((SIZE) == 2) \
	{ \
          /* NOTE: binaries ARE clauses */ \
          /* NOTE: binaries ARE tier1 clauses too */ \
	  assert ((GLUE) == 1); \
	  S->NAME.FIXbinaries++; \
	} \
      if ((GLUE) <= TIER1_GLUE_LIMIT) \
	S->NAME.FIXtier1++; \
      else if ((GLUE) <= TIER2_GLUE_LIMIT) \
	S->NAME.FIXtier2++; \
      else \
	S->NAME.FIXtier3++; \
      if ((GLUE) < SIZE_GLUE_STATISTICS) \
	S->NAME.FIXglue[(GLUE)]++; \
      else \
	S->NAME.FIXglue[0]++; \
    } \
} while (0)

#define INC_UNIT_CLAUSE_STATISTICS(NAME) \
do { \
  INC_CLAUSE_STATISTICS (NAME, 0, 1); \
} while (0)

#define INC_BINARY_CLAUSE_STATISTICS(NAME) \
do { \
  INC_CLAUSE_STATISTICS (NAME, 1, 2); \
} while (0)

#define INC_LARGE_CLAUSE_STATISTICS(NAME,GLUE) \
do { \
  INC_CLAUSE_STATISTICS (NAME, GLUE, 3); \
} while (0)

#define SEARCH_CONFLICTS \
  ring->statistics.contexts[SEARCH_CONTEXT].conflicts

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
