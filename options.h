#ifndef _options_h_INCLUDED
#define _options_h_INCLUDED

#include <limits.h>
#include <stdbool.h>

#define MAX_VAR ((1u<<30) - 1)
#define MAX_LIT NOT (LIT (MAX_VAR))

#define MAX_GLUE 255

#define FREE (UINT_MAX-1)
#define INVALID UINT_MAX

#define MAX_SCORE 1e150
#define MINIMIZE_DEPTH 1000

#define FOCUSED_RESTART_INTERVAL 50
#define MODE_INTERVAL 3e3

#if 1
#define REDUCE_INTERVAL 1e3
#else
#define REDUCE_INTERVAL 1
#endif

#define REPHASE_INTERVAL 1e3
#define STABLE_RESTART_INTERVAL 500
#define RANDOM_DECISIONS 100

#define FOCUSED_DECAY 0.75
#define REDUCE_FRACTION 0.75
#define STABLE_DECAY 0.95
#define TIER1_GLUE_LIMIT 2
#define TIER2_GLUE_LIMIT 6

#define FAST_ALPHA 3e-2
#define SLOW_ALPHA 1e-5
#define RESTART_MARGIN 1.1

#define WALK_EFFORT 0.02
#define INITIAL_PHASE 1

#define CACHE_LINE_SIZE 128

#define SIMPLIFICATION_ROUNDS 16
#define CLAUSE_SIZE_LIMIT 100
#define OCCURRENCE_LIMIT 1000

#define SUBSUMPTION_TICKS_LIMIT 2000
#define ELIMINATION_TICKS_LIMIT 2000

#define LD_MAX_MARGIN 4

struct options
{
  long long conflicts;
  unsigned seconds;
  unsigned threads;
  unsigned optimize;
  bool no_walk;
  bool no_simplify;
  bool walk_initially;
};

#endif
