#ifndef _options_h_INCLUDED
#define _options_h_INCLUDED

#include "file.h"

#include <limits.h>
#include <stdbool.h>

#define MAX_VAR ((1u<<30) - 1)
#define MAX_LIT NOT (LIT (MAX_VAR))

#define MAX_GLUE 255

#define INITIAL_PHASE 1

#define MINIMIZE_DEPTH 1000

#define MODE_INTERVAL 3e3

#define REDUCE_INTERVAL 1e3
#define REDUCE_FRACTION 0.75

#define REPHASE_INTERVAL 1e3

#define STABLE_RESTART_INTERVAL 500
#define FOCUSED_RESTART_INTERVAL 50

#define RANDOM_DECISIONS 100

#define DECAY 0.95
#define MAX_SCORE 1e150

#define TIER1_GLUE_LIMIT 2
#define TIER2_GLUE_LIMIT 6

#define FAST_ALPHA 3e-2
#define SLOW_ALPHA 1e-5
#define RESTART_MARGIN 1.1

#define WALK_EFFORT 0.02

#define CACHE_LINE_SIZE 128

#define SIMPLIFICATION_ROUNDS 16
#define CLAUSE_SIZE_LIMIT 100
#define OCCURRENCE_LIMIT 1000

#define SUBSUMPTION_TICKS_LIMIT 2000
#define ELIMINATION_TICKS_LIMIT 2000

#define LD_MAX_ELIMINATE_MARGIN 4

#define MAX_THREADS (1u<<16)

#define FAILED_EFFORT 0.02
#define VIVIFY_EFFORT 0.01
#define PROBING_INTERVAL 2000

#define OPTIONS \
OPTION (bool,	binary,		1, 0, 1) \
OPTION (bool,	deduplicate,	1, 0, 1) \
OPTION (bool,	eliminate,	1, 0, 1) \
OPTION (bool,	fail,		1, 0, 1) \
OPTION (bool,	force,		0, 0, 1) \
OPTION (bool,	inprocessing,	1, 0, 1) \
OPTION (bool,	preprocessing,	1, 0, 1) \
OPTION (bool,	probe,		1, 0, 1) \
OPTION (bool,	simplify,	1, 0, 1) \
OPTION (bool,	substitute,	1, 0, 1) \
OPTION (bool,	subsume,	1, 0, 1) \
OPTION (bool,	vivify,		1, 0, 1) \
OPTION (bool,	walk,		1, 0, 1) \
OPTION (bool,	walk_initially,	0, 0, 1) \
OPTION (bool,	witness,	1, 0, 1) \

struct options
{
  long long conflicts;
  unsigned seconds;
  unsigned threads;

  unsigned optimize;

  struct {
    unsigned reduce;
    unsigned probe;
  } interval;

#define OPTION(TYPE,NAME,DEFAULT,MIN,MAX) \
  TYPE NAME;
  OPTIONS
#undef OPTION

  struct file dimacs;
  struct file proof;
};

void parse_options (int argc, char **argv, struct options *);

void normalize_options (struct options *);
void initialize_options (struct options *);

#endif
