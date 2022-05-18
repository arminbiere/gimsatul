#ifndef _options_h_INCLUDED
#define _options_h_INCLUDED

#include "file.h"

#include <limits.h>
#include <stdbool.h>

#define MAX_VAR ((1u<<30) - 1)
#define MAX_LIT NOT (LIT (MAX_VAR))

#define MAX_GLUE 255

#define MINIMIZE_DEPTH 1000

#define MODE_INTERVAL 3e3

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

#define OPTIONS \
OPTION (bool,     binary,          1, 0, 1) \
OPTION (bool,     deduplicate,     1, 0, 1) \
OPTION (bool,     eliminate,       1, 0, 1) \
OPTION (bool,     fail,            1, 0, 1) \
OPTION (bool,     focus_initially, 1, 0, 1) \
OPTION (bool,     force,           0, 0, 1) \
OPTION (bool,     inprocessing,    1, 0, 1) \
OPTION (bool,     phase,           1, 0, 1) \
OPTION (bool,     portfolio,       1, 0, 1) \
OPTION (bool,     preprocessing,   1, 0, 1) \
OPTION (bool,     probe,           1, 0, 1) \
OPTION (unsigned, probe_interval,  2e3, 1, INT_MAX) \
OPTION (unsigned, reduce_interval, 1e3, 1, INT_MAX) \
OPTION (bool,     simplify,        1, 0, 1) \
OPTION (bool,     switch_mode,     1, 0, 1) \
OPTION (bool,     substitute,      1, 0, 1) \
OPTION (bool,     subsume,         1, 0, 1) \
OPTION (bool,     vivify,          1, 0, 1) \
OPTION (bool,     walk_initially,  0, 0, 1) \
OPTION (bool,     witness,         1, 0, 1) \

struct options
{
  long long conflicts;
  unsigned seconds;
  unsigned threads;

  unsigned optimize;

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
const char * match_and_find_option_argument (const char *, const char *);
bool parse_option_with_value (struct options *, const char *);
void report_non_default_options (struct options *);
void print_usage_of_options (void);

#endif
