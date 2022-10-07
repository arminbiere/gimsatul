#ifndef _options_h_INCLUDED
#define _options_h_INCLUDED

#include "file.h"

#include <limits.h>
#include <stdbool.h>

/*------------------------------------------------------------------------*/

#define INVALID_VAR ((1u<<30) - 1)
#define MAX_VAR (INVALID_VAR - 1)
#define INVALID_LIT ((1u << 31) - 1)
#define MAX_LIT NOT (LIT (MAX_VAR))
#define MAX_WATCHER_INDEX ((1u << 31) - 1)

#define MAX_GLUE 255
#define MAX_SCORE 1e150
#define MAX_THREADS (1u<<16)

#define CACHE_LINE_SIZE 128

/*------------------------------------------------------------------------*/

#define DECAY 0.95

#define FAST_ALPHA 3e-2
#define SLOW_ALPHA 1e-5

#define TIER1_GLUE_LIMIT 2
#define TIER2_GLUE_LIMIT 6

#define REDUCE_FRACTION 0.75

#define RESTART_MARGIN 1.1
#define STABLE_RESTART_INTERVAL (1<<10)
#define MAX_STABLE_RESTART_INTERVAL (1<<20)
#define FOCUSED_RESTART_INTERVAL 1

#define ELIMINATE_EFFORT 0.10
#define FAILED_EFFORT 0.02
#define SUBSUME_EFFORT 0.10
#define VIVIFY_EFFORT 0.10
#define RELATIVE_VIVIFY_TIER1_EFFORT 1
#define RELATIVE_VIVIFY_TIER2_EFFORT 3

#define VIVIFY_CLAUSE_SIZE_LIMIT 16

#define WALK_EFFORT 0.02

/*------------------------------------------------------------------------*/

#define INF INT_MAX

#define OPTIONS \
OPTION (bool,     binary,                1, 0, 1,     "use binary DRAT proof format") \
OPTION (bool,     bump_reasons,          1, 0, 1,     "bump reason side literals") \
OPTION (unsigned, clause_size_limit,     100,3,10000,"during simplification") \
OPTION (bool,     deduplicate,           1, 0, 1,     "remove duplicated binary clauses") \
OPTION (bool,     eliminate,             1, 0, 1,     "bounded variable elimination") \
OPTION (unsigned, eliminate_bound,       16, 0, 1024, "additionally added clause margin") \
OPTION (unsigned, eliminate_ticks,       20, 0, INF,  "elimination ticks limit in millions") \
OPTION (bool,     fail,                  1, 0, 1,     "failed literal probing") \
OPTION (bool,     focus_initially,       1, 0, 1,     "start with focus mode initially") \
OPTION (bool,     force,                 0, 0, 1,     "force relaxed parsing and proof writing") \
OPTION (unsigned, maximum_shared_glue,   8, 0, 15,    "share 0=binary 1=glue1 2=glue2 ... clauses") \
OPTION (bool,     minimize,              1, 0, 1,     "minimize learned clauses") \
OPTION (unsigned, minimize_depth,        1000,1,INF,  "recursive clause minimization depth") \
OPTION (unsigned, occurrence_limit,      1000,0,INF,  "literal occurrence limit in simplification") \
OPTION (bool,     phase,                 1, 0, 1,     "initial decision phase") \
OPTION (bool,     portfolio,             1, 0, 1,     "threads use different strategies") \
OPTION (bool,     probe,                 1, 0, 1,     "enable probing based inprocessing") \
OPTION (unsigned, probe_interval,        100, 1, INF, "probing base conflict interval") \
OPTION (unsigned, random_decisions,      100, 0, INF, "initial random decisions") \
OPTION (bool,     random_order,          0, 0, 1,     "initial random decision order") \
OPTION (unsigned, reduce_interval,       1e3, 1, INF, "reduce base conflict interval") \
OPTION (bool,     rephase,               1, 0, 1,     "reset saved phases regularly") \
OPTION (unsigned, rephase_interval,      1e3, 1, INF, "base rephase conflict interval") \
OPTION (unsigned, report,                1, 0, INF,   "report details for many threads") \
OPTION (bool,     share_learned,         1, 0, 1,     "export and import learned clauses") \
OPTION (bool,     shrink,                1, 0, 1,     "shrink (glue 1) learned clauses") \
OPTION (bool,     simplify,              1, 0, 1,     "elimination, subsumption and substitution") \
OPTION (unsigned, simplify_boost,        1, 0, 1,     "additional initial boost to simplification") \
OPTION (unsigned, simplify_boost_rounds, 4, 2, INF,   "initial increase rounds limit") \
OPTION (unsigned, simplify_boost_ticks,  10, 2, INF,  "initial increase of ticks limits") \
OPTION (unsigned, simplify_interval,     500, 1, INF, "simplification base conflict interval") \
OPTION (bool,     simplify_initially,    1, 0, 1,     "initial preprocessing through simplification") \
OPTION (bool,     simplify_regularly,    1, 0, 1,     "regular inprocessing through simplification") \
OPTION (unsigned, simplify_rounds,       4, 1, INF,   "number of rounds per simplification") \
OPTION (bool,     sort_deduced,          0, 0, 1,     "sort deduced clause") \
OPTION (bool,     switch_mode,           1, 0, 1,     "switch between focused and stable mode") \
OPTION (unsigned, switch_interval,       1e3, 1, INF, "mode switching base conflict interval") \
OPTION (bool,     substitute,            1, 0, 1,     "equivalent literal substitution") \
OPTION (bool,     subsume,               1, 0, 1,     "clause subsumption and strengthening") \
OPTION (bool,     subsume_imported,      1, 0, 1,     "subsume imported clauses") \
OPTION (unsigned, subsume_ticks,         20, 0, INF,  "subsumption ticks limit in millions") \
OPTION (unsigned, target_phases,         1, 0, 2,     "target phases (2 = in focused mode too)") \
OPTION (bool,     vivify,                1, 0, 1,     "vivification of redundant clauses") \
OPTION (bool,     walk_initially,        0, 0, 1,     "local search initially") \
OPTION (bool,     warm_up_walking,       1, 0, 1,     "unit propagation warm-up of local search") \
OPTION (bool,     witness,               1, 0, 1,     "print satisfying assignment") \

struct options
{
  long long conflicts;
  unsigned seconds;
  unsigned threads;
  unsigned optimize;
  bool summarize;

#define OPTION(TYPE,NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
  TYPE NAME;
    OPTIONS
#undef OPTION
  struct file dimacs;
  struct file proof;
};

/*------------------------------------------------------------------------*/

void parse_options (int argc, char **argv, struct options *);
const char *match_and_find_option_argument (const char *, const char *);
bool parse_option_with_value (struct options *, const char *);
void report_non_default_options (struct options *);

#endif
