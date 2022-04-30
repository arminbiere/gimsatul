// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimsatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-a|--ascii       use ASCII format for proof output\n"
"-f|--force       force reading and writing\n"
"-h|--help        print this command line option summary\n"
#ifdef LOGGING   
"-l|--log[ging]   enable very verbose internal logging\n"
#endif
"-n|--no-witness  do not print satisfying assignments\n"
"-v|--verbose     increase verbosity\n"
"--version        print version\n"
"\n"
"--conflicts=<conflicts>  limit conflicts (zero or more - default unlimited)\n"
"--threads=<number>       set number of threads (1 ... %zu - default '1')\n"
"--time=<seconds>         limit time (1,2,3, ... - default unlimited)\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof output file in 'DRAT' format (no proof if missing).\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

#define MAX_VAR ((1u<<30) - 1)
#define MAX_LIT NOT (LIT (MAX_VAR))

#define FREE (UINT_MAX-1)
#define INVALID UINT_MAX

#define MAX_SCORE 1e150
#define MAX_VERBOSITY 3
#define MINIMIZE_DEPTH 1000

#define FOCUSED_RESTART_INTERVAL 50
#define MODE_INTERVAL 3e3
#define REDUCE_INTERVAL 1e3
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

#define WALK_EFFORT 0.01
#define INITIAL_PHASE 1

/*------------------------------------------------------------------------*/

#define IDX(LIT) ((LIT) >> 1)
#define LIT(IDX) ((IDX) << 1)
#define NOT(LIT) ((LIT) ^ 1u)
#define SGN(LIT) ((LIT) & 1)

#define VAR(LIT) (solver->variables + IDX (LIT))

#define REFERENCES(LIT) (solver->references[LIT])
#define OCCS(LIT) (walker->occs[LIT])

#define MAX_THREADS \
  ((size_t) 1 << 8*sizeof ((struct clause *) 0)->shared)

/*------------------------------------------------------------------------*/

#define SIZE(STACK) ((size_t)((STACK).end - (STACK).begin))

#define CAPACITY(STACK) ((size_t)((STACK).allocated - (STACK).begin))

#define EMPTY(STACK) ((STACK).end == (STACK).begin)

#define FULL(STACK) ((STACK).end == (STACK).allocated)

#define INIT(STACK) \
do { \
  (STACK).begin = (STACK).end = (STACK).allocated = 0; \
} while (0)

#define RELEASE(STACK) \
do { \
  free ((STACK).begin); \
  INIT (STACK); \
} while (0)

#define ENLARGE(STACK) \
do { \
  size_t OLD_SIZE = SIZE (STACK); \
  size_t OLD_CAPACITY = CAPACITY (STACK); \
  size_t NEW_CAPACITY = OLD_CAPACITY ? 2*OLD_CAPACITY : 1; \
  size_t NEW_BYTES = NEW_CAPACITY * sizeof *(STACK).begin; \
  (STACK).begin = reallocate_block ((STACK).begin, NEW_BYTES); \
  (STACK).end = (STACK).begin + OLD_SIZE; \
  (STACK).allocated = (STACK).begin + NEW_CAPACITY; \
} while (0)

#define PUSH(STACK,ELEM) \
do { \
  if (FULL (STACK)) \
    ENLARGE (STACK); \
  *(STACK).end++ = (ELEM); \
} while (0)

#define SHRINK(STACK) \
do { \
  size_t OLD_SIZE = SIZE (STACK); \
  if (!OLD_SIZE) \
    { \
      RELEASE (STACK); \
      break; \
    } \
  size_t OLD_CAPACITY = CAPACITY (STACK); \
  if (OLD_CAPACITY == OLD_SIZE) \
    break; \
  size_t NEW_CAPACITY = OLD_SIZE; \
  size_t NEW_BYTES = NEW_CAPACITY * sizeof *(STACK).begin; \
  (STACK).begin = reallocate_block ((STACK).begin, NEW_BYTES); \
  (STACK).end = (STACK).allocated = (STACK).begin + OLD_SIZE; \
} while (0)

#define CLEAR(STACK) \
do { \
  (STACK).end = (STACK).begin; \
} while (0)

#define TOP(STACK) \
  (assert (!EMPTY (STACK)), (STACK).end[-1])

#define POP(STACK) \
  (assert (!EMPTY (STACK)), *--(STACK).end)

/*------------------------------------------------------------------------*/

#define all_elements_on_stack(TYPE,ELEM,STACK) \
  TYPE * P_ ## ELEM = (STACK).begin, * END_ ## ELEM = (STACK).end, ELEM; \
  (P_ ## ELEM != END_ ## ELEM) && ((ELEM) = *P_ ## ELEM, true); \
  ++P_ ## ELEM

#define all_watches(ELEM,WATCHES) \
  struct watch ** P_ ## ELEM = (WATCHES).begin, \
               ** END_ ## ELEM = (WATCHES).end, * ELEM; \
  (P_ ## ELEM != END_ ## ELEM) && ((ELEM) = *P_ ## ELEM, true); \
  ++P_ ## ELEM

#define all_counters(ELEM,COUNTERS) \
  struct counter ** P_ ## ELEM = (COUNTERS).begin, \
               ** END_ ## ELEM = (COUNTERS).end, * ELEM; \
  (P_ ## ELEM != END_ ## ELEM) && ((ELEM) = *P_ ## ELEM, true); \
  ++P_ ## ELEM

#define all_variables(VAR) \
  struct variable * VAR = solver->variables, \
                  * END_ ## VAR = VAR + solver->size; \
  (VAR != END_ ## VAR); \
  ++ VAR

#define all_literals_on_trail(LIT) \
  unsigned * P_ ## LIT = solver->trail.begin, \
           * END_ ## LIT = solver->trail.end, LIT; \
  P_ ## LIT != END_ ## LIT && (LIT = *P_ ## LIT, true); \
  ++ P_ ## LIT

#define all_nodes(NODE) \
  struct node * NODE = solver->queue.nodes, \
              * END_ ## NODE = (NODE) + solver->size; \
  NODE != END_ ## NODE; \
  ++NODE

#define all_indices(IDX) \
  unsigned IDX = 0, END_ ## IDX = solver->size; \
  IDX != END_ ## IDX; \
  ++IDX

#define all_literals(LIT) \
  unsigned LIT = 0, END_ ## LIT = 2*solver->size; \
  LIT != END_ ## LIT; \
  ++LIT

#define all_literals_in_clause(LIT,CLAUSE) \
  unsigned * P_ ## LIT = (CLAUSE)->literals, \
           * END_ ## LIT = P_ ## LIT + (CLAUSE)->size, LIT;\
  P_ ## LIT != END_ ## LIT && (LIT = *P_ ## LIT, true); \
  ++ P_ ## LIT

#define all_averages(AVG) \
  struct average * AVG = (struct average*) &solver->averages, \
  * END_ ## AVG = (struct average*) ((char*) AVG + sizeof solver->averages); \
  AVG != END_ ## AVG; \
  ++AVG

#define all_solvers(SOLVER) \
  struct solver ** P_ ## SOLVER = root->solvers.begin, \
                ** END_ ## SOLVER = root->solvers.end, * SOLVER; \
  (P_ ## SOLVER != END_ ## SOLVER) && ((SOLVER) = *P_ ## SOLVER, true); \
  ++P_ ## SOLVER

/*------------------------------------------------------------------------*/

struct file
{
  const char *path;
  FILE *file;
  int close;
  uint64_t lines;
};

struct unsigneds
{
  unsigned *begin, *end, *allocated;
};

struct buffer
{
  unsigned char *begin, *end, *allocated;
};

struct trail
{
  unsigned *begin, *end, *propagate;
};

#define MAX_GLUE 255

struct clause
{
#ifdef LOGGING
  uint64_t id;
#endif
  atomic_ushort shared;
  unsigned char glue;
  bool redundant;
  unsigned size;
  unsigned literals[];
};

struct clauses
{
  struct clause **begin, **end, **allocated;
};

struct watch
{
  unsigned short used;
  unsigned char glue;
  bool garbage:1;
  bool reason:1;
  bool redundant:1;
  unsigned middle;
  unsigned sum;
  struct clause *clause;
};

struct watches
{
  struct watch ** begin, **end, **allocated;
};

struct references
{
  struct watch ** begin, **end, **allocated;
  unsigned *binaries;
};

struct variable
{
  unsigned level;
  signed char best;
  signed char saved;
  signed char target;
  bool minimize:1;
  bool poison:1;
  bool seen:1;
  struct watch *reason;
};

struct node
{
  double score;
  struct node *child, *prev, *next;
};

struct reluctant
{
  uint64_t u, v;
};

struct queue
{
  double increment[2];
  struct node *nodes;
  struct node *root;
  double *scores;
};

struct limits
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

struct average
{
  double value, biased, exp;
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

struct profile
{
  double time;
  const char *name;
  double start;
  int level;
};

struct profiles
{
  struct profile focused;
  struct profile search;
  struct profile stable;
  struct profile walk;

  struct profile total;
};

struct last
{
  unsigned fixed;
  uint64_t walk;
};

#define SEARCH 0
#define WALK 1
#define CONTEXTS 2

#define SEARCH_CONFLICTS solver->statistics.contexts[SEARCH].conflicts
#define SEARCH_PROPAGATIONS solver->statistics.contexts[SEARCH].propagations
#define SEARCH_TICKS solver->statistics.contexts[SEARCH].ticks

struct context
{
  uint64_t conflicts;
  uint64_t decisions;
  uint64_t propagations;
  uint64_t ticks;
};

struct statistics
{
  uint64_t flips;
  uint64_t reductions;
  uint64_t rephased;
  uint64_t restarts;
  uint64_t switched;
  uint64_t walked;

  struct context contexts[CONTEXTS];

  uint64_t deduced;
  uint64_t minimized;
#ifdef LOGGING
  uint64_t ids;
#endif

  unsigned fixed;

  size_t irredundant;
  size_t redundant;

  struct
  {
    uint64_t units;
    uint64_t binary;
    uint64_t clauses;
    uint64_t glue1;
    uint64_t literals;
    uint64_t tier1;
    uint64_t tier2;
    uint64_t tier3;
  } learned, exported, imported;
};

struct binaries
{
  struct unsigneds redundant;
  struct unsigneds irredundant;
};

struct solvers
{
  pthread_mutex_t lock;
  struct solver ** begin, ** end, **allocated;
};

struct units
{
  pthread_mutex_t lock;
  unsigned * begin;
  volatile unsigned * end;
};

struct root
{
  unsigned size;
  volatile bool terminate;
  struct solvers solvers;
  volatile struct solver *winner;
  volatile signed char * values;
  struct unsigneds binaries;
  struct units units;
  unsigned *watches;
};

struct solver
{
  unsigned id;
  struct root *root;
  pthread_t thread;
  volatile struct watch * share;
  volatile int status;
  bool inconsistent;
  bool iterating;
  bool stable;
  unsigned size;
  unsigned context;
  unsigned active;
  unsigned level;
  unsigned unassigned;
  unsigned target;
  unsigned best;
  bool *used;
  signed char *values;
  struct variable *variables;
  struct watches watches;
  struct references *references;
  struct unsigneds levels;
  struct queue queue;
  struct unsigneds clause;
  struct unsigneds analyzed;
  struct buffer buffer;
  struct trail trail;
  unsigned * units;
  struct last last;
  struct limits limits;
  struct intervals intervals;
  struct averages averages[2];
  struct reluctant reluctant;
  struct statistics statistics;
  struct profiles profiles;
  uint64_t random;
};

/*------------------------------------------------------------------------*/

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

static double
percent (double a, double b)
{
  return average (100 * a, b);
}

/*------------------------------------------------------------------------*/

static double
process_time (void)
{
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static double
current_time (void)
{
  struct timeval tv;
  if (gettimeofday (&tv, 0))
    return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

static double start_time;

static double
wall_clock_time (void)
{
  return current_time () - start_time;
}

static size_t
maximum_resident_set_size (void)
{
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  return ((size_t) u.ru_maxrss) << 10;
}

static size_t
current_resident_set_size (void)
{
  char path[48];
  sprintf (path, "/proc/%d/statm", (int) getpid ());
  FILE *file = fopen (path, "r");
  if (!file)
    return 0;
  size_t dummy, rss;
  int scanned = fscanf (file, "%zu %zu", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

/*------------------------------------------------------------------------*/

static void
update_average (struct average *average, double alpha, double y)
{
  double beta = 1 - alpha;
  double old_biased = average->biased;
  double delta = y - old_biased;
  double scaled_delta = alpha * delta;
  double new_biased = old_biased + scaled_delta;
  average->biased = new_biased;
  double old_exp = average->exp;
  double new_value;
  if (old_exp)
    {
      double new_exp = old_exp * beta;
      average->exp = new_exp;
      double div = 1 - new_exp;
      new_value = new_biased / div;
    }
  else
    new_value = new_biased;
  average->value = new_value;
}

/*------------------------------------------------------------------------*/

static int
export_literal (unsigned unsigned_lit)
{
  int signed_lit = unsigned_lit / 2 + 1;
  if (SGN (unsigned_lit))
    signed_lit *= -1;
  return signed_lit;
}

/*------------------------------------------------------------------------*/

static pthread_mutex_t message_mutex = PTHREAD_MUTEX_INITIALIZER;

static void
message_lock_failure (const char * str)
{
  char buffer[128];
  sprintf (buffer, "gimsatul: fatal message locking error: %s\n", str);
  size_t len = strlen (buffer);
  assert (len < sizeof buffer);
  if (write (1, buffer, len) != len)
    abort ();
  abort ();
}

static void
acquire_message_lock (void)
{
  if (pthread_mutex_lock (&message_mutex))
    message_lock_failure ("failed to acquire message lock");
}

static void
release_message_lock (void)
{
  if (pthread_mutex_unlock (&message_mutex))
    message_lock_failure ("failed to release message lock");
}

static void die (const char *, ...) __attribute__((format (printf, 1, 2)));

static void
die (const char *fmt, ...)
{
  acquire_message_lock ();
  fputs ("gimsatul: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  release_message_lock ();
  exit (1);
}

static void fatal_error (const char *, ...)
  __attribute__((format (printf, 1, 2)));

static void
fatal_error (const char *fmt, ...)
{
  acquire_message_lock ();
  fputs ("gimsatul: fatal error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  release_message_lock ();
  abort ();
}

static void
print_without_acquiring_lock (struct solver *, const char *, ...)
  __attribute__((format (printf, 2, 3)));

static const char * prefix_format = "c%-2u ";

static void
print_without_acquiring_lock (struct solver * solver, const char * fmt, ...)
{
  va_list ap;
  printf (prefix_format, solver->id);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
}

#define PRINT(...) \
  print_without_acquiring_lock (solver, __VA_ARGS__)

static void message (struct solver *solver, const char *, ...)
  __attribute__((format (printf, 2, 3)));

static void
message (struct solver *solver, const char *fmt, ...)
{
  acquire_message_lock ();
  printf (prefix_format, solver->id);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  release_message_lock ();
}

static int verbosity;

#define verbose(...) \
do { \
  if (verbosity > 1) \
    message (__VA_ARGS__); \
} while (0)

#define very_verbose(...) \
do { \
  if (verbosity > 2) \
    message (__VA_ARGS__); \
} while (0)

#define COVER(COND) \
( \
  (COND) \
  ? \
  \
    ( \
      fflush (stdout), \
      fprintf (stderr, "%s:%ld: %s: Coverage goal `%s' reached.\n", \
	__FILE__, (long) __LINE__, __func__, #COND), \
      abort (), \
      (void) 0 \
    ) \
  : \
    (void) 0 \
)

/*------------------------------------------------------------------------*/

#ifdef LOGGING

static bool logging;
static char loglitbuf[4][64];
static unsigned loglitpos;

#define loglitsize (sizeof loglitbuf / sizeof *loglitbuf)

static char *
next_loglitbuf (void)
{
  char *res = loglitbuf[loglitpos++];
  if (loglitpos == loglitsize)
    loglitpos = 0;
  return res;
}

static const char *
loglit (struct solver *solver, unsigned unsigned_lit)
{
  char *res = next_loglitbuf ();
  int signed_lit = export_literal (unsigned_lit);
  sprintf (res, "%u(%d)", unsigned_lit, signed_lit);
  signed char value = solver->values[unsigned_lit];
  if (value)
    {
      sprintf (res + strlen (res), "=%d", (int) value);
      struct variable *v = VAR (unsigned_lit);
      if (v->level != INVALID)
	sprintf (res + strlen (res), "@%u", v->level);
    }
  assert (strlen (res) + 1 < sizeof *loglitbuf);
  return res;
}

static const char *
logvar (struct solver *solver, unsigned idx)
{
  unsigned lit = LIT (idx);
  const char *tmp = loglit (solver, lit);
  char *res = next_loglitbuf ();
  sprintf (res, "variable %u(%u) (literal %s)", idx, idx + 1, tmp);
  return res;
}

#define LOGVAR(...) logvar (solver, __VA_ARGS__)

#define LOGLIT(...) loglit (solver, __VA_ARGS__)

#define LOGPREFIX(...) \
  if (!logging) \
    break; \
  acquire_message_lock (); \
  printf (prefix_format, solver->id); \
  printf ("LOG %u ", solver->level); \
  printf (__VA_ARGS__)

#define LOGSUFFIX(...) \
  fputc ('\n', stdout); \
  fflush (stdout); \
  release_message_lock ()

#define LOG(...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  LOGSUFFIX (); \
} while (0)

#define LOGTMP(...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  printf (" size %zu temporary clause", SIZE (solver->clause)); \
  for (all_elements_on_stack (unsigned, LIT, solver->clause)) \
    printf (" %s", LOGLIT (LIT)); \
  LOGSUFFIX (); \
} while (0)

#define LOGBINARY(REDUNDANT,LIT,OTHER, ...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  if ((REDUNDANT)) \
    printf (" redundant"); \
  else \
    printf (" irredundant"); \
  printf (" binary clause %s %s", LOGLIT (LIT), LOGLIT (OTHER)); \
  LOGSUFFIX (); \
} while (0)

#define LOGCLAUSE(CLAUSE, ...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  if ((CLAUSE)->redundant) \
    printf (" redundant glue %u", (CLAUSE)->glue); \
  else \
    printf (" irredundant"); \
  printf (" size %u clause[%" PRIu64 "]", \
          (CLAUSE)->size, (uint64_t) (CLAUSE)->id); \
  for (all_literals_in_clause (LIT, (CLAUSE))) \
    printf (" %s", LOGLIT (LIT)); \
  LOGSUFFIX (); \
} while (0)

#define LOGWATCH(WATCH, ...) \
do { \
  if (binary_pointer (WATCH)) \
    { \
      unsigned LIT = lit_pointer (WATCH); \
      unsigned OTHER = other_pointer (WATCH); \
      bool REDUNDANT = redundant_pointer (WATCH); \
      LOGBINARY (REDUNDANT, LIT, OTHER, __VA_ARGS__); \
    } \
  else \
    LOGCLAUSE ((WATCH)->clause, __VA_ARGS__); \
} while (0)

#else

#define LOG(...) do { } while (0)
#define LOGTMP(...) do { } while (0)
#define LOGBINARY(...) do { } while (0)
#define LOGCLAUSE(...) do { } while (0)
#define LOGWATCH(...) do { } while (0)

#endif

/*------------------------------------------------------------------------*/

static void *
allocate_block (size_t bytes)
{
  void *res = malloc (bytes);
  if (bytes && !res)
    fatal_error ("out-of-memory allocating %zu bytes", bytes);
  return res;
}

static void *
allocate_and_clear_block (size_t bytes)
{
  void *res = calloc (1, bytes);
  if (bytes && !res)
    fatal_error ("out-of-memory allocating %zu bytes", bytes);
  return res;
}

static void *
allocate_array (size_t num, size_t bytes)
{
  size_t actual_bytes = num * bytes;
  void *res = malloc (actual_bytes);
  if (actual_bytes && !res)
    fatal_error ("out-of-memory allocating %zu*%zu bytes", num, bytes);
  return res;
}

static void *
allocate_and_clear_array (size_t num, size_t bytes)
{
  void *res = calloc (num, bytes);
  if (num && bytes && !res)
    fatal_error ("out-of-memory allocating %zu*%zu bytes", num, bytes);
  return res;
}

static void *
reallocate_block (void *ptr, size_t bytes)
{
  void *res = realloc (ptr, bytes);
  if (bytes && !res)
    fatal_error ("out-of-memory reallocating %zu bytes", bytes);
  return res;
}

/*------------------------------------------------------------------------*/

static uint64_t
random64 (struct solver *solver)
{
  uint64_t res = solver->random, next = res;
  next *= 6364136223846793005ul;
  next += 1442695040888963407ul;
  solver->random = next;
  return res;
}

static unsigned
random32 (struct solver *solver)
{
  return random64 (solver) >> 32;
}

#if 0

static bool
random_bool (struct solver * solver)
{
  return (random64 (solver) >> 33) & 1;
}

#endif

static size_t
random_modulo (struct solver *solver, size_t mod)
{
  assert (mod);
  size_t tmp = random64 (solver);
  size_t res = tmp % mod;
  assert (res < mod);
  return res;
}

static double
random_double (struct solver *solver)
{
  return random32 (solver) / 4294967296.0;
}

/*------------------------------------------------------------------------*/

static bool
queue_contains (struct queue *queue, struct node *node)
{
  return queue->root == node || node->prev;
}

static struct node *
merge_nodes (struct node *a, struct node *b)
{
  if (!a)
    return b;
  if (!b)
    return a;
  assert (a != b);
  struct node *parent, *child;
  if (b->score > a->score)
    parent = b, child = a;
  else
    parent = a, child = b;
  struct node *parent_child = parent->child;
  child->next = parent_child;
  if (parent_child)
    parent_child->prev = child;
  child->prev = parent;
  parent->child = child;
  parent->prev = parent->next = 0;

  return parent;
}

static void
push_queue (struct queue *queue, struct node *node)
{
  assert (!queue_contains (queue, node));
  node->child = 0;
  queue->root = merge_nodes (queue->root, node);
  assert (queue_contains (queue, node));
}

static struct node *
collapse_node (struct node *node)
{
  if (!node)
    return 0;

  struct node *next = node, *tail = 0;

  do
    {
      struct node *a = next;
      assert (a);
      struct node *b = a->next;
      if (b)
	{
	  next = b->next;
	  struct node *tmp = merge_nodes (a, b);
	  assert (tmp);
	  tmp->prev = tail;
	  tail = tmp;
	}
      else
	{
	  a->prev = tail;
	  tail = a;
	  break;
	}
    }
  while (next);

  struct node *res = 0;
  while (tail)
    {
      struct node *prev = tail->prev;
      res = merge_nodes (res, tail);
      tail = prev;
    }

  return res;
}

static void
dequeue_node (struct node *node)
{
  assert (node);
  struct node *prev = node->prev;
  struct node *next = node->next;
  assert (prev);
  node->prev = 0;
  if (prev->child == node)
    prev->child = next;
  else
    prev->next = next;
  if (next)
    next->prev = prev;
}

static void
pop_queue (struct queue *queue, struct node *node)
{
  struct node *root = queue->root;
  struct node *child = node->child;
  if (root == node)
    queue->root = collapse_node (child);
  else
    {
      dequeue_node (node);
      struct node *collapsed = collapse_node (child);
      queue->root = merge_nodes (root, collapsed);
    }
  assert (!queue_contains (queue, node));
}

static void
update_queue (struct queue *queue, struct node *node, double new_score)
{
  double old_score = node->score;
  assert (old_score <= new_score);
  if (old_score == new_score)
    return;
  node->score = new_score;
  struct node *root = queue->root;
  if (root == node)
    return;
  if (!node->prev)
    return;
  dequeue_node (node);
  queue->root = merge_nodes (root, node);
}

static void
rescale_variable_scores (struct solver *solver)
{
  struct queue *queue = &solver->queue;
  unsigned stable = solver->stable;
  double max_score = queue->increment[stable];
  struct node *nodes = queue->nodes;
  struct node *end = nodes + solver->size;
  for (struct node * node = nodes; node != end; node++)
    if (node->score > max_score)
      max_score = node->score;
  LOG ("rescaling by maximum score of %g", max_score);
  assert (max_score > 0);
  for (struct node * node = nodes; node != end; node++)
    node->score /= max_score;
  queue->increment[stable] /= max_score;
}

static void
bump_variable_score (struct solver *solver, unsigned idx)
{
  struct queue *queue = &solver->queue;
  struct node *node = queue->nodes + idx;
  double old_score = node->score;
  double new_score = old_score + queue->increment[solver->stable];
  LOG ("bumping %s old score %g to new score %g",
       LOGVAR (idx), old_score, new_score);
  update_queue (queue, node, new_score);
  if (new_score > MAX_SCORE)
    rescale_variable_scores (solver);
}

static void
bump_score_increment (struct solver *solver)
{
  struct queue *queue = &solver->queue;
  unsigned stable = solver->stable;
  double old_increment = queue->increment[stable];
  double factor = stable ? 1.0 / STABLE_DECAY : 1.0 / FOCUSED_DECAY;
  double new_increment = old_increment * factor;
  LOG ("new increment %g", new_increment);
  queue->increment[stable] = new_increment;
  if (queue->increment[stable] > MAX_SCORE)
    rescale_variable_scores (solver);
}

static void
swap_scores (struct solver *solver)
{
  struct queue *queue = &solver->queue;
  double *s = queue->scores;
  for (all_nodes (node))
    {
      double tmp = node->score;
      node->score = *s;
      node->child = node->prev = node->next = 0;
      *s++ = tmp;
    }
  assert (s == queue->scores + solver->size);
  queue->root = 0;
  for (all_nodes (node))
    push_queue (queue, node);
  double tmp = queue->increment[0];
  queue->increment[0] = queue->increment[1];
  queue->increment[1] = tmp;
}

/*------------------------------------------------------------------------*/

static bool
tagged_literal (unsigned lit)
{
  return lit & 1;
}

static unsigned
untag_literal (unsigned lit)
{
  return lit >> 1;
}

static unsigned
tag_literal (bool tag, unsigned lit)
{
  assert (lit < (1u << 31));
  unsigned res = tag | (lit << 1);
  assert (untag_literal (res) == lit);
  assert (tagged_literal (res) == tag);
  return res;
}

/*------------------------------------------------------------------------*/

static unsigned
lower_pointer (void * watch)
{
  return (size_t) watch;
}

static unsigned
upper_pointer (void * watch)
{
  return (size_t) watch >> 32;
}

static bool
binary_pointer (void *watch)
{
  unsigned lower = lower_pointer (watch);
  return tagged_literal (lower);
}

static bool
redundant_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned upper = upper_pointer (watch);
  return tagged_literal (upper);
}

static unsigned
lit_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned lower = lower_pointer  (watch);
  return untag_literal (lower);
}

static unsigned
other_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned upper = upper_pointer  (watch);
  return untag_literal (upper);
}

static void *
tag_pointer (bool redundant, unsigned lit, unsigned other)
{
  unsigned lower = tag_literal (true, lit);
  unsigned upper = tag_literal (redundant, other);
  size_t word = lower | (size_t) upper << 32;
  void * res = (void*) word;
  assert (binary_pointer (res));
  assert (lit_pointer (res) == lit);
  assert (other_pointer (res) == other);
  assert (redundant_pointer (res) == redundant);
  return res;
}

/*------------------------------------------------------------------------*/

#define INIT_PROFILE(NAME) \
do { \
  struct profile * profile = &solver->profiles.NAME; \
  profile->start = -1; \
  profile->name = #NAME; \
} while (0)

static void
start_profile (struct profile *profile, double time)
{
  double volatile *p = &profile->start;
  assert (*p < 0);
  *p = time;
}

static void
stop_profile (struct profile *profile, double time)
{
  double volatile *p = &profile->start;
  double delta = time - *p;
  *p = -1;
  profile->time += delta;
}

#define START(NAME) \
  start_profile (&solver->profiles.NAME, current_time ())

#define STOP(NAME) \
  stop_profile (&solver->profiles.NAME, current_time ())

#define MODE_PROFILE \
  (solver->stable ? &solver->profiles.stable : &solver->profiles.focused)

#define STOP_SEARCH_AND_START(NAME) \
do { \
  double t = current_time (); \
  stop_profile (MODE_PROFILE, t); \
  stop_profile (&solver->profiles.search, t); \
  start_profile (&solver->profiles.NAME, t); \
} while (0)

#define STOP_AND_START_SEARCH(NAME) \
do { \
  double t = current_time (); \
  stop_profile (&solver->profiles.NAME, t); \
  start_profile (&solver->profiles.search, t); \
  start_profile (MODE_PROFILE, t); \
} while (0)

static void
init_profiles (struct solver *solver)
{
  INIT_PROFILE (focused);
  INIT_PROFILE (search);
  INIT_PROFILE (stable);
  INIT_PROFILE (walk);
  INIT_PROFILE (total);
  START (total);
}

/*------------------------------------------------------------------------*/

static struct root *
new_root (size_t size)
{
  struct root *root = allocate_and_clear_block (sizeof *root);
  pthread_mutex_init (&root->solvers.lock, 0);
  root->size = size;
  root->values = allocate_and_clear_block (2*size);
  root->units.begin = allocate_array (size, sizeof (unsigned));
  root->units.end = root->units.begin;
  pthread_mutex_init (&root->units.lock, 0);
  return root;
}

static void
delete_root (struct root *root)
{
#ifndef NDEBUG
  for (all_solvers (solver))
    assert (!solver);
#endif
  RELEASE (root->solvers);
  RELEASE (root->binaries);
  free (root->watches);
  free (root);
}

static void
push_solver (struct root *root, struct solver *solver)
{
  if (pthread_mutex_lock (&root->solvers.lock))
    fatal_error ("failed to acquire root lock while pushing solver");
  size_t id = SIZE (root->solvers); 
  assert (id < MAX_THREADS);
  solver->id = id;
  PUSH (root->solvers, solver);
  solver->random = solver->id;
  solver->root = root;
  solver->units = root->units.begin;
  if (pthread_mutex_unlock (&root->solvers.lock))
    fatal_error ("failed to release root lock while pushing solver");
}

static void
detach_solver (struct root *root, struct solver *solver)
{
  if (pthread_mutex_lock (&root->solvers.lock))
    fatal_error ("failed to acquire root lock while detaching solver");
  assert (solver->id < SIZE (root->solvers));
  assert (root->solvers.begin[solver->id] == solver);
  root->solvers.begin[solver->id] = 0;
  if (pthread_mutex_unlock (&root->solvers.lock))
    fatal_error ("failed to release root lock while detaching solver");
}

/*------------------------------------------------------------------------*/

static struct solver *
new_solver (struct root *root)
{
  unsigned size = root->size;
  assert (size < (1u << 30));
  struct solver *solver = allocate_and_clear_block (sizeof *solver);
  push_solver (root, solver);
  solver->size = size;
  verbose (solver, "new solver[%u] of size %u", solver->id, size);
  solver->values = allocate_and_clear_array (1, 2 * size);
  solver->references =
    allocate_and_clear_array (sizeof (struct references), 2 * size);
  solver->used = allocate_and_clear_block (size);
  solver->variables =
    allocate_and_clear_array (size, sizeof *solver->variables);
  struct trail *trail = &solver->trail;
  trail->begin = allocate_array (size, sizeof *trail->begin);
  trail->end = trail->propagate = trail->begin;
  struct queue *queue = &solver->queue;
  queue->nodes = allocate_and_clear_array (size, sizeof *queue->nodes);
  queue->scores = allocate_and_clear_array (size, sizeof *queue->scores);
  queue->increment[0] = queue->increment[1] = 1;
  for (all_nodes (node))
    push_queue (queue, node);
  solver->unassigned = size;
  solver->active = size;
  init_profiles (solver);
  for (all_averages (a))
    a->exp = 1.0;
  solver->limits.conflicts = -1;
  return solver;
}

static void
release_watches (struct solver *solver)
{
  for (all_literals (lit))
    free (REFERENCES (lit).begin);
  free (solver->references);

  for (all_watches (watch, solver->watches))
    {
      assert (!binary_pointer (watch));
      struct clause *clause = watch->clause;
      if (!atomic_fetch_sub (&clause->shared, 1))
	free (clause);
      free (watch);
    }
  RELEASE (solver->watches);
}

static void
delete_solver (struct solver *solver)
{
  verbose (solver, "delete solver[%u]", solver->id);
  RELEASE (solver->clause);
  RELEASE (solver->analyzed);
  free (solver->trail.begin);
  RELEASE (solver->levels);
  RELEASE (solver->buffer);
  release_watches (solver);
  free (solver->queue.nodes);
  free (solver->queue.scores);
  free (solver->variables);
  free (solver->values);
  free (solver->used);
  free (solver);
}

/*------------------------------------------------------------------------*/

static struct file proof;
static bool binary_proof_format = true;
static bool force = false;

static void
write_buffer (struct buffer *buffer, FILE * file)
{
  assert (file);
  size_t size = SIZE (*buffer);
  fwrite (buffer->begin, size, 1, file);
  CLEAR (*buffer);
}

static void
inc_proof_lines (void)
{
  atomic_fetch_add (&proof.lines, 1);
}

static void
trace_empty (struct solver *solver)
{
  assert (proof.file);
  struct buffer *buffer = &solver->buffer;
  assert (EMPTY (*buffer));
  if (binary_proof_format)
    {
      PUSH (*buffer, 'a');
      PUSH (*buffer, 0);
    }
  else
    {
      PUSH (*buffer, '0');
      PUSH (*buffer, '\n');
    }
  write_buffer (buffer, proof.file);
  inc_proof_lines ();
}

static void
binary_proof_line (struct buffer *buffer, size_t size, unsigned *literals)
{
  const unsigned *end = literals + size;
  for (const unsigned *p = literals; p != end; p++)
    {
      unsigned tmp = *p + 2;
      while (tmp & ~127u)
	{
	  unsigned char ch = (tmp & 0x7f) | 128;
	  PUSH (*buffer, ch);
	  tmp >>= 7;
	}
      PUSH (*buffer, (unsigned char) tmp);
    }
  PUSH (*buffer, 0);
}

static void
ascii_proof_line (struct buffer *buffer, size_t size, unsigned *literals)
{
  const unsigned *end = literals + size;
  char tmp[32];
  for (const unsigned *p = literals; p != end; p++)
    {
      sprintf (tmp, "%d", export_literal (*p));
      for (char *q = tmp, ch; (ch = *q); q++)
	PUSH (*buffer, ch);
      PUSH (*buffer, ' ');
    }
  PUSH (*buffer, '0');
  PUSH (*buffer, '\n');
}

static inline void
trace_added (struct solver *solver)
{
  assert (proof.file);
  struct buffer *buffer = &solver->buffer;
  assert (EMPTY (*buffer));
  struct unsigneds *clause = &solver->clause;
  if (binary_proof_format)
    {
      PUSH (*buffer, 'a');
      binary_proof_line (buffer, SIZE (*clause), clause->begin);
    }
  else
    ascii_proof_line (buffer, SIZE (*clause), clause->begin);
  write_buffer (buffer, proof.file);
  inc_proof_lines ();
}

static inline void
trace_deleted (struct solver *solver, struct clause *clause)
{
  assert (proof.file);
  struct buffer *buffer = &solver->buffer;
  assert (EMPTY (*buffer));
  PUSH (*buffer, 'd');
  if (binary_proof_format)
    binary_proof_line (buffer, clause->size, clause->literals);
  else
    {
      PUSH (*buffer, ' ');
      ascii_proof_line (buffer, clause->size, clause->literals);
    }
  write_buffer (buffer, proof.file);
  inc_proof_lines ();
}

#define TRACE_EMPTY() \
do { if (proof.file) trace_empty (solver); } while (0)

#define TRACE_ADDED() \
do { if (proof.file) trace_added (solver); } while (0)

#define TRACE_DELETED(CLAUSE) \
do { if (proof.file) trace_deleted (solver, (CLAUSE)); } while (0)

static void
close_proof (void)
{
  if (!proof.file)
    return;
  if (proof.close)
    fclose (proof.file);

  printf ("c\nc closed '%s' after writing %" PRIu64 " proof lines\n",
	  proof.path, proof.lines);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

static void
push_watch (struct solver *solver, unsigned lit, struct watch *watch)
{
  LOGWATCH (watch, "watching %s in", LOGLIT (lit));
  PUSH (REFERENCES (lit), watch);
}

static struct watch *
new_watch (struct solver *solver, struct clause *clause,
	   bool redundant, unsigned glue)
{
  assert (clause->size > 2);
  unsigned *literals = clause->literals;
  struct watch *watch = allocate_block (sizeof *watch);
  watch->garbage = false;
  watch->reason = false;
  watch->redundant = redundant;
  if (redundant && TIER1_GLUE_LIMIT < glue && glue <= TIER2_GLUE_LIMIT)
    watch->used = 2;
  else if (redundant && glue >= TIER2_GLUE_LIMIT)
    watch->used = 1;
  else
    watch->used = 0;
  watch->glue = glue;
  watch->middle = 2;
  watch->sum = literals[0] ^ literals[1];
  watch->clause = clause;
  push_watch (solver, literals[0], watch);
  push_watch (solver, literals[1], watch);
  PUSH (solver->watches, watch);
  assert (watch->glue == clause->glue);
  assert (watch->redundant == clause->redundant);
  return watch;
}

static void
delete_watch (struct solver *solver, struct watch *watch)
{
  (void) solver;
  free (watch);
}

static void
inc_clauses (struct solver *solver, bool redundant)
{
  if (redundant)
    solver->statistics.redundant++;
  else
    solver->statistics.irredundant++;
}

static void
dec_clauses (struct solver *solver, bool redundant)
{
  if (redundant)
    {
      assert (solver->statistics.redundant > 0);
      solver->statistics.redundant--;
    }
  else
    {
      assert (solver->statistics.irredundant > 0);
      solver->statistics.irredundant--;
    }
}

static void
new_global_binary_clause (struct solver *solver, bool redundant,
			  unsigned lit, unsigned other)
{
  struct root *root = solver->root;
  struct unsigneds *binaries = &root->binaries;
  PUSH (*binaries, lit);
  PUSH (*binaries, other);
  LOGBINARY (redundant, lit, other, "new global");
}

static struct watch *
new_local_binary_clause (struct solver *solver, bool redundant,
			 unsigned lit, unsigned other)
{
  inc_clauses (solver, redundant);
  struct watch *watch_lit = tag_pointer (redundant, lit, other);
  struct watch *watch_other = tag_pointer (redundant, other, lit);
  push_watch (solver, lit, watch_lit);
  push_watch (solver, other, watch_other);
  LOGBINARY (redundant, lit, other, "new local");
  return watch_lit;
}

static struct watch *
new_large_clause (struct solver *solver, size_t size, unsigned *literals,
		  bool redundant, unsigned glue)
{
  assert (2 <= size);
  assert (size <= solver->size);
  size_t bytes = size * sizeof (unsigned);
  struct clause *clause = allocate_block (sizeof *clause + bytes);
#ifdef LOGGING
  clause->id = ++solver->statistics.ids;
#endif
  inc_clauses (solver, redundant);
  if (glue > MAX_GLUE)
    glue = MAX_GLUE;
  clause->glue = glue;
  clause->redundant = redundant;
  clause->shared = 0;
  clause->size = size;
  memcpy (clause->literals, literals, bytes);
  LOGCLAUSE (clause, "new");
  return new_watch (solver, clause, redundant, glue);
}

static void
delete_clause (struct solver *solver, struct clause *clause)
{
  LOGCLAUSE (clause, "delete");
  dec_clauses (solver, clause->redundant);
  TRACE_DELETED (clause);
  free (clause);
}

/*------------------------------------------------------------------------*/

static struct solver *
first_solver (struct root * root)
{
  assert (!EMPTY (root->solvers));
  return root->solvers.begin[0];
}

static void
init_root_watches (struct root *root)
{
  struct solver * solver = first_solver (root);
  long *counts = allocate_and_clear_array (2 * root->size, sizeof *counts);
  struct unsigneds *binaries = &root->binaries;
  unsigned *begin = binaries->begin;
  unsigned *end = binaries->end;
  for (unsigned *p = begin; p != end; p += 2)
    counts[p[0]]++, counts[p[1]]++;
  long size = 0;
  for (all_literals (lit))
    {
      long count = counts[lit];
      if (count)
	{
	  assert (count < LONG_MAX);
	  assert (count + 1 <= LONG_MAX - size);
	  size += count;
	  counts[lit] = size++;
	}
      else
	counts[lit] = -1;
    }
  unsigned *global_watches = allocate_array (size, sizeof *global_watches);
  root->watches = global_watches;
  for (all_literals (lit))
    if (counts[lit] >= 0)
      global_watches[counts[lit]] = INVALID;
  {
    unsigned *p = end;
    while (p != begin)
      {
	unsigned lit = *--p;
	assert (p != begin);
	unsigned other = *--p;
	long count_lit = counts[lit];
	long count_other = counts[other];
	assert (count_lit > 0), counts[lit] = --count_lit;
	assert (count_other > 0), counts[other] = --count_other;
	global_watches[count_lit] = other;
	global_watches[count_other] = lit;
      }
  }
  for (all_literals (lit))
    {
      long count = counts[lit];
      struct references *lit_watches = &REFERENCES (lit);
      if (count >= 0)
	{
	  lit_watches->binaries = global_watches + count;
	  assert (lit_watches->binaries);
	}
      else
	assert (!lit_watches->binaries);
    }
  free (counts);

#ifdef LOGGING
  for (all_literals (lit))
    {
      unsigned *binaries = REFERENCES (lit).binaries;
      LOGPREFIX ("global binary watches of %s:", LOGLIT (lit));
      if (binaries)
	{
	  for (unsigned *p = binaries, other; (other = *p) != INVALID; p++)
	    printf (" %s", LOGLIT (other));
	}
      else
	printf (" none");
      LOGSUFFIX ();
    }
#endif
  printf ("c need %ld global binary clause watches\n", size);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

static void
assign (struct solver *solver, unsigned lit, struct watch *reason)
{
  const unsigned not_lit = NOT (lit);
  assert (!solver->values[lit]);
  assert (!solver->values[not_lit]);
  assert (solver->unassigned);
  solver->unassigned--;
  solver->values[lit] = 1;
  solver->values[not_lit] = -1;
  *solver->trail.end++ = lit;
  struct variable *v = VAR (lit);
  v->saved = SGN (lit) ? -1 : 1;
  unsigned level = solver->level;
  v->level = level;
  if (level)
    v->reason = reason;
  else
    {
      v->reason = 0;
      solver->statistics.fixed++;
      assert (solver->active);
      solver->active--;
    }
}

static void
assign_with_reason (struct solver *solver, unsigned lit, struct watch *reason)
{
  assert (reason);
  assign (solver, lit, reason);
  LOGWATCH (reason, "assign %s with reason", LOGLIT (lit));
}

static void
assign_unit (struct solver *solver, unsigned unit)
{
  assert (!solver->level);
  assign (solver, unit, 0);
  LOG ("assign %s unit", LOGLIT (unit));
}

static void
assign_decision (struct solver *solver, unsigned decision)
{
  assert (solver->level);
  assign (solver, decision, 0);
  LOG ("assign %s decision score %g",
       LOGLIT (decision), solver->queue.nodes[IDX (decision)].score);
}

/*------------------------------------------------------------------------*/

static void
set_winner (struct solver *solver)
{
  struct solver *winner = 0;
  struct root *root = solver->root;
  bool winning =
    atomic_compare_exchange_strong (&root->winner, &winner, solver);
  if (!winning)
    {
      assert (winner);
      assert (winner->status == solver->status);
      return;
    }
  atomic_store (&root->terminate, true);
  verbose (solver, "winning solver[%u] with status %d",
	   solver->id, solver->status);
}

static void
set_inconsistent (struct solver *solver, const char *msg)
{
  assert (!solver->inconsistent);
  very_verbose (solver, "%s", msg);
  solver->inconsistent = true;
  assert (!solver->status);
  solver->status = 20;
  set_winner (solver);
}

static void
set_satisfied (struct solver *solver)
{
  assert (!solver->inconsistent);
  assert (!solver->unassigned);
  assert (solver->trail.propagate == solver->trail.begin + solver->size);
  solver->status = 10;
  set_winner (solver);
}

/*------------------------------------------------------------------------*/

static void
share_clauses (struct solver *dst, struct solver *src)
{
  struct solver *solver = dst;
  verbose (solver, "copying clauses from solver[%u] to solver[%u]",
	   src->id, dst->id);
  assert (!src->level);
  assert (src->trail.propagate == src->trail.begin);
  if (src->inconsistent)
    {
      set_inconsistent (solver, "copying inconsistent empty clause");
      TRACE_EMPTY ();
      return;
    }
  unsigned units = 0;
  for (all_elements_on_stack (unsigned, lit, src->trail))
    {
      LOG ("copying unit %s", LOGLIT (lit));
      assign_unit (solver, lit);
      units++;
    }
  very_verbose (solver, "copied %u units", units);

  struct references *src_references = src->references;
  struct references *dst_references = dst->references;
  size_t copied_binary_watch_lists = 0;
  for (all_literals (lit))
    {
      struct references *src_watches = src_references + lit;
      struct references *dst_watches = dst_references + lit;
      assert (EMPTY (*dst_watches));
      unsigned *src_binaries = src_watches->binaries;
      if (src_binaries)
	{
	  dst_watches->binaries = src_binaries;
	  copied_binary_watch_lists++;
	}
#ifndef NDEBUG
      for (all_watches (src_watch, *src_watches))
	assert (!binary_pointer (src_watch));
#endif
    }
  very_verbose (solver, "shared %zu global binary watch lists",
		copied_binary_watch_lists);

  size_t shared = 0;
  for (all_watches (src_watch, src->watches))
    {
      struct clause *clause = src_watch->clause;
      assert (!clause->redundant);
      unsigned tmp = atomic_fetch_add (&clause->shared, 1);
      assert (tmp < MAX_THREADS - 1);
      (void) tmp;
      inc_clauses (solver, false);
      new_watch (solver, clause, false, 0);
      shared++;
    }
  very_verbose (solver, "shared %zu large clauses", shared);
}

static void
clone_solver (struct solver *src)
{
  struct solver *solver = new_solver (src->root);
  share_clauses (solver, src);
}

/*------------------------------------------------------------------------*/

static struct watch *
propagate (struct solver *solver, bool search)
{
  assert (!solver->inconsistent);
  struct trail *trail = &solver->trail;
  struct watch *conflict = 0;
  signed char *values = solver->values;
  uint64_t ticks = 0, propagations = 0;
  while (trail->propagate != trail->end)
    {
      if (search && conflict)
	break;
      unsigned lit = *trail->propagate++;
      LOG ("propagating %s", LOGLIT (lit));
      propagations++;
      unsigned not_lit = NOT (lit);
      struct references *watches = &REFERENCES (not_lit);
      unsigned *binaries = watches->binaries;
      if (binaries)
	{
	  unsigned other;
	  for (unsigned *p = binaries; (other = *p) != INVALID; p++)
	    {
	      struct watch *watch = tag_pointer (false, other, not_lit);
	      signed char other_value = values[other];
	      if (other_value < 0)
		{
		  conflict = watch;
		  if (search)
		    break;
		}
	      else if (!other_value)
		{
		  struct watch * reason = tag_pointer (false, other, not_lit);
		  assign_with_reason (solver, other, reason);
		  ticks++;
		}
	    }
	  if (search && conflict)
	    break;
	}
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end, **p = begin;
      ticks++;
      while (p != end)
	{
	  assert (!search || !conflict);
	  struct watch *watch = *q++ = *p++;
	  unsigned other;
	  signed char other_value;
	  if (binary_pointer (watch))
	    {
	      assert (lit_pointer (watch) == not_lit);
	      other = other_pointer (watch);
	      other_value = values[other];
	      if (other_value > 0)
		continue;
	      if (other_value < 0)
		{
		  conflict = watch;
		  if (search)
		    break;
		}
	      else
		{
		  struct watch * reason = tag_pointer (false, other, not_lit);
		  assign_with_reason (solver, other, reason);
		  ticks++;
		}
	    }
	  else
	    {
	      other = watch->sum ^ not_lit;
	      assert (other < 2 * solver->size);
	      other_value = values[other];
	      ticks++;
	      if (other_value > 0)
		continue;
	      struct clause *clause = watch->clause;
	      unsigned replacement = INVALID;
	      signed char replacement_value = -1;
	      unsigned *literals = clause->literals;
	      unsigned *end_literals = literals + clause->size;
	      assert (watch->middle <= clause->size);
	      unsigned *middle_literals = literals + watch->middle;
	      unsigned *r = middle_literals;
	      ticks++;
	      while (r != end_literals)
		{
		  replacement = *r;
		  if (replacement != not_lit && replacement != other)
		    {
		      replacement_value = values[replacement];
		      if (replacement_value >= 0)
			break;
		    }
		  r++;
		}
	      if (replacement_value < 0)
		{
		  r = literals;
		  while (r != middle_literals)
		    {
		      replacement = *r;
		      if (replacement != not_lit && replacement != other)
			{
			  replacement_value = values[replacement];
			  if (replacement_value >= 0)
			    break;
			}
		      r++;
		    }
		}
	      watch->middle = r - literals;
	      if (replacement_value >= 0)
		{
		  watch->sum = other ^ replacement;
		  LOGCLAUSE (watch->clause, "unwatching %s in", LOGLIT (lit));
		  push_watch (solver, replacement, watch);
		  ticks++;
		  q--;
		}
	      else if (other_value)
		{
		  assert (other_value < 0);
		  conflict = watch;
		  if (search)
		    break;
		}
	      else
		{
		  assign_with_reason (solver, other, watch);
		  ticks++;
		}
	    }
	}
      while (p != end)
	*q++ = *p++;
      watches->end = q;
      if (q == watches->begin)
	RELEASE (*watches);
    }

  struct context * context = solver->statistics.contexts + solver->context;

  if (conflict)
    {
      LOGWATCH (conflict, "conflicting");
      context->conflicts++;
    }

  context->propagations += propagations;
  context->ticks += ticks;

  return conflict;
}

/*------------------------------------------------------------------------*/

static void
backtrack (struct solver *solver, unsigned level)
{
  assert (solver->level > level);
  struct trail *trail = &solver->trail;
  struct variable *variables = solver->variables;
  signed char *values = solver->values;
  struct queue *queue = &solver->queue;
  struct node *nodes = queue->nodes;
  unsigned *t = trail->end;
  while (t != trail->begin)
    {
      unsigned lit = t[-1], idx = IDX (lit);
      if (variables[idx].level == level)
	break;
      LOG ("unassign %s", LOGLIT (lit));
      unsigned not_lit = NOT (lit);
      values[lit] = values[not_lit] = 0;
      assert (solver->unassigned < solver->size);
      solver->unassigned++;
      struct node *node = nodes + idx;
      if (!queue_contains (queue, node))
	push_queue (queue, node);
      t--;
    }
  trail->end = trail->propagate = t;
  solver->level = level;
}

static void
update_best_and_target_phases (struct solver *solver)
{
  if (!solver->stable)
    return;
  unsigned assigned = SIZE (solver->trail);
  if (solver->target < assigned)
    {
      very_verbose (solver, "updating target assigned to %u", assigned);
      solver->target = assigned;
      signed char *p = solver->values;
      for (all_variables (v))
	{
	  signed char tmp = *p;
	  p += 2;
	  if (tmp)
	    v->target = tmp;
	}
    }
  if (solver->best < assigned)
    {
      very_verbose (solver, "updating best assigned to %u", assigned);
      solver->best = assigned;
      signed char *p = solver->values;
      for (all_variables (v))
	{
	  signed char tmp = *p;
	  p += 2;
	  if (tmp)
	    v->best = tmp;
	}
    }
}

/*------------------------------------------------------------------------*/

#define COMPILER_BARRIER() __asm__ __volatile__("": : :"memory")

static void
export_unit (struct solver * solver, unsigned unit)
{
  struct root * root = solver->root;
  volatile signed char * values = root->values;
  if (values[unit])
    return;
  if (pthread_mutex_lock (&root->units.lock))
    message_lock_failure ("failed to acquire unit lock");
  signed char value = values[unit];
  if (!value)
    {
      solver->statistics.exported.units++;
      unsigned not_unit = NOT (unit);
      assert (!values[not_unit]);
      *root->units.end++ = unit;
      values[unit] = 1;
      values[not_unit] = -1;
      LOG ("exporting root unit %s", LOGLIT (unit));
    }
  if (pthread_mutex_unlock (&root->units.lock))
    message_lock_failure ("failed to release unit lock");
}

static bool
import_unit (struct solver * solver)
{
  return false;
}

static void
export_clause (struct solver * solver, struct watch * watch)
{
  if (!binary_pointer (watch))
    return;
  struct root * root = solver->root;
  if (SIZE (root->solvers) == 1)
    return;
  solver->statistics.exported.binary++;
  COMPILER_BARRIER ();
  solver->share = watch;
}

static bool
import_clause (struct solver * solver)
{
  struct root * root = solver->root;
  size_t solvers = SIZE (root->solvers);
  assert (solvers <= UINT_MAX);
  assert (solvers > 0);
  if (solvers == 1)
    return false;
  unsigned id = random_modulo (solver, solvers-1) + solver->id + 1;
  if (id >= solvers)
    id -= solvers;
  assert (id < solvers);
  assert (id != solver->id);
  struct solver * src = root->solvers.begin[id];
  if (!src->share)
    return false;
  struct watch * watch = (struct watch*) atomic_exchange (&src->share, 0);
  if (!watch)
    return false;
  solver->statistics.imported.binary++;
  return true;
}

/*------------------------------------------------------------------------*/

static void
bump_reason (struct watch *watch)
{
  if (!watch->redundant)
    return;
  if (watch->clause->glue <= TIER1_GLUE_LIMIT)
    return;
  if (watch->clause->glue <= TIER2_GLUE_LIMIT)
    watch->used = 2;
  else
    watch->used = 1;
}

static bool
minimize_literal (struct solver *solver, unsigned lit, unsigned depth)
{
  assert (solver->values[lit] < 0);
  if (depth >= MINIMIZE_DEPTH)
    return false;
  unsigned idx = IDX (lit);
  struct variable *v = solver->variables + idx;
  if (!v->level)
    return true;
  if (!solver->used[v->level])
    return false;
  if (v->poison)
    return false;
  if (v->minimize)
    return true;
  if (depth && (v->seen))
    return true;
  struct watch *reason = v->reason;
  if (!reason)
    return false;
  depth++;
  bool res = true;
  const unsigned not_lit = NOT (lit);
  if (binary_pointer (reason))
    {
      assert (lit_pointer (reason) == not_lit);
      unsigned other = other_pointer (reason);
      res = minimize_literal (solver, other, depth);
    }
  else
    {
      struct clause *clause = reason->clause;
      for (all_literals_in_clause (other, clause))
	if (other != not_lit && !minimize_literal (solver, other, depth))
	  res = false;
    }
  if (res)
    v->minimize = true;
  else
    v->poison = true;
  PUSH (solver->analyzed, idx);
  return res;
}

static void
minimize_clause (struct solver *solver, unsigned glue)
{
  struct unsigneds *clause = &solver->clause;
  unsigned *begin = clause->begin, *q = begin + 1;
  unsigned *end = clause->end;
  size_t minimized = 0;
  for (unsigned *p = q; p != end; p++)
    {
      unsigned lit = *q++ = *p;
      if (!minimize_literal (solver, lit, 0))
	continue;
      LOG ("minimized literal %s\n", LOGLIT (lit));
      minimized++;
      q--;
    }
  size_t deduced = SIZE (*clause);
  clause->end = q;
  size_t learned = SIZE (*clause);
  assert (learned + minimized == deduced);

  solver->statistics.learned.clauses++;
  if (learned == 1)
    solver->statistics.learned.units++;
  if (learned == 2)
    solver->statistics.learned.binary++;
  if (glue == 1)
    solver->statistics.learned.glue1++;
  if (glue <= TIER1_GLUE_LIMIT)
    solver->statistics.learned.tier1++;
  else if (glue <= TIER2_GLUE_LIMIT)
    solver->statistics.learned.tier2++;
  else
    solver->statistics.learned.tier3++;

  solver->statistics.learned.literals += learned;
  solver->statistics.minimized += minimized;
  solver->statistics.deduced += deduced;
  LOG ("minimized %zu literals out of %zu", minimized, deduced);
}

static void
bump_reason_side_literal (struct solver *solver, unsigned lit)
{
  unsigned idx = IDX (lit);
  struct variable *v = solver->variables + idx;
  if (!v->level)
    return;
  if (v->seen)
    return;
  v->seen = true;
  if (!v->poison && !v->minimize)
    PUSH (solver->analyzed, idx);
  bump_variable_score (solver, idx);
}

static void
bump_reason_side_literals (struct solver *solver)
{
  for (all_elements_on_stack (unsigned, lit, solver->clause))
    {
      struct variable *v = VAR (lit);
      if (!v->level)
	continue;
      struct watch *reason = v->reason;
      if (!reason)
	continue;
      assert (v->seen);
      if (binary_pointer (reason))
	{
	  assert (NOT (lit) == lit_pointer (reason));
	  bump_reason_side_literal (solver, other_pointer (reason));
	}
      else
	{
	  struct clause *clause = reason->clause;
	  const unsigned not_lit = NOT (lit);
	  for (all_literals_in_clause (other, clause))
	    if (other != not_lit)
	      bump_reason_side_literal (solver, other);
	}
    }
}

#define ANALYZE(LIT) \
do { \
  if (LIT == uip) \
    break; \
  assert (solver->values[LIT] < 0); \
  unsigned idx = IDX (LIT); \
  struct variable *v = variables + idx; \
  unsigned lit_level = v->level; \
  if (!lit_level) \
    break; \
  if (v->seen) \
    break; \
  v->seen = true; \
  PUSH (*analyzed, idx); \
  bump_variable_score (solver, idx); \
  if (lit_level == level) \
    { \
      open++; \
      break;; \
    } \
  PUSH (*clause, LIT); \
  if (!used[lit_level]) \
    { \
      glue++; \
      used[lit_level] = true; \
      PUSH (*levels, lit_level); \
      if (lit_level > jump) \
	jump = lit_level; \
    } \
} while (0)

static bool
analyze (struct solver *solver, struct watch *reason)
{
  assert (!solver->inconsistent);
#if 0
  for (all_variables (v))
    assert (!v->seen), assert (!v->poison), assert (!v->minimize);
#endif
  if (!solver->level)
    {
      set_inconsistent (solver,
			"conflict on root-level produces empty clause");
      TRACE_EMPTY ();
      return false;
    }
  struct unsigneds *clause = &solver->clause;
  struct unsigneds *analyzed = &solver->analyzed;
  struct unsigneds *levels = &solver->levels;
  assert (EMPTY (*clause));
  assert (EMPTY (*analyzed));
  assert (EMPTY (*levels));
  bool *used = solver->used;
  struct variable *variables = solver->variables;
  struct trail *trail = &solver->trail;
  unsigned *t = trail->end;
  PUSH (*clause, INVALID);
  const unsigned level = solver->level;
  unsigned uip = INVALID, jump = 0, glue = 0, open = 0;
  for (;;)
    {
      LOGWATCH (reason, "analyzing");
      if (binary_pointer (reason))
	{
	  unsigned lit = lit_pointer (reason);
	  unsigned other = other_pointer (reason);
	  ANALYZE (lit);
	  ANALYZE (other);
	}
      else
	{
	  bump_reason (reason);
	  for (all_literals_in_clause (lit, reason->clause))
	    ANALYZE (lit);
	}
      do
	{
	  assert (t > solver->trail.begin);
	  uip = *--t;
	}
      while (!VAR (uip)->seen);
      if (!--open)
	break;
      reason = variables[IDX (uip)].reason;
      assert (reason);
    }
  LOG ("back jump level %u", jump);
  struct averages *averages = solver->averages + solver->stable;
  update_average (&averages->level, SLOW_ALPHA, jump);
  LOG ("glucose level (LBD) %u", glue);
  update_average (&averages->glue.slow, SLOW_ALPHA, glue);
  update_average (&averages->glue.fast, FAST_ALPHA, glue);
  unsigned assigned = SIZE (solver->trail);
  double filled = percent (assigned, solver->size);
  LOG ("assigned %u variables %.0f%% filled", assigned, filled);
  update_average (&averages->trail, SLOW_ALPHA, filled);
  unsigned *literals = clause->begin;
  const unsigned not_uip = NOT (uip);
  literals[0] = not_uip;
  LOGTMP ("first UIP %s", LOGLIT (uip));
  minimize_clause (solver, glue);
  bump_reason_side_literals (solver);
  bump_score_increment (solver);
  backtrack (solver, level - 1);
  update_best_and_target_phases (solver);
  if (jump < level - 1)
    backtrack (solver, jump);
  unsigned size = SIZE (*clause);
  assert (size);
  if (size == 1)
    {
      assign_unit (solver, not_uip);
      export_unit (solver, not_uip);
      solver->iterating = true;
    }
  else
    {
      unsigned other = literals[1];
      struct watch *learned;
      if (size == 2)
	{
	  assert (VAR (other)->level == jump);
	  learned = new_local_binary_clause (solver, true, not_uip, other);
	}
      else
	{
	  if (VAR (other)->level != jump)
	    {
	      unsigned *p = literals + 2, replacement;
	      while (assert (p != clause->end),
		     VAR (replacement = *p)->level != jump)
		p++;
	      literals[1] = replacement;
	      *p = other;
	    }
	  learned = new_large_clause (solver, size, literals, true, glue);
	}
      assign_with_reason (solver, not_uip, learned);
      export_clause (solver, learned);
    }
  TRACE_ADDED ();
  CLEAR (*clause);
  for (all_elements_on_stack (unsigned, idx, *analyzed))
    {
      struct variable *v = variables + idx;
      v->seen = v->poison = v->minimize = false;
    }
  CLEAR (*analyzed);
  for (all_elements_on_stack (unsigned, used_level, *levels))
      used[used_level] = false;
  CLEAR (*levels);
  return true;
}

static signed char
decide_phase (struct solver *solver, struct variable *v)
{
  signed char phase = 0;
  if (solver->stable)
    phase = v->target;
  if (!phase)
    phase = v->saved;
  if (!phase)
    phase = INITIAL_PHASE;
  return phase;
}

static unsigned
gcd (unsigned a, unsigned b)
{
  while (b) {
    unsigned r = a % b;
    a = b, b = r;
  }
  return a;
}

static unsigned
random_decision (struct solver * solver)
{
  assert (solver->unassigned);

  signed char *values = solver->values;
  unsigned size = solver->size;

  unsigned idx = random_modulo (solver, size);
  unsigned lit = LIT (idx);

  if (values[lit])
    {
      unsigned delta = random_modulo (solver, size);
      while (gcd (delta, size) != 1)
	if (++delta == size)
	  delta = 1;
      assert (delta < size);
      do {
	idx += delta;
	if (idx >= size)
	  idx -= size;
	lit = LIT (idx);
      } while (values[lit]);
    }

  LOG ("random decision %s", LOGVAR (idx));

  return idx;
}

static unsigned
best_score_decision (struct solver * solver)
{
  assert (solver->unassigned);

  signed char *values = solver->values;
  struct queue *queue = &solver->queue;
  struct node *nodes = queue->nodes;

  assert (queue->root);

  unsigned lit, idx;
  for (;;)
    {
      struct node *root = queue->root;
      assert (root);
      assert (root - nodes < solver->size);
      idx = root - nodes;
      lit = LIT (idx);
      if (!values[lit])
	break;
      pop_queue (queue, root);
    }
  assert (idx < solver->size);

  LOG ("best score decision %s score %g",
       LOGVAR (idx), nodes[idx].score);

  return idx;
}

static void
decide (struct solver *solver)
{
  struct context * context = solver->statistics.contexts;
  context += solver->context;
  uint64_t decisions = context->decisions++;

  unsigned idx;
  if (solver->id && decisions < RANDOM_DECISIONS)
    idx = random_decision (solver);
  else
    idx = best_score_decision (solver);

  struct variable *v = solver->variables + idx;
  signed char phase = decide_phase (solver, v);
  unsigned lit = LIT (idx);
  if (phase < 0)
    lit = NOT (lit);

  solver->level++;
  assign_decision (solver, lit);
}

static void
report (struct solver *solver, char type)
{
  struct statistics *s = &solver->statistics;
  struct averages *a = solver->averages + solver->stable;

  acquire_message_lock ();

  double t = wall_clock_time ();
  double m = current_resident_set_size () / (double) (1 << 20);
  uint64_t conflicts = s->contexts[SEARCH].conflicts;

  static uint64_t reported;
  if (!(reported++ % 20))
    printf ("c\nc       seconds MB level reductions restarts "
	    "conflicts redundant trail glue irredundant variables\nc\n");

  PRINT ("%c %7.2f %4.0f %5.0f %6" PRIu64 " %9" PRIu64 " %11" PRIu64
	 " %9zu %3.0f%% %6.1f %9zu %9u %3.0f%%", type, t, m,
	 a->level.value, s->reductions, s->restarts, conflicts,
	 s->redundant, a->trail.value, a->glue.slow.value, s->irredundant,
	 solver->active, percent (solver->active, solver->size));

  fflush (stdout);

  release_message_lock ();
}

static bool
restarting (struct solver *solver)
{
  if (!solver->level)
    return false;
  struct limits *l = &solver->limits;
  if (!solver->stable)
    {
      struct averages *a = solver->averages;
      if (a->glue.fast.value <= RESTART_MARGIN * a->glue.slow.value)
	return false;
    }
  return l->restart < SEARCH_CONFLICTS;
}

static void
restart (struct solver *solver)
{
  struct statistics *statistics = &solver->statistics;
  statistics->restarts++;
  verbose (solver, "restart %" PRIu64 " at %" PRIu64 " conflicts",
	   statistics->restarts, SEARCH_CONFLICTS);
  update_best_and_target_phases (solver);
  backtrack (solver, 0);
  struct limits *limits = &solver->limits;
  limits->restart = SEARCH_CONFLICTS;
  if (solver->stable)
    {
      struct reluctant *reluctant = &solver->reluctant;
      uint64_t u = reluctant->u, v = reluctant->v;
      if ((u & -u) == v)
	u++, v = 1;
      else
	v *= 2;
      limits->restart += STABLE_RESTART_INTERVAL * v;
      reluctant->u = u, reluctant->v = v;
    }
  else
    limits->restart += FOCUSED_RESTART_INTERVAL;
  verbose (solver, "next restart limit at %" PRIu64 " conflicts",
	   limits->restart);
  if (verbosity > 0)
    report (solver, 'r');
}

static void
mark_reasons (struct solver *solver)
{
  for (all_literals_on_trail (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (!watch)
	continue;
      if (binary_pointer (watch))
	continue;
      assert (!watch->reason);
      watch->reason = true;
    }
}

static void
unmark_reasons (struct solver *solver)
{
  for (all_literals_on_trail (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (!watch)
	continue;
      if (binary_pointer (watch))
	continue;
      assert (watch->reason);
      watch->reason = false;
    }
}

static void
mark_satisfied_clauses_as_garbage (struct solver *solver)
{
  size_t marked = 0;
  signed char *values = solver->values;
  struct variable *variables = solver->variables;
  for (all_watches (watch, solver->watches))
    {
      if (watch->garbage)
	continue;
      bool satisfied = false;
      struct clause *clause = watch->clause;
      for (all_literals_in_clause (lit, clause))
	{
	  if (values[lit] <= 0)
	    continue;
	  unsigned idx = IDX (lit);
	  if (variables[idx].level)
	    continue;
	  satisfied = true;
	  break;
	}
      if (!satisfied)
	continue;
      LOGCLAUSE (clause, "marking satisfied garbage");
      watch->garbage = true;
      marked++;
    }
  solver->last.fixed = solver->statistics.fixed;
  verbose (solver, "marked %zu satisfied clauses as garbage %.0f%%",
	   marked, percent (marked, SIZE (solver->watches)));
}

static void
gather_reduce_candidates (struct solver *solver, struct watches *candidates)
{
  for (all_watches (watch, solver->watches))
    {
      if (watch->garbage)
	continue;
      if (watch->reason)
	continue;
      if (!watch->redundant)
	continue;
      if (watch->glue <= TIER1_GLUE_LIMIT)
	continue;
      if (watch->used)
	{
	  watch->used--;
	  continue;
	}
      PUSH (*candidates, watch);
    }
  verbose (solver, "gathered %zu reduce candidates clauses %.0f%%",
	   SIZE (*candidates),
	   percent (SIZE (*candidates), solver->statistics.redundant));
}

static void
sort_reduce_candidates (struct watches *candidates)
{
  size_t size_candidates = SIZE (*candidates);
  if (size_candidates < 2)
    return;
  size_t size_count = MAX_GLUE + 1, count[size_count];
  memset (count, 0, sizeof count);
  for (all_watches (watch, *candidates))
    assert (watch->glue <= MAX_GLUE), count[watch->glue]++;
  size_t pos = 0, *c = count + size_count, size;
  while (c-- != count)
    size = *c, *c = pos, pos += size;
  size_t bytes = size_candidates * sizeof (struct watch *);
  struct watch **tmp = allocate_block (bytes);
  for (all_watches (watch, *candidates))
    tmp[count[watch->glue]++] = watch;
  memcpy (candidates->begin, tmp, bytes);
  free (tmp);
}

static void
mark_reduce_candidates_as_garbage (struct solver *solver,
				   struct watches *candidates)
{
  size_t size = SIZE (*candidates);
  size_t target = REDUCE_FRACTION * size;
  size_t reduced = 0;
  for (all_watches (watch, *candidates))
    {
      LOGCLAUSE (watch->clause, "marking garbage");
      assert (!watch->garbage);
      watch->garbage = true;
      if (++reduced == target)
	break;
    }
  verbose (solver, "reduced %zu clauses %.0f%%",
	   reduced, percent (reduced, size));
}

static void
flush_references (struct solver *solver, bool fixed)
{
  size_t flushed = 0;
  signed char *values = solver->values;
  struct variable *variables = solver->variables;
  for (all_literals (lit))
    {
      signed char lit_value = values[lit];
      if (lit_value > 0)
	{
	  if (variables[IDX (lit)].level)
	    lit_value = 0;
	}
      struct references *watches = &REFERENCES (lit);
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end;
      for (struct watch ** p = begin; p != end; p++)
	{
	  struct watch *watch = *q++ = *p;
	  if (binary_pointer (watch))
	    {
	      if (!fixed)
		continue;
	      unsigned other = lit_pointer (watch);
	      signed char other_value = values[other];
	      if (other_value > 0)
		{
		  if (variables[IDX (other)].level)
		    other_value = 0;
		}
	      if (lit_value > 0 || other_value > 0)
		{
		  if (lit < other)
		    {
		      bool redundant = redundant_pointer (watch);
		      dec_clauses (solver, redundant);
		    }
		  flushed++;
		  q--;
		}
	    }
	  else
	    {
	      if (!watch->garbage)
		continue;
	      if (watch->reason)
		continue;
	      flushed++;
	      q--;
	    }
	}
      watches->end = q;
      SHRINK (*watches);
    }
  verbose (solver, "flushed %zu garbage watches from watch lists", flushed);
}

static void
flush_watches (struct solver *solver)
{
  struct watches *watches = &solver->watches;
  struct watch **begin = watches->begin, **q = begin;
  struct watch **end = watches->end;
  size_t flushed = 0, deleted = 0;
  for (struct watch ** p = begin; p != end; p++)
    {
      struct watch *watch = *q++ = *p;
      assert (!binary_pointer (watch));
      if (!watch->garbage)
	continue;
      if (watch->reason)
	continue;
      flushed++;
      q--;

      struct clause *clause = watch->clause;
      delete_watch (solver, watch);

      if (atomic_fetch_sub (&clause->shared, 1))
	continue;

      delete_clause (solver, clause);
      deleted++;
    }
  watches->end = q;
  verbose (solver,
	   "flushed %zu garbage watched and deleted %zu clauses %.0f%%",
	   flushed, deleted, percent (deleted, flushed));
}

static bool
reducing (struct solver *solver)
{
  return solver->limits.reduce < SEARCH_CONFLICTS;
}

static void
reduce (struct solver *solver)
{
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  statistics->reductions++;
  verbose (solver, "reduction %" PRIu64 " at %" PRIu64 " conflicts",
	   statistics->reductions, SEARCH_CONFLICTS);
  mark_reasons (solver);
  struct watches candidates;
  INIT (candidates);
  bool fixed = solver->last.fixed != solver->statistics.fixed;
  if (fixed)
    mark_satisfied_clauses_as_garbage (solver);
  gather_reduce_candidates (solver, &candidates);
  sort_reduce_candidates (&candidates);
  mark_reduce_candidates_as_garbage (solver, &candidates);
  RELEASE (candidates);
  flush_references (solver, fixed);
  flush_watches (solver);
  unmark_reasons (solver);
  limits->reduce = SEARCH_CONFLICTS;
  limits->reduce += REDUCE_INTERVAL * sqrt (statistics->reductions + 1);
  verbose (solver, "next reduce limit at %" PRIu64 " conflicts",
	   limits->reduce);
  report (solver, '-');
}

static void
switch_to_focused_mode (struct solver *solver)
{
  assert (solver->stable);
  report (solver, ']');
  STOP (stable);
  solver->stable = false;
  START (focused);
  report (solver, '{');
  struct limits *limits = &solver->limits;
  limits->restart = SEARCH_CONFLICTS + FOCUSED_RESTART_INTERVAL;
}

static void
switch_to_stable_mode (struct solver *solver)
{
  assert (!solver->stable);
  report (solver, '}');
  STOP (focused);
  solver->stable = true;
  START (stable);
  report (solver, '[');
  struct limits *limits = &solver->limits;
  limits->restart = SEARCH_CONFLICTS + STABLE_RESTART_INTERVAL;
  solver->reluctant.u = solver->reluctant.v = 1;
}

static bool
switching_mode (struct solver *solver)
{
  struct limits *l = &solver->limits;
  if (solver->statistics.switched)
    return SEARCH_TICKS > l->mode;
  else
    return SEARCH_CONFLICTS > l->mode;
}

static uint64_t
square (uint64_t n)
{
  assert (n);
  return n * n;
}

static void
switch_mode (struct solver *solver)
{
  struct statistics *s = &solver->statistics;
  struct intervals *i = &solver->intervals;
  struct limits *l = &solver->limits;
  if (!s->switched++)
    {
      i->mode = SEARCH_TICKS;
      verbose (solver, "determined mode switching ticks interval %" PRIu64,
	       i->mode);
    }
  if (solver->stable)
    switch_to_focused_mode (solver);
  else
    switch_to_stable_mode (solver);
  swap_scores (solver);
  l->mode = SEARCH_TICKS + square (s->switched / 2 + 1) * i->mode;
  verbose (solver, "next mode switching limit at %" PRIu64 " ticks", l->mode);
}

struct doubles
{
  double *begin, *end, *allocated;
};

struct counter
{
  unsigned count;
  struct clause *clause;
};

struct counters
{
  struct counter ** begin, ** end, ** allocated;
  unsigned *binaries;
};

struct set
{
  size_t size;
  size_t deleted;
  size_t allocated;
  void ** table;
};

static size_t
hash_pointer_to_position (void * ptr)
{
  size_t res = 1111111121u * (size_t) ptr;
  return res;
}

static size_t
hash_pointer_to_delta (void * ptr)
{
  size_t res = 2222222243u * (size_t) ptr;
  return res;
}

#ifndef NDEBUG

static bool
is_power_of_two (size_t n)
{
  return n && !(n & (n-1));
}

#endif

static size_t
reduce_hash (size_t hash, size_t allocated)
{
  assert (allocated);
  assert (is_power_of_two (allocated));
  size_t res = hash;
  if (allocated >= (size_t)1 << 32)
    res ^= res >> 32;
  if (allocated >= (size_t)1 << 16)
    res ^= res >> 16;
  if (allocated >= (size_t)1 << 8)
    res ^= res >> 8;
  res &= allocated - 1;
  assert (res < allocated);
  return res;
}

static size_t
reduce_delta (size_t hash, size_t allocated)
{
  return reduce_hash (hash, allocated) | 1;
}

#define DELETED ((void*) ~(size_t) 0)

#ifndef NDEBUG

static bool
set_contains (struct set * set, void * ptr)
{
  assert (ptr);
  assert (ptr != DELETED);
  size_t size = set->size;
  if (!size)
    return false;
  size_t hash = hash_pointer_to_position (ptr);
  size_t allocated = set->allocated;
  size_t start = reduce_hash (hash, allocated);
  void ** table = set->table;
  void * tmp = table[start];
  if (!tmp)
    return false;
  if (tmp == ptr)
    return true;
  hash = hash_pointer_to_delta (ptr);
  size_t delta = reduce_delta (hash, allocated);
  size_t pos = start;
  assert (allocated < 2 || (delta & 1));
  for (;;)
    {
      pos += delta;
      if (pos >= allocated)
	pos -= allocated;
      assert (pos < allocated);
      if (pos == start)
	return false;
      tmp = table[pos];
      if (!tmp)
	return false;
      if (tmp == ptr)
	return true;
    } 
}

#endif

static void enlarge_set (struct set * set);
static void shrink_set (struct set * set);

static void
set_insert (struct set * set, void * ptr)
{
  assert (ptr);
  assert (ptr != DELETED);
  if (set->size + set->deleted >= set->allocated/2)
    enlarge_set (set);
  size_t hash = hash_pointer_to_position (ptr);
  size_t allocated = set->allocated;
  size_t start = reduce_hash (hash, allocated);
  void ** table = set->table;
  size_t pos = start;
  void * tmp = table[pos];
  if (tmp && tmp != DELETED)
    {
      hash = hash_pointer_to_delta (ptr);
      size_t delta = reduce_delta (hash, allocated);
      assert (delta & 1);
      do
	{
	  pos += delta;
	  if (pos >= allocated)
	    pos -= allocated;
	  assert (pos < allocated);
	  assert (pos != start);
	  tmp = table[pos];
	}
      while (tmp && tmp != DELETED);
    }
  if (tmp == DELETED)
    {
      assert (set->deleted);
      set->deleted--;
    }
  set->size++;
  table[pos] = ptr;
  assert (set_contains (set, ptr));
}

static void
set_remove (struct set * set, void * ptr)
{
  assert (ptr);
  assert (ptr != DELETED);
  assert (set_contains (set, ptr));
  assert (set->size);
  if (set->allocated > 16 && set->size <= set->allocated/8)
    shrink_set (set);
  size_t hash = hash_pointer_to_position (ptr);
  size_t allocated = set->allocated;
  size_t start = reduce_hash (hash, allocated);
  void ** table = set->table;
  size_t pos = start;
  void * tmp = table[pos];
  if (tmp != ptr)
    {
      assert (tmp);
      hash = hash_pointer_to_delta (ptr);
      size_t delta = reduce_delta (hash, allocated);
      assert (delta & 1);
      do 
	{
	  pos += delta;
	  if (pos >= allocated)
	    pos -= allocated;
	  assert (pos < allocated);
	  assert (pos != start);
	  tmp = table[pos];
	  assert (tmp);
	} 
      while (tmp != ptr);
    }
  table[pos] = DELETED;
  set->deleted++;
  set->size--;
}

static void
resize_set (struct set * set, size_t new_allocated)
{
  assert (new_allocated != set->allocated);
  void ** old_table = set->table;
  unsigned old_allocated = set->allocated;
  set->allocated = new_allocated;
#ifndef NDEBUG
  size_t old_size = set->size;
#endif
  assert (old_size < new_allocated);
  set->size = set->deleted = 0;
  set->table = allocate_and_clear_array (new_allocated, sizeof *set->table);
  void ** end = old_table + old_allocated;
  for (void ** p = old_table, * ptr; p != end; p++)
    if ((ptr = *p) && ptr != DELETED)
      set_insert (set, ptr);
  assert (set->size == old_size);
  assert (set->allocated == new_allocated);
  free (old_table);
}

static void
enlarge_set (struct set * set)
{
  size_t old_allocated = set->allocated;
  size_t new_allocated = old_allocated ? 2*old_allocated : 2;
  resize_set (set, new_allocated);
}

static void
shrink_set (struct set * set)
{
  size_t old_allocated = set->allocated;
  size_t new_allocated = old_allocated / 2;
  resize_set (set, new_allocated);
}

static void *
random_set (struct solver * solver, struct set * set)
{
  assert (set->size);
  size_t allocated = set->allocated;
  size_t pos = random_modulo (solver, allocated);
  void ** table = set->table;
  void * res = table[pos];
  while (!res || res == DELETED)
    {
      if (++pos == allocated)
	pos = 0;
      res = table[pos];
    }
  return res;
}

struct walker
{
  struct solver *solver;
  struct counters *occurrences;
  struct counter *counters;
  struct set unsatisfied;
  struct unsigneds literals;
  struct unsigneds trail;
  struct watches saved;
  struct doubles scores;
  struct doubles breaks;
  unsigned maxbreak;
  double epsilon;
  size_t minimum;
  size_t initial;
  unsigned best;
  uint64_t limit;
  uint64_t extra;
  uint64_t flips;
};

#ifdef LOGGING

#define WOG(...) \
do { \
  struct solver * solver = walker->solver; \
  LOG (__VA_ARGS__); \
} while (0)

#else

#define WOG(...) do { } while (0)

#endif

#define OCCURRENCES(LIT) (walker->occurrences[LIT])

static size_t
count_irredundant_non_garbage_clauses (struct solver *solver,
				       struct clause **last_ptr)
{
  size_t res = 0;
  struct clause *last = 0;
  for (all_watches (watch, solver->watches))
    {
      assert (!binary_pointer (watch));
      if (watch->garbage)
	continue;
      if (watch->redundant)
	continue;
      struct clause *clause = watch->clause;
      last = clause;
      res++;
    }
  *last_ptr = last;
  return res;
}

// *INDENT-OFF*

static double base_values[][2] = {
  {0.0, 2.00},
  {3.0, 2.50},
  {4.0, 2.85},
  {5.0, 3.70},
  {6.0, 5.10},
  {7.0, 7.40}
};

// *INDENT-ON*

static double
interpolate_base (double size)
{
  const size_t num_base_values = sizeof base_values / sizeof *base_values;
  size_t i = 0;
  while (i + 2 < num_base_values &&
	 (base_values[i][0] > size || base_values[i + 1][0] < size))
    i++;
  double x2 = base_values[i + 1][0], x1 = base_values[i][0];
  double y2 = base_values[i + 1][1], y1 = base_values[i][1];
  double dx = x2 - x1, dy = y2 - y1;
  assert (dx);
  double res = dy * (size - x1) / dx + y1;
  assert (res > 0);
  if (res < 1.01)
    res = 1.01;
  return res;
}

static void
initialize_break_table (struct walker *walker, double length)
{
  double epsilon = 1;
  unsigned maxbreak = 0;
  struct solver *solver = walker->solver;
  uint64_t walked = solver->statistics.walked;
  const double base = (walked & 1) ? 2.0 : interpolate_base (length);
  verbose (solver, "propability exponential sample base %.2f", base);
  assert (base > 1);
  for (;;)
    {
      double next = epsilon / base;
      if (!next)
	break;
      maxbreak++;
      PUSH (walker->breaks, epsilon);
      epsilon = next;
    }
  walker->epsilon = epsilon;
  walker->maxbreak = maxbreak;
  WOG ("epsilon score %g of %u break count and more", epsilon, maxbreak);
}

static void *
min_max_tag_pointer (bool redundant, unsigned first, unsigned second)
{
  assert (first != second);
  unsigned min = first < second ? first : second;
  unsigned max = first < second ? second : first;
  return tag_pointer (redundant, min, max);
}

static double
connect_counters (struct walker *walker, struct clause *last)
{
  struct solver *solver = walker->solver;
  signed char *values = solver->values;
  struct counter *p = walker->counters;
  double sum_lengths = 0;
  size_t clauses = 0;
  uint64_t ticks = 1;
  for (all_watches (watch, solver->watches))
    {
      if (watch->garbage)
	continue;
      if (watch->redundant)
	continue;
      ticks++;
      struct clause *clause = watch->clause;
      unsigned count = 0;
      unsigned length = 0;
      for (all_literals_in_clause (lit, clause))
	{
	  signed char value = values[lit];
	  if (!value)
	    continue;
	  count += (value > 0);
	  PUSH (walker->occurrences[lit], p);
	  ticks++;
	  length++;
	}
      sum_lengths += length;
      p->count = count;
      p->clause = clause;
      if (!count)
	{
	  set_insert (&walker->unsatisfied, p);
	  LOGCLAUSE (clause, "initially broken");
	}
      clauses++;
      p++;
      if (clause == last)
	break;
    }
  for (all_literals (lit))
    {
      if (values[lit] >= 0)
	continue;
      struct counters * counters = &OCCURRENCES (lit);
      unsigned * binaries = counters->binaries;
      if (!binaries)
	continue;
      for (unsigned * p = binaries, other; (other = *p) != INVALID; p++)
	if (lit < other && values[other] < 0)
	  {
	    LOGBINARY (false, lit, other, "initially broken");
	    void * ptr = tag_pointer (false, lit, other);
	    assert (ptr == min_max_tag_pointer (false, lit, other));
	    set_insert (&walker->unsatisfied, ptr);
	  }
    }
  double average_length = average (sum_lengths, clauses);
  verbose (solver, "average clause length %.2f", average_length);
  very_verbose (solver, "connecting counters took %" PRIu64 " extra ticks",
		ticks);
  walker->extra += ticks;
  return average_length;
}

static void
warming_up_saved_phases (struct solver *solver)
{
  assert (!solver->level);
  assert (solver->trail.propagate == solver->trail.end);
  uint64_t decisions = 0, conflicts = 0;
  while (solver->unassigned)
    {
      decisions++;
      decide (solver);
      if (!propagate (solver, false))
	conflicts++;
    }
  if (solver->level)
    backtrack (solver, 0);
  verbose (solver,
	   "warmed-up phases with %" PRIu64 " decisions and %" PRIu64
	   " conflicts", decisions, conflicts);
}

static void
import_decisions (struct walker *walker)
{
  struct solver *solver = walker->solver;
  assert (solver->context == WALK);
  uint64_t saved = solver->statistics.contexts[WALK].ticks;
  warming_up_saved_phases (solver);
  uint64_t extra = solver->statistics.contexts[WALK].ticks - saved;
  walker->extra += extra;
  very_verbose (solver, "warming up needed %" PRIu64 " extra ticks", extra);
  signed char *values = solver->values;
  unsigned pos = 0, neg = 0, ignored = 0;
  signed char *p = values;
  for (all_variables (v))
    {
      signed char phase = v->saved;
      if (*p)
	{
	  phase = 0;
	  ignored++;
	}
      else
	{
	  pos += (phase > 0);
	  neg += (phase < 0);
	  v->level = INVALID;
	}
      *p++ = phase;
      *p++ = -phase;
    }
  assert (p == values + 2 * solver->size);
  verbose (solver, "imported %u positive %u negative decisions (%u ignored)",
	   pos, neg, ignored);
}

static void
fix_values_after_local_search (struct solver *solver)
{
  signed char *values = solver->values;
  memset (values, 0, 2 * solver->size);
  for (all_elements_on_stack (unsigned, lit, solver->trail))
    {
      values[lit] = 1;
      values[NOT (lit)] = -1;
      VAR (lit)->level = 0;
    }
}

static void
set_walking_limits (struct walker *walker)
{
  struct solver *solver = walker->solver;
  struct statistics *statistics = &solver->statistics;
  struct last *last = &solver->last;
  uint64_t search = statistics->contexts[SEARCH].ticks;
  uint64_t walk = statistics->contexts[WALK].ticks;
  uint64_t ticks = search - last->walk;
  uint64_t extra = walker->extra;
  uint64_t effort = extra + WALK_EFFORT * ticks;
  walker->limit = walk + effort;
  very_verbose (solver, "walking effort %" PRIu64 " ticks = "
		"%" PRIu64 " + %g * %" PRIu64
		" = %" PRIu64 " + %g * (%" PRIu64 " - %" PRIu64 ")",
		effort, extra, (double) WALK_EFFORT, ticks,
		extra, (double) WALK_EFFORT, search, last->walk);
}

static void
disconnect_references (struct solver * solver, struct watches * saved)
{
  size_t disconnected = 0;
  for (all_literals (lit))
    {
      struct references * watches = &REFERENCES (lit);
      for (all_watches (watch, *watches))
	if (binary_pointer (watch))
	  {
	    assert (redundant_pointer (watch));
	    assert (lit_pointer (watch) == lit);
	    unsigned other = other_pointer (watch);
	    if (other < lit)
	      PUSH (*saved, watch);
	  }
      disconnected += SIZE (*watches);
      RELEASE (*watches);
    }
}

static void
release_references (struct solver * solver)
{
  for (all_literals (lit))
    RELEASE (REFERENCES (lit));
}

static void
reconnect_watches (struct solver * solver, struct watches * saved)
{
  size_t reconnected = 0;
  for (all_watches (watch, solver->watches))
    {
      assert (!binary_pointer (watch));
      unsigned * literals = watch->clause->literals;
      watch->sum = literals[0] ^ literals[1];
      push_watch (solver, literals[0], watch);
      push_watch (solver, literals[1], watch);
      reconnected++;
    }
  for (all_watches (lit_watch, *saved))
    {
      assert (binary_pointer (lit_watch));
      assert (redundant_pointer (lit_watch));
      unsigned lit = lit_pointer (lit_watch);
      unsigned other = other_pointer (lit_watch);
      struct watch * other_watch = tag_pointer (true, other, lit);
      push_watch (solver, lit, lit_watch);
      push_watch (solver, other, other_watch);
    }
  very_verbose (solver, "reconnected %zu clauses", reconnected);
  solver->trail.propagate = solver->trail.begin;
}

static struct walker *
new_walker (struct solver *solver)
{
  struct clause *last = 0;
  size_t clauses = count_irredundant_non_garbage_clauses (solver, &last);

  verbose (solver, "local search over %zu clauses %.0f%%", clauses,
	   percent (clauses, solver->statistics.irredundant));

  struct walker * walker = allocate_and_clear_block (sizeof *walker);
  
  disconnect_references (solver, &walker->saved);

  walker->solver = solver;
  walker->counters =
    allocate_and_clear_array (clauses, sizeof *walker->counters);
  walker->occurrences = (struct counters *) solver->references;

  import_decisions (walker);
  double length = connect_counters (walker, last);
  set_walking_limits (walker);
  initialize_break_table (walker, length);

  walker->initial = walker->minimum = walker->unsatisfied.size;
  verbose (solver, "initially %zu clauses unsatisfied", walker->minimum);

  return walker;
}

static void
delete_walker (struct walker *walker)
{
  struct solver *solver = walker->solver;
  free (walker->counters);
  free (walker->unsatisfied.table);
  RELEASE (walker->literals);
  RELEASE (walker->trail);
  RELEASE (walker->scores);
  RELEASE (walker->breaks);
  release_references (solver);
  reconnect_watches (solver, &walker->saved);
  RELEASE (walker->saved);
  free (walker);
}

static unsigned
break_count (struct walker *walker, unsigned lit)
{
  struct solver * solver = walker->solver;
  signed char * values = solver->values;
  unsigned not_lit = NOT (lit);
  assert (values[not_lit] > 0);
  unsigned res = 0;
  struct counters * counters = &OCCURRENCES (not_lit);
  unsigned * binaries = counters->binaries;
  if (binaries)
    for (unsigned * p = binaries, other; (other = *p) != INVALID; p++)
	if (values[other] <= 0)
	  res++;
  for (all_counters (counter, *counters))
    if (binary_pointer (counter))
      {
	assert (lit_pointer (counter) == not_lit);
	unsigned other = other_pointer (counter);
	if (values[other] <= 0)
	  res++;
      }
    else if (counter->count == 1)
      res++;
  return res;
}

static double
break_score (struct walker *walker, unsigned lit)
{
  unsigned count = break_count (walker, lit);
  assert (SIZE (walker->breaks) == walker->maxbreak);
  double res;
  if (count >= walker->maxbreak)
    res = walker->epsilon;
  else
    res = walker->breaks.begin[count];
  WOG ("break count of %s is %u and score %g", LOGLIT (lit), count, res);
  return res;
}

static void
save_all_values (struct walker *walker)
{
  assert (walker->best == INVALID);
  struct solver *solver = walker->solver;
  signed char *p = solver->values;
  for (all_variables (v))
    {
      signed char value = *p;
      p += 2;
      if (value)
	v->saved = value;
    }
  walker->best = 0;
}

static void
save_walker_trail (struct walker *walker, bool keep)
{
  assert (walker->best != INVALID);
  unsigned *begin = walker->trail.begin;
  unsigned *best = begin + walker->best;
  unsigned *end = walker->trail.end;
  assert (best <= end);
  struct solver *solver = walker->solver;
  struct variable *variables = solver->variables;
  for (unsigned *p = begin; p != best; p++)
    {
      unsigned lit = *p;
      signed phase = SGN (lit) ? -1 : 1;
      unsigned idx = IDX (lit);
      struct variable *v = variables + idx;
      v->saved = phase;
    }
  if (!keep)
    return;
  unsigned *q = begin;
  for (unsigned *p = best; p != end; p++)
    *q++ = *p;
  walker->trail.end = q;
  walker->best = 0;
}

static void
save_final_minimum (struct walker *walker)
{
  struct solver *solver = walker->solver;

  if (walker->minimum == walker->initial)
    {
      verbose (solver, "minimum number of unsatisfied clauses %zu unchanged",
	       walker->minimum);
      return;
    }

  verbose (solver, "saving improved assignment of %zu unsatisfied clauses",
	   walker->minimum);

  if (walker->best && walker->best != INVALID)
    save_walker_trail (walker, false);
}

static void
push_flipped (struct walker *walker, unsigned flipped)
{
  if (walker->best == INVALID)
    return;
  struct solver *solver = walker->solver;
  struct unsigneds *trail = &walker->trail;
  size_t size = SIZE (*trail);
  unsigned limit = solver->size / 4 + 1;
  if (size < limit)
    PUSH (*trail, flipped);
  else if (walker->best)
    {
      save_walker_trail (walker, true);
      PUSH (*trail, flipped);
    }
  else
    {
      CLEAR (*trail);
      walker->best = INVALID;
    }
}

static void
new_minimium (struct walker *walker, unsigned unsatisfied)
{
  very_verbose (walker->solver,
		"new minimum %u of unsatisfied clauses after %" PRIu64
		" flips", unsatisfied, walker->flips);
  walker->minimum = unsatisfied;
  if (walker->best == INVALID)
    save_all_values (walker);
  else
    walker->best = SIZE (walker->trail);
}

static void
update_minimum (struct walker *walker, unsigned lit)
{
  (void) lit;

  unsigned unsatisfied = walker->unsatisfied.size;
  WOG ("making literal %s gives %u unsatisfied clauses",
       LOGLIT (lit), unsatisfied);

  if (unsatisfied < walker->minimum)
    new_minimium (walker, unsatisfied);
}

static void
make_literal (struct walker *walker, unsigned lit)
{
  struct solver *solver = walker->solver;
  signed char * values = solver->values;
  assert (values[lit] > 0);
  uint64_t ticks = 1;
  struct counters * counters = &OCCURRENCES (lit);
  for (all_counters (counter, *counters))
    {
      ticks++;
      assert (!binary_pointer (counter));
      if (counter->count++)
	continue;
      LOGCLAUSE (counter->clause, "literal %s makes", LOGLIT (lit));
      set_remove (&walker->unsatisfied, counter);
      ticks++;
    }
  unsigned * binaries = counters->binaries;
  if (binaries)
    {
      ticks++;
      for (unsigned * p = binaries, other; (other = *p) != INVALID; p++)
	if (values[other] < 0)
	  {
	    LOGBINARY (false, lit, other, "literal %s makes", LOGLIT (lit));
	    void * ptr = min_max_tag_pointer (false, lit, other);
	    set_remove (&walker->unsatisfied, ptr);
	  }
    }
  solver->statistics.contexts[WALK].ticks += ticks;
}

static void
break_literal (struct walker *walker, unsigned lit)
{
  struct solver *solver = walker->solver;
  signed char * values = solver->values;
  assert (values[lit] < 0);
  uint64_t ticks = 1;
  struct counters *counters = &OCCURRENCES (lit);
  for (all_counters (counter, *counters))
    {
      ticks++;
      assert (!binary_pointer (counter));
      assert (counter->count);
      if (--counter->count)
	continue;
      LOGCLAUSE (counter->clause, "literal %s breaks", LOGLIT (lit));
      set_insert (&walker->unsatisfied, counter);
      ticks++;
    }
  unsigned * binaries = counters->binaries;
  if (binaries)
    {
      ticks++;
      for (unsigned * p = binaries, other; (other = *p) != INVALID; p++)
	if (values[other] < 0)
	  {
	    LOGBINARY (false, lit, other, "literal %s breaks", LOGLIT (lit));
	    void * ptr = min_max_tag_pointer (false, lit, other);
	    set_insert (&walker->unsatisfied, ptr);
	  }
    }
  solver->statistics.contexts[WALK].ticks += ticks;
}

static void
flip_literal (struct walker *walker, unsigned lit)
{
  struct solver *solver = walker->solver;
  signed char *values = solver->values;
  assert (values[lit] < 0);
  solver->statistics.flips++;
  walker->flips++;
  unsigned not_lit = NOT (lit);
  values[lit] = 1, values[not_lit] = -1;
  break_literal (walker, not_lit);
  make_literal (walker, lit);
}

static unsigned
pick_literal_to_flip (struct walker *walker,
                      size_t size, unsigned * literals)
{
  assert (EMPTY (walker->literals));
  assert (EMPTY (walker->scores));

  struct solver *solver = walker->solver;
  signed char *values = solver->values;

  unsigned res = INVALID;
  double total = 0, score = -1;

  unsigned * end = literals + size;

  for (unsigned * p = literals; p != end; p++)
    {
      unsigned lit = *p;
      if (!values[lit])
	continue;
      PUSH (walker->literals, lit);
      score = break_score (walker, lit);
      PUSH (walker->scores, score);
      total += score;
      res = lit;
    }

  double random = random_double (solver);
  assert (0 <= random), assert (random < 1);
  double threshold = random * total;

  double sum = 0, *scores = walker->scores.begin;

  for (unsigned * p = literals; p != end; p++)
    {
      unsigned other = *p;
      if (!values[other])
	continue;
      double tmp = *scores++;
      sum += tmp;
      if (threshold >= sum)
	continue;
      res = other;
      score = tmp;
      break;
    }

  assert (res != INVALID);
  assert (score >= 0);

  CLEAR (walker->literals);
  CLEAR (walker->scores);

  LOG ("flipping literal %s with score %g", LOGLIT (res), score);

  return res;
}

static void
walking_step (struct walker *walker)
{
  struct set *unsatisfied = &walker->unsatisfied;
  struct solver * solver = walker->solver;
  struct counter * counter = random_set (solver, unsatisfied);
  unsigned lit;
  if (binary_pointer (counter))
    {
      unsigned first = lit_pointer (counter);
      unsigned second = other_pointer (counter);
      assert (!redundant_pointer (counter));
      unsigned literals[2] = { first, second };
      LOGBINARY (false, first, second, "picked broken");
      lit = pick_literal_to_flip (walker, 2, literals);
    }
  else
    {
      assert (!counter->count);
      struct clause * clause = counter->clause;
      LOGCLAUSE (clause, "picked broken");
      lit = pick_literal_to_flip (walker, clause->size, clause->literals);
    }
  flip_literal (walker, lit);
  push_flipped (walker, lit);
  update_minimum (walker, lit);
}

static void
walking_loop (struct walker *walker)
{
  struct solver *solver = walker->solver;
  uint64_t *ticks = &solver->statistics.contexts[WALK].ticks;
  uint64_t limit = walker->limit;
  while (walker->minimum && *ticks <= limit)
    walking_step (walker);
}

static void
local_search (struct solver *solver)
{
  STOP_SEARCH_AND_START (walk);
  assert (solver->context == SEARCH);
  solver->context = WALK;
  solver->statistics.walked++;
  if (solver->level)
    backtrack (solver, 0);
  if (solver->last.fixed != solver->statistics.fixed)
    mark_satisfied_clauses_as_garbage (solver);
  struct walker * walker = new_walker (solver);
  walking_loop (walker);
  save_final_minimum (walker);
  verbose (solver, "walker flipped %" PRIu64 " literals", walker->flips);
  delete_walker (walker);
  fix_values_after_local_search (solver);
  solver->last.walk = solver->statistics.contexts[SEARCH].ticks;
  assert (solver->context == WALK);
  solver->context = SEARCH;
  STOP_AND_START_SEARCH (walk);
}

static char
rephase_walk (struct solver *solver)
{
  local_search (solver);
  for (all_variables (v))
    v->target = v->saved;
  return 'W';
}

static char
rephase_best (struct solver *solver)
{
  for (all_variables (v))
    v->target = v->saved = v->best;
  return 'B';
}

static char
rephase_inverted (struct solver *solver)
{
  for (all_variables (v))
    v->target = v->saved = -INITIAL_PHASE;
  return 'I';
}

static char
rephase_original (struct solver *solver)
{
  for (all_variables (v))
    v->target = v->saved = INITIAL_PHASE;
  return 'O';
}

static bool
rephasing (struct solver *solver)
{
  return solver->stable && SEARCH_CONFLICTS > solver->limits.rephase;
}

// *INDENT-OFF*

static char (*schedule[])(struct solver *) =
{
  rephase_original, rephase_best, rephase_walk,
  rephase_inverted, rephase_best, rephase_walk,
};

// *INDENT-ON*

static void
rephase (struct solver *solver)
{
  if (solver->level)
    backtrack (solver, 0);
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  uint64_t rephased = ++statistics->rephased;
  size_t size_schedule = sizeof schedule / sizeof *schedule;
  char type = schedule[rephased % size_schedule] (solver);
  verbose (solver, "resetting number of target assigned %u", solver->target);
  solver->target = 0;
  if (type == 'B')
    {
      verbose (solver, "resetting number of best assigned %u", solver->best);
      solver->best = 0;
    }
  limits->rephase = SEARCH_CONFLICTS;
  limits->rephase += REPHASE_INTERVAL * rephased * sqrt (rephased);
  verbose (solver, "next rephase limit at %" PRIu64 " conflicts",
	   limits->rephase);
  report (solver, type);
}

static void
iterate (struct solver *solver)
{
  solver->iterating = false;
  report (solver, 'i');
}

static void
start_search (struct solver *solver)
{
  START (search);
  assert (!solver->stable);
  START (focused);
  report (solver, '{');
}

static void
stop_search (struct solver *solver, int res)
{
  if (solver->stable)
    {
      report (solver, ']');
      STOP (stable);
    }
  else
    {
      report (solver, '}');
      STOP (focused);
    }
  if (res == 10)
    report (solver, '1');
  else if (res == 20)
    report (solver, '0');
  else
    report (solver, '?');
  STOP (search);
}

static bool
conflict_limit_hit (struct solver *solver)
{
  long limit = solver->limits.conflicts;
  if (limit < 0)
    return false;
  uint64_t conflicts = SEARCH_CONFLICTS;
  if (conflicts < (unsigned long) limit)
    return false;
  verbose (solver, "conflict limit %ld hit at %" PRIu64 " conflicts", limit,
	   conflicts);
  return true;
}

static int
solve (struct solver *solver)
{
  start_search (solver);
  int res = solver->inconsistent ? 20 : 0;
  while (!res)
    {
      struct watch *conflict = propagate (solver, true);
      if (conflict)
	{
	  if (!analyze (solver, conflict))
	    res = 20;
	}
      else if (!solver->unassigned)
	set_satisfied (solver), res = 10;
      else if (solver->iterating)
	iterate (solver);
      else if (solver->root->terminate)
	break;
#if 0
      else if (!solver->statistics.walked)
	local_search (solver);
#endif
      else if (conflict_limit_hit (solver))
	break;
      else if (reducing (solver))
	reduce (solver);
      else if (restarting (solver))
	restart (solver);
      else if (switching_mode (solver))
	switch_mode (solver);
      else if (rephasing (solver))
	rephase (solver);
      else if (!import_unit (solver) && !import_clause (solver))
	decide (solver);
    }
  stop_search (solver, res);
  return res;
}

static void *
solve_routine (void *ptr)
{
  struct solver *solver = ptr;
  int res = solve (solver);
  assert (solver->status == res);
  (void) res;
  return solver;
}

/*------------------------------------------------------------------------*/

static bool
has_suffix (const char *str, const char *suffix)
{
  size_t len = strlen (str);
  size_t suffix_len = strlen (suffix);
  if (len < suffix_len)
    return 0;
  return !strcmp (str + len - suffix_len, suffix);
}

static bool
looks_like_dimacs (const char *path)
{
  return has_suffix (path, ".cnf") || has_suffix (path, ".dimacs") ||
    has_suffix (path, ".cnf.bz2") || has_suffix (path, ".dimacs.bz2") ||
    has_suffix (path, ".cnf.gz") || has_suffix (path, ".dimacs.gz") ||
    has_suffix (path, ".cnf.xz") || has_suffix (path, ".dimacs.xz");
}

/*------------------------------------------------------------------------*/

static struct file dimacs;

static void parse_error (const char *, ...)
  __attribute__((format (printf, 1, 2)));

static void
parse_error (const char *fmt, ...)
{
  fprintf (stderr, "gimsatul: parse error: at line %" PRIu64 " in '%s': ",
	   dimacs.lines, dimacs.path);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static bool witness = true;

static FILE *
open_and_read_from_pipe (const char *path, const char *fmt)
{
  char *cmd = allocate_block (strlen (path) + strlen (fmt));
  sprintf (cmd, fmt, path);
  FILE *file = popen (cmd, "r");
  free (cmd);
  return file;
}

#include "config.h"

struct options
{
  long long conflicts;
  unsigned seconds;
  unsigned threads;
};

static const char *
parse_long_option (const char * arg, const char * match)
{
  if (arg[0] != '-')
    return 0;
  if (arg[1] != '-')
    return 0;
  const char * p = arg + 2;
  for (const char * q = match; *q; q++, p++)
    if (*q != *p)
      return 0;
  if (*p++ != '=')
    return 0;
  const char * res = p;
  int ch;
  if (!(ch = *p++))
    return 0;
  if (!isdigit (ch))
    return 0;
  while ((ch = *p++) && isdigit (ch))
    ;
  return ch ? 0 : res;
}

static void
parse_options (int argc, char **argv, struct options *opts)
{
  opts->conflicts = -1;
  opts->seconds = 0;
  opts->threads = 0;
  for (int i = 1; i != argc; i++)
    {
      const char *opt = argv[i], * arg;
      if (!strcmp (opt, "-a") || !strcmp (opt, "--ascii"))
	binary_proof_format = false;
      else if (!strcmp (opt, "-f") || !strcmp (opt, "--force"))
	force = true;
      else if (!strcmp (opt, "-h") || !strcmp (opt, "--help"))
	{
	  printf (usage, (size_t) MAX_THREADS);
	  exit (0);
	}
      else if (!strcmp (opt, "-l") || !strcmp (opt, "--log") || !strcmp (opt, "logging"))
#ifdef LOGGING
	{
	  logging = true;
	  verbosity = MAX_VERBOSITY;
	}
#else
	die ("invalid option '%s' (compiled without logging support)", opt);
#endif
      else if (!strcmp (opt, "-n") || !strcmp (opt, "--no-witness"))
	witness = false;
      else if (!strcmp (opt, "-v"))
	{
	  if (verbosity < MAX_VERBOSITY)
	    verbosity++;
	}
      else if (!strcmp (opt, "--version"))
	{
	  printf ("%s\n", VERSION);
	  exit (0);
	}
      else if ((arg = parse_long_option (opt, "conflicts")))
	{
	  if (opts->conflicts >= 0)
	    die ("multiple '--conflicts=%lld' and '%s'", opts->conflicts, opt);
	  if (sscanf (arg, "%lld", &opts->conflicts) != 1)
	    die ("invalid argument in '%s'", opt);
	  if (opts->conflicts < 0)
	    die ("invalid negative argument in '%s'", opt);
	}
      else if ((arg = parse_long_option (opt, "threads")))
	{
	  if (opts->threads)
	    die ("multiple '--threads=%u' and '%s'", opts->seconds, opt);
	  if (sscanf (arg, "%u", &opts->threads) != 1)
	    die ("invalid argument in '%s'", opt);
	  if (!opts->threads)
	    die ("invalid zero argument in '%s'", opt);
	  if (opts->threads > MAX_THREADS)
	    die ("invalid argument in '%s' (maximum %zu)", opt, MAX_THREADS);
	}
      else if ((arg = parse_long_option (opt, "time")))
	{
	  if (opts->seconds)
	    die ("multiple '--time=%u' and '%s'", opts->seconds, opt);
	  if (sscanf (arg, "%u", &opts->seconds) != 1)
	    die ("invalid argument in '%s'", opt);
	  if (!opts->seconds)
	    die ("invalid zero argument in '%s'", opt);
	}
      else if (opt[0] == '-' && opt[1])
	die ("invalid option '%s' (try '-h')", opt);
      else if (proof.file)
	die ("too many arguments");
      else if (dimacs.file)
	{
	  if (!strcmp (opt, "-"))
	    {
	      proof.path = "<stdout>";
	      proof.file = stdout;
	      binary_proof_format = false;
	    }
	  else if (!force && looks_like_dimacs (opt))
	    die ("proof file '%s' looks like a DIMACS file (use '-f')", opt);
	  else if (!(proof.file = fopen (opt, "w")))
	    die ("can not open and write to '%s'", opt);
	  else
	    {
	      proof.path = opt;
	      proof.close = true;
	    }
	}
      else
	{
	  if (!strcmp (opt, "-"))
	    {
	      dimacs.path = "<stdin>";
	      dimacs.file = stdin;
	    }
	  else if (has_suffix (opt, ".bz2"))
	    {
	      dimacs.file = open_and_read_from_pipe (opt, "bzip2 -c -d %s");
	      dimacs.close = 2;
	    }
	  else if (has_suffix (opt, ".gz"))
	    {
	      dimacs.file = open_and_read_from_pipe (opt, "gzip -c -d %s");
	      dimacs.close = 2;
	    }
	  else if (has_suffix (opt, ".xz"))
	    {
	      dimacs.file = open_and_read_from_pipe (opt, "xz -c -d %s");
	      dimacs.close = 2;
	    }
	  else
	    {
	      dimacs.file = fopen (opt, "r");
	      dimacs.close = 1;
	    }
	  if (!dimacs.file)
	    die ("can not open and read from '%s'", opt);
	  dimacs.path = opt;
	}
    }

  if (!dimacs.file)
    {
      dimacs.path = "<stdin>";
      dimacs.file = stdin;
    }

  if (!opts->threads)
    opts->threads = 1;

  if (opts->threads <= 10)
    prefix_format = "c%-1u ";
  else if (opts->threads <= 100)
    prefix_format = "c%-2u ";
  else if (opts->threads <= 1000)
    prefix_format = "c%-3u ";
  else if (opts->threads <= 10000)
    prefix_format = "c%-4u ";
  else
    prefix_format = "c%-5u ";
}

static void
set_limits (struct solver *solver, long long conflicts)
{
  if (solver->inconsistent)
    return;
  assert (!solver->stable);
  assert (!SEARCH_CONFLICTS);
  struct limits *limits = &solver->limits;
  limits->mode = MODE_INTERVAL;
  limits->reduce = REDUCE_INTERVAL;
  limits->restart = FOCUSED_RESTART_INTERVAL;
  limits->rephase = REPHASE_INTERVAL;
  verbose (solver, "reduce interval of %" PRIu64 " conflict", limits->reduce);
  verbose (solver, "restart interval of %" PRIu64 " conflict",
	   limits->restart);
  verbose (solver, "initial mode switching interval of %" PRIu64 " conflicts",
	   limits->mode);
  if (conflicts >= 0)
    {
      limits->conflicts = conflicts;
      message (solver, "conflict limit set to %lld conflicts", conflicts);
    }
}

static void
print_banner (void)
{
  printf ("c GimSATul SAT Solver\n");
  printf ("c Copyright (c) 2022 Armin Biere University of Freiburg\n");
  fputs ("c\n", stdout);
  printf ("c Version %s%s\n", VERSION, GITID ? " " GITID : "");
  printf ("c %s\n", COMPILER);
  printf ("c %s\n", BUILD);
}

/*------------------------------------------------------------------------*/

static int
next_char (void)
{
  int res = getc (dimacs.file);
  if (res == '\r')
    {
      res = getc (dimacs.file);
      if (res != '\n')
	return EOF;
    }
  if (res == '\n')
    dimacs.lines++;
  return res;
}

static bool
parse_int (int *res_ptr, int prev, int *next)
{
  int ch = prev == EOF ? next_char () : prev;
  int sign = 1;
  if (ch == '-')
    {
      sign = -1;
      ch = next_char ();
      if (!isdigit (ch) || ch == '0')
	return false;
    }
  else if (!isdigit (ch))
    return false;
  unsigned tmp = ch - '0';
  while (isdigit (ch = next_char ()))
    {
      if (!tmp && ch == '0')
	return false;
      if (UINT_MAX / 10 < tmp)
	return false;
      tmp *= 10;
      unsigned digit = ch - '0';
      if (UINT_MAX - digit < tmp)
	return false;
      tmp += digit;
    }
  if (ch == EOF)
    return false;
  int res;
  if (sign > 0)
    {
      if (tmp > 0x1fffffffu)
	return false;
      res = tmp;
    }
  else
    {
      assert (sign < 0);
      if (tmp > 0x20000000u)
	return false;
      if (tmp == 0x20000000u)
	res = INT_MIN;
      else
	res = -tmp;
    }
  *next = ch;
  *res_ptr = res;
  return true;
}

#ifndef NDEBUG
static struct unsigneds original;
#endif

static struct root *
parse_dimacs_file ()
{
  int ch;
  while ((ch = next_char ()) == 'c')
    {
      while ((ch = next_char ()) != '\n')
	if (ch == EOF)
	  parse_error ("unexpected end-of-file in header comment");
    }
  if (ch != 'p')
    parse_error ("expected 'c' or 'p'");
  int variables, expected;
  if (next_char () != ' ' ||
      next_char () != 'c' ||
      next_char () != 'n' ||
      next_char () != 'f' ||
      next_char () != ' ' ||
      !parse_int (&variables, EOF, &ch) ||
      variables < 0 ||
      ch != ' ' || !parse_int (&expected, EOF, &ch) || expected < 0)
  INVALID_HEADER:
    parse_error ("invalid 'p cnf ...' header line");
  if (variables > MAX_VAR)
    parse_error ("too many variables (maximum %u)", MAX_VAR);
  while (ch == ' ' || ch == '\t')
    ch = next_char ();
  if (ch != '\n')
    goto INVALID_HEADER;
  printf ("c\nc parsed header with %d variables\n", variables);
  fflush (stdout);
  struct root *root = new_root (variables);
  struct solver *solver = new_solver (root);
  signed char *marked = allocate_and_clear_block (variables);
  int signed_lit = 0, parsed = 0;
  bool trivial = false;
  struct unsigneds *clause = &solver->clause;
  for (;;)
    {
      ch = next_char ();
      if (ch == EOF)
	{
	  if (signed_lit)
	    parse_error ("terminating zero missing");
	  if (parsed != expected)
	    parse_error ("clause missing");
	  break;
	}
      if (ch == ' ' || ch == '\t' || ch == '\n')
	continue;
      if (ch == 'c')
	{
	SKIP_BODY_COMMENT:
	  while ((ch = next_char ()) != '\n')
	    if (ch == EOF)
	      parse_error ("invalid end-of-file in body comment");
	  continue;
	}
      if (!parse_int (&signed_lit, ch, &ch))
	parse_error ("failed to parse literal");
      if (signed_lit == INT_MIN || abs (signed_lit) > variables)
	parse_error ("invalid literal %d", signed_lit);
      if (parsed == expected)
	parse_error ("too many clauses");
      if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n')
	parse_error ("invalid character after '%d'", signed_lit);
      if (signed_lit)
	{
	  unsigned idx = abs (signed_lit) - 1;
	  assert (idx < (unsigned) variables);
	  signed char sign = (signed_lit < 0) ? -1 : 1;
	  signed char mark = marked[idx];
	  unsigned unsigned_lit = 2 * idx + (sign < 0);
#ifndef NDEBUG
	  PUSH (original, unsigned_lit);
#endif
	  if (mark == -sign)
	    {
	      LOG ("skipping trivial clause");
	      trivial = true;
	    }
	  else if (!mark)
	    {
	      PUSH (*clause, unsigned_lit);
	      marked[idx] = sign;
	    }
	  else
	    assert (mark == sign);
	}
      else
	{
#ifndef NDEBUG
	  PUSH (original, INVALID);
#endif
	  parsed++;
	  unsigned *literals = clause->begin;
	  if (!solver->inconsistent && !trivial)
	    {
	      const size_t size = SIZE (*clause);
	      assert (size <= solver->size);
	      if (!size)
		set_inconsistent (solver, "found empty original clause");
	      else if (size == 1)
		{
		  const unsigned unit = *clause->begin;
		  const signed char value = solver->values[unit];
		  if (value < 0)
		    {
		      set_inconsistent (solver, "found inconsistent unit");
		      TRACE_EMPTY ();
		    }
		  else if (!value)
		    assign_unit (solver, unit);
		}
	      else if (size == 2)
		new_global_binary_clause (solver, false,
					  literals[0], literals[1]);
	      else
		new_large_clause (solver, size, literals, false, 0);
	    }
	  else
	    trivial = false;
	  for (all_elements_on_stack (unsigned, unsigned_lit, *clause))
	      marked[IDX (unsigned_lit)] = 0;
	  CLEAR (*clause);
	}
      if (ch == 'c')
	goto SKIP_BODY_COMMENT;
    }
  free (marked);
  assert (parsed == expected);
  printf ("c parsed 'p cnf %d %d' DIMACS file '%s'\n",
	  variables, parsed, dimacs.path);
  fflush (stdout);
  assert (dimacs.file);
  if (dimacs.close == 1)
    fclose (dimacs.file);
  if (dimacs.close == 2)
    pclose (dimacs.file);
  return root;
}

/*------------------------------------------------------------------------*/

static char line[80];
static size_t buffered;

static void
flush_line (void)
{
  fwrite (line, 1, buffered, stdout);
  fputc ('\n', stdout);
  buffered = 0;
}

static void
print_signed_literal (int lit)
{
  char buffer[32];
  sprintf (buffer, " %d", lit);
  size_t len = strlen (buffer);
  if (buffered + len >= sizeof line)
    flush_line ();
  if (!buffered)
    line[buffered++] = 'v';
  memcpy (line + buffered, buffer, len);
  buffered += len;
}

static void
print_unsigned_literal (signed char *values, unsigned unsigned_lit)
{
  assert (unsigned_lit < (unsigned) INT_MAX);
  int signed_lit = IDX (unsigned_lit) + 1;
  signed_lit *= values[unsigned_lit];
  print_signed_literal (signed_lit);
}

static void
print_witness (struct solver *solver)
{
  signed char *values = solver->values;
  for (all_indices (idx))
    print_unsigned_literal (values, LIT (idx));
  print_signed_literal (0);
  if (buffered)
    flush_line ();
}

/*------------------------------------------------------------------------*/

static void
clone_solvers (struct root * root, unsigned threads)
{
  if (threads == 1)
    return;
  assert (threads - 1);
  printf ("c trying to clone %u solvers to support %u solver threads\n",
          threads - 1, threads);
  fflush (stdout);
  struct solver * solver = first_solver (root);
  while (SIZE (root->solvers) < threads)
    (void) clone_solver (solver);
}

static void
set_limits_of_all_solvers (struct root * root, long long conflicts)
{
  for (all_solvers (solver))
    set_limits (solver, conflicts);
}

static void
start_running_solver (struct solver *solver)
{
  if (pthread_create (&solver->thread, 0, solve_routine, solver))
    fatal_error ("failed to create solving thread");
}

static void
stop_running_solver (struct solver *solver)
{
  if (pthread_join (solver->thread, 0))
    fatal_error ("failed to join solving thread");
}

static void
run_solvers (struct root * root)
{
  size_t threads = SIZE (root->solvers);
  if (threads > 1)
    {
      printf ("c starting and running %zu solver threads\n", threads);
      fflush (stdout);
      for (all_solvers (solver))
	start_running_solver (solver);

      for (all_solvers (solver))
	stop_running_solver (solver);
    }
  else
    {
      printf ("c running single solver in main thread\n");
      fflush (stdout);
      struct solver * solver = first_solver (root);
      solve_routine (solver);
    }
}

static void
detach_and_delete_solvers (struct root * root)
{
  for (all_solvers (solver))
    {
      detach_solver (root, solver);
      delete_solver (solver);
    }
}

/*------------------------------------------------------------------------*/

static volatile int caught_signal;
static volatile bool catching_signals;
static volatile bool catching_alarm;

static struct root *root;

#define SIGNALS \
SIGNAL(SIGABRT) \
SIGNAL(SIGBUS) \
SIGNAL(SIGILL) \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGTERM)

// *INDENT-OFF*

// Saved previous signal handlers.

#define SIGNAL(SIG) \
static void (*saved_ ## SIG ## _handler)(int);
SIGNALS
#undef SIGNAL
static void (*saved_SIGALRM_handler)(int);

// *INDENT-ON*

static void
reset_alarm_handler (void)
{
  if (atomic_exchange (&catching_alarm, false))
    signal (SIGALRM, saved_SIGALRM_handler);
}

static void
reset_signal_handlers (void)
{
  if (atomic_exchange (&catching_signals, false))
    {
  // *INDENT-OFF*
#define SIGNAL(SIG) \
      signal (SIG, saved_ ## SIG ## _handler);
      SIGNALS
#undef SIGNAL
  // *INDENT-ON*
    }
  reset_alarm_handler ();
}

static void print_root_statistics (struct root *);

static void
caught_message (int sig)
{
  const char *name = "SIGNUNKNOWN";
#define SIGNAL(SIG) \
  if (sig == SIG) name = #SIG;
  SIGNALS
#undef SIGNAL
    if (sig == SIGALRM)
    name = "SIGALRM";
  char buffer[80];
  sprintf (buffer, "c\nc caught signal %d (%s)\nc\n", sig, name);
  size_t bytes = strlen (buffer);
  if (write (1, buffer, bytes) != bytes)
    exit (0);
}

static void
catch_signal (int sig)
{
  if (atomic_exchange (&caught_signal, sig))
    return;
  caught_message (sig);
  reset_signal_handlers ();
  print_root_statistics (root);
  raise (sig);
}

static void
catch_alarm (int sig)
{
  assert (sig == SIGALRM);
  if (!atomic_load (&catching_alarm))
    catch_signal (sig);
  if (atomic_exchange (&caught_signal, sig))
    return;
  if (verbosity)
    caught_message (sig);
  reset_alarm_handler ();
  assert (root);
  atomic_store (&root->terminate, true);
  atomic_store (&caught_signal, 0);
}

static void
set_alarm_handler (unsigned seconds)
{
  assert (seconds);
  assert (!atomic_load (&catching_alarm));
  saved_SIGALRM_handler = signal (SIGALRM, catch_alarm);
  alarm (seconds);
  atomic_store (&catching_alarm, true);
}

static void
set_signal_handlers (unsigned seconds)
{
  assert (!atomic_load (&catching_signals));
  // *INDENT-OFF*
#define SIGNAL(SIG) \
  saved_ ## SIG ##_handler = signal (SIG, catch_signal);
  SIGNALS
#undef SIGNAL
  // *INDENT-ON*
  atomic_store (&catching_signals, true);
  if (seconds)
    set_alarm_handler (seconds);
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

static void
check_witness (struct solver *solver)
{
  signed char *values = solver->values;
  size_t clauses = 0;
  for (unsigned *c = original.begin, *p; c != original.end; c = p + 1)
    {
      bool satisfied = false;
      for (p = c; assert (p != original.end), *p != INVALID; p++)
	if (values[*p] > 0)
	  satisfied = true;
      clauses++;
      if (satisfied)
	continue;
      acquire_message_lock ();
      fprintf (stderr, "gimsatul: error: unsatisfied clause[%zu]", clauses);
      for (unsigned *q = c; q != p; q++)
	fprintf (stderr, " %d", export_literal (*q));
      fputs (" 0\n", stderr);
      release_message_lock ();
      abort ();
    }
}

#endif

/*------------------------------------------------------------------------*/

#define begin_profiles ((struct profile *)(&solver->profiles))
#define end_profiles (&solver->profiles.total)

#define all_profiles(PROFILE) \
struct profile * PROFILE = begin_profiles, \
               * END_ ## PROFILE = end_profiles; \
PROFILE != END_ ## PROFILE; \
++PROFILE

static void
flush_profile (double time, struct profile *profile)
{
  double volatile *p = &profile->start;
  assert (*p >= 0);
  double delta = time - *p;
  *p = time;
  profile->time += delta;
}

static double
flush_profiles (struct solver *solver)
{
  double time = current_time ();
  for (all_profiles (profile))
    if (profile->start >= 0)
      flush_profile (time, profile);

  flush_profile (time, &solver->profiles.total);
  return time;
}

static int
cmp_profiles (struct profile *a, struct profile *b)
{
  if (!a)
    return -1;
  if (!b)
    return -1;
  if (a->time < b->time)
    return -1;
  if (a->time > b->time)
    return 1;
  return strcmp (b->name, a->name);
}

static void
print_profiles (struct solver *solver)
{
  flush_profiles (solver);
  double total = solver->profiles.total.time;
  struct profile *prev = 0;
  fputs ("c\n", stdout);
  for (;;)
    {
      struct profile *next = 0;
      for (all_profiles (tmp))
	if (cmp_profiles (tmp, prev) < 0 && cmp_profiles (next, tmp) < 0)
	  next = tmp;
      if (!next)
	break;
      PRINT ("%10.2f seconds  %5.1f %%  %s",
	     next->time, percent (next->time, total), next->name);
      prev = next;
    }
  PRINT ("---------------------------------------");
  PRINT ("%10.2f seconds  100.0 %%  total", total);
  fputs ("c\n", stdout);
  fflush (stdout);
}

static void
print_solver_statistics (struct solver *solver)
{
  print_profiles (solver);
  double search = solver->profiles.search.time;
  double walk = solver->profiles.total.time;
  struct statistics *s = &solver->statistics;
  uint64_t conflicts = s->contexts[SEARCH].conflicts;
  uint64_t decisions = s->contexts[SEARCH].decisions;
  uint64_t propagations = s->contexts[SEARCH].propagations;
  PRINT ("%-19s %13" PRIu64 " %13.2f per second", "conflicts:",
	  conflicts, average (conflicts, search));
  PRINT ("%-19s %13" PRIu64 " %13.2f per second", "decisions:",
	  decisions, average (decisions, search));
  PRINT ("%-19s %13u %13.2f %% variables", "fixed-variables:",
	  s->fixed, percent (s->fixed, solver->size));
  PRINT ("%-19s %13" PRIu64 " %13.2f thousands per second",
	  "flips:", s->flips, average (s->flips, 1e3 * walk));
  PRINT ("%-19s %13" PRIu64 " %13.2f per learned clause",
	  "learned-literals:", s->learned.literals,
	  average (s->learned.literals, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f per second",
	  "learned-clauses:", s->learned.clauses,
	  average (s->learned.clauses, search));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  unit-clauses:", s->learned.units,
	  percent (s->learned.units, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  binary-clauses:", s->learned.binary,
	  percent (s->learned.binary, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  exported-units:", s->exported.units,
	  percent (s->exported.units, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  exported-binary:", s->exported.binary,
	  percent (s->exported.binary, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  glue1-clauses:", s->learned.glue1,
	  percent (s->learned.glue1, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  imported-units:", s->imported.units,
	  percent (s->imported.units, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  imported-binary:", s->imported.binary,
	  percent (s->imported.binary, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  tier1-clauses:", s->learned.tier1,
	  percent (s->learned.tier1, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  tier2-clauses:", s->learned.tier2,
	  percent (s->learned.tier2, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% learned",
	  "  tier3-clauses:", s->learned.tier3,
	  percent (s->learned.tier3, s->learned.clauses));
  PRINT ("%-19s %13" PRIu64 " %13.2f %% per deduced literals",
	  "minimized-literals:", s->minimized, percent (s->minimized,
							s->deduced));
  PRINT ("%-19s %13" PRIu64 " %13.2f millions per second",
	  "propagations:", propagations, average (propagations,
						  1e6 * search));
  PRINT ("%-19s %13" PRIu64 " %13.2f conflict interval",
	  "reductions:", s->reductions, average (conflicts, s->reductions));
  PRINT ("%-19s %13" PRIu64 " %13.2f conflict interval",
	  "rephased:", s->rephased, average (conflicts, s->rephased));
  PRINT ("%-19s %13" PRIu64 " %13.2f conflict interval",
	  "restarts:", s->restarts, average (conflicts, s->restarts));
  PRINT ("%-19s %13" PRIu64 " %13.2f conflict interval",
	  "switched:", s->switched, average (conflicts, s->switched));
  PRINT ("%-19s %13" PRIu64 " %13.2f flips per walkinterval",
	  "walked:", s->walked, average (s->flips, s->walked));
  fflush (stdout);
}

static void
print_root_statistics (struct root *root)
{
  for (all_solvers (solver))
    {
      print_solver_statistics (solver);
      printf ("c\n");
    }

  double process = process_time ();
  double total = current_time () - start_time;
  double memory = maximum_resident_set_size () / (double) (1 << 20);

  printf ("c %-30s %16.2f sec\n", "process-time:", process);
  printf ("c %-30s %16.2f sec\n", "wall-clock-time:", total);
  printf ("c %-30s %16.2f MB\n", "maximum-resident-set-size:", memory);

  fflush (stdout);
}

/*------------------------------------------------------------------------*/

#define CHECK_TYPE(TYPE,BYTES) \
do { \
  if (sizeof (TYPE) != (BYTES)) \
    fatal_error ("unsupported platform:\n" \
                 "'sizeof (" #TYPE ") == %zu' " \
		 "but expected 'sizeof (" #TYPE ") == %zu'", \
	         sizeof (TYPE), (size_t) (BYTES)); \
} while (0)

static void
check_types (void)
{
  CHECK_TYPE (signed char, 1);
  CHECK_TYPE (unsigned char, 1);
  CHECK_TYPE (unsigned short, 2);
  CHECK_TYPE (atomic_ushort, 2);
  CHECK_TYPE (unsigned, 4);
  CHECK_TYPE (int, 4);
  CHECK_TYPE (size_t, 8);
  CHECK_TYPE (void*, 8);
#if 1
  printf ("c sizeof (struct watch) = %zu\n", sizeof (struct watch));
  printf ("c sizeof (struct clause) = %zu\n", sizeof (struct clause));
  printf ("c sizeof (struct counter) = %zu\n", sizeof (struct counter));
#endif
}

/*------------------------------------------------------------------------*/

int
main (int argc, char **argv)
{
  start_time = current_time ();
  struct options options;
  parse_options (argc, argv, &options);
  print_banner ();
  check_types ();
  if (proof.file)
    {
      printf ("c\nc writing %s proof trace to '%s'\n",
	      binary_proof_format ? "binary" : "ASCII", proof.path);
      fflush (stdout);
    }
  root = parse_dimacs_file ();
  init_root_watches (root);
  clone_solvers (root, options.threads);
  set_limits_of_all_solvers (root, options.conflicts);
  set_signal_handlers (options.seconds);
  run_solvers (root);
  struct solver *winner = (struct solver*) root->winner;
  int res = winner ? winner->status : 0;
  reset_signal_handlers ();
  close_proof ();
  if (res == 20)
    {
      printf ("c\ns UNSATISFIABLE\n");
      fflush (stdout);
    }
  else if (res == 10)
    {
#ifndef NDEBUG
      check_witness (winner);
#endif
      printf ("c\ns SATISFIABLE\n");
      if (witness)
	print_witness (winner);
      fflush (stdout);
    }
  print_root_statistics (root);
  detach_and_delete_solvers (root);
  delete_root (root);
#ifndef NDEBUG
  RELEASE (original);
#endif
  printf ("c\nc exit %d\n", res);
  fflush (stdout);
  return res;
}
