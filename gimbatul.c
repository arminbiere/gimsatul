// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimbatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-a          use ASCII format for proof output\n"
"-h          print this command line option summary\n"
"-f          force reading and writing\n"
#ifdef LOGGING
"-l          enable very verbose internal logging\n"
#endif
"-n          do not print satisfying assignments\n"
"-v          increase verbosity\n"
"--version   print version\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof output file in 'DRAT' format\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
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

#define INVALID UINT_MAX

#define MAX_SCORE 1e150
#define MAX_VERBOSITY 2
#define MINIMIZE_DEPTH 1000

#define FOCUSED_RESTART_INTERVAL 50
#define MODE_INTERVAL 3e3
#define REDUCE_INTERVAL 1e3
#define REPHASE_INTERVAL 1e3
#define STABLE_RESTART_INTERVAL 500

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
#define WATCHES(LIT) (VAR (LIT)->watches[SGN (LIT)])

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

/*------------------------------------------------------------------------*/

struct file
{
  const char *path;
  FILE *file;
  int close;
  size_t lines;
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

struct clause
{
  size_t id:63;
  bool redundant:1;
  unsigned shared;
  unsigned glue;
  unsigned size;
  unsigned literals[];
};

typedef struct clause * clause_pointer;

struct clauses
{
  struct clause **begin, **end, **allocated;
};

struct watch
{
  bool binary:1;
  bool garbage:1;
  bool reason:1;
  bool redundant:1;
  unsigned used:28;
  unsigned glue;
  unsigned middle;
  unsigned sum;
  struct clause *clause;
};

struct watches
{
  struct watch **begin, **end, **allocated;
};

struct variable
{
  unsigned level;
  signed char best;
  signed char saved;
  signed char target;
  bool seen:1;
  bool poison:1;
  bool minimize:1;
  struct watch *reason;
  struct watches watches[2];
};

struct node
{
  double score;
  struct node *child, *prev, *next;
};

struct reluctant
{
  size_t u, v;
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
  size_t mode;
  size_t reduce;
  size_t rephase;
  size_t restart;
  size_t walk;
};

struct intervals
{
  size_t mode;
};

struct averages
{
  struct
  {
    double fast;
    double slow;
  } glue;
  double level;
  double trail;
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
  size_t fixed;
  size_t walk;
};

struct statistics
{
  size_t conflicts;
  size_t decisions;
  size_t flips;
  size_t propagations;
  size_t reductions;
  size_t rephased;
  size_t restarts;
  size_t switched;
  size_t walked;

  struct
  {
    size_t search;
    size_t walk;
  } ticks;

  size_t added;
  size_t deduced;
  size_t fixed;
  size_t irredundant;
  size_t minimized;
  size_t redundant;

  struct
  {
    size_t clauses;
    size_t literals;
  } learned;
};

struct solver
{
  bool inconsistent;
  bool iterating;
  bool stable;
  unsigned size;
  unsigned active;
  unsigned level;
  unsigned unassigned;
  unsigned target;
  unsigned best;
  struct watches watches;
  struct variable *variables;
  signed char *values;
  bool *used;
  size_t random;
  struct unsigneds levels;
  struct queue queue;
  struct unsigneds clause;
  struct unsigneds analyzed;
  struct buffer buffer;
  struct trail trail;
  struct last last;
  struct limits limits;
  struct intervals intervals;
  struct averages averages[2];
  struct reluctant reluctant;
  struct statistics statistics;
  struct profiles profiles;
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
lock_message_mutex (void)
{
  if (pthread_mutex_lock (&message_mutex))
    {
      fprintf (stderr,
	       "gimbatul: locking error: failed to lock message mutex\n");
      fflush (stderr);
      abort ();
    }
}

static void
unlock_message_mutex (void)
{
  if (pthread_mutex_unlock (&message_mutex))
    {
      fprintf (stderr,
	       "gimbatul: locking error: failed to unlock message mutex\n");
      fflush (stderr);
      abort ();
    }
}

static void die (const char *, ...) __attribute__((format (printf, 1, 2)));

static void
die (const char *fmt, ...)
{
  lock_message_mutex ();
  fputs ("gimbatul: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  unlock_message_mutex ();
  exit (1);
}

static void fatal_error (const char *, ...)
  __attribute__((format (printf, 1, 2)));

static void
fatal_error (const char *fmt, ...)
{
  lock_message_mutex ();
  fputs ("gimbatul: fatal error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  unlock_message_mutex ();
  abort ();
}

static void message (const char *, ...)
  __attribute__((format (printf, 1, 2)));

static void
message (const char *fmt, ...)
{
  lock_message_mutex ();
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  unlock_message_mutex ();
}

static int verbosity;

#define verbose(...) \
do { \
  if (verbosity > 1) \
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
static char loglitbuf[4][32];
static unsigned loglitpos;

#define loglitsize (sizeof loglitbuf / sizeof *loglitbuf)

static const char *
loglit (struct solver *solver, unsigned unsigned_lit)
{
  char *res = loglitbuf[loglitpos++];
  if (loglitpos == loglitsize)
    loglitpos = 0;
  int signed_lit = export_literal (unsigned_lit);
  sprintf (res, "%u(%d)", unsigned_lit, signed_lit);
  signed char value = solver->values[unsigned_lit];
  if (value)
    {
      sprintf (res + strlen (res), "=%d", (int) value);
      struct variable * v = VAR (unsigned_lit);
      if (v->level != INVALID)
	sprintf (res + strlen (res), "@%u", v->level);
    }
  assert (strlen (res) + 1 < sizeof *loglitbuf);
  return res;
}

#define LOGLIT(...) loglit (solver, __VA_ARGS__)

#define LOGPREFIX(...) \
  if (!logging) \
    break; \
  lock_message_mutex (); \
  printf ("c LOG %u ", solver->level); \
  printf (__VA_ARGS__)

#define LOGSUFFIX(...) \
  fputc ('\n', stdout); \
  fflush (stdout); \
  unlock_message_mutex ()

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

#define LOGCLAUSE(CLAUSE, ...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  if ((CLAUSE)->redundant) \
    printf (" redundant glue %u", (CLAUSE)->glue); \
  else \
    printf (" irredundant"); \
  printf (" size %u clause[%zu]", (CLAUSE)->size, (size_t) (CLAUSE)->id); \
  for (all_literals_in_clause (LIT, (CLAUSE))) \
    printf (" %s", LOGLIT (LIT)); \
  LOGSUFFIX (); \
} while (0)

#else

#define LOG(...) do { } while (0)
#define LOGTMP(...) do { } while (0)
#define LOGCLAUSE(...) do { } while (0)

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

#define INIT_PROFILE(NAME) \
do { \
  struct profile * profile = &solver->profiles.NAME; \
  profile->start = -1; \
  profile->name = #NAME; \
} while (0)

static void
start_profile (struct profile *profile)
{
  double time = current_time ();
  double volatile *p = &profile->start;
  assert (*p < 0);
  *p = time;
}

static void
stop_profile (struct profile *profile)
{
  double time = current_time ();
  double volatile *p = &profile->start;
  double delta = time - *p;
  *p = -1;
  profile->time += delta;
}

#define START(NAME) \
  start_profile (&solver->profiles.NAME)

#define STOP(NAME) \
  stop_profile (&solver->profiles.NAME)

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

static struct solver *
new_solver (unsigned size)
{
  assert (size < (1u << 30));
  struct solver *solver = allocate_and_clear_block (sizeof *solver);
  solver->size = size;
  solver->values = allocate_and_clear_array (1, 2*size);
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
  return solver;
}

static void
release_watches (struct solver *solver)
{
  for (all_literals (lit))
    RELEASE (WATCHES (lit));
  for (all_watches (w, solver->watches))
    {
      struct clause *clause = w->clause;
      if (!--clause->shared)
	free (clause);
      free (w);
    }
  RELEASE (solver->watches);
}

static void
delete_solver (struct solver *solver)
{
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

  printf ("c\nc closed '%s' after writing %zu proof lines\n",
	  proof.path, proof.lines);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

static struct watch *
new_watch (struct solver *solver, struct clause *clause,
	   bool redundant, unsigned glue)
{
  assert (clause->size >= 2);
  unsigned *literals = clause->literals;
  struct watch *watch = allocate_block (sizeof *watch);
  watch->binary = (clause->size == 2);
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
  PUSH (WATCHES (literals[0]), watch);
  PUSH (WATCHES (literals[1]), watch);
  PUSH (solver->watches, watch);
  return watch;
}

static void
delete_watch (struct solver *solver, struct watch *watch)
{
  (void) solver;
  free (watch);
}

static struct watch *
new_clause (struct solver *solver,
	    size_t size, unsigned *literals, bool redundant, unsigned glue)
{
  assert (2 <= size);
  assert (size <= solver->size);
  size_t bytes = size * sizeof (unsigned);
  struct clause *clause = allocate_block (sizeof *clause + bytes);
  clause->id = ++solver->statistics.added;
  if (redundant)
    solver->statistics.redundant++;
  else
    solver->statistics.irredundant++;
  clause->redundant = redundant;
  clause->glue = glue;

  clause->shared = 1;
  clause->size = size;
  memcpy (clause->literals, literals, bytes);
  LOGCLAUSE (clause, "new");
  return new_watch (solver, clause, redundant, glue);
}

static void
delete_clause (struct solver *solver, struct clause *clause)
{
  LOGCLAUSE (clause, "delete");
  if (clause->redundant)
    {
      assert (solver->statistics.redundant > 0);
      solver->statistics.redundant--;
    }
  else
    {
      assert (solver->statistics.irredundant > 0);
      solver->statistics.irredundant--;
    }
  TRACE_DELETED (clause);
  free (clause);
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
  LOGCLAUSE (reason->clause, "assign %s with reason", LOGLIT (lit));
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

static struct watch *
propagate (struct solver *solver)
{
  assert (!solver->inconsistent);
  struct trail *trail = &solver->trail;
  struct watch *conflict = 0;
  signed char *values = solver->values;
  size_t ticks = 0;
  while (!conflict && trail->propagate != trail->end)
    {
      unsigned lit = *trail->propagate++;
      LOG ("propagating %s", LOGLIT (lit));
      solver->statistics.propagations++;
      unsigned not_lit = NOT (lit);
      struct watches *watches = &WATCHES (not_lit);
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end, **p = begin;
      ticks++;
      while (!conflict && p != end)
	{
	  struct watch *watch = *q++ = *p++;
	  unsigned other = watch->sum ^ not_lit;
	  assert (other < 2*solver->size);
	  signed char other_value = values[other];
	  ticks++;
	  if (other_value > 0)
	    continue;
	  struct clause *clause = watch->clause;
	  if (watch->binary)
	    {
	      if (other_value)
		goto CONFLICT;
	      else
		goto ASSIGN;
	    }
	  unsigned replacement = INVALID;
	  signed char replacement_value = -1;
	  unsigned *literals = clause->literals;
	  assert (watch->middle <= clause->size);
	  unsigned *middle_literals = literals + watch->middle;
	  unsigned *end_literals = literals + clause->size;
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
	      struct watches *replacement_watches = &WATCHES (replacement);
	      PUSH (*replacement_watches, watch);
	      ticks++;
	      q--;
	    }
	  else if (other_value)
	    {
	    CONFLICT:
	      assert (other_value < 0);
	      conflict = watch;
	    }
	  else
	    {
	    ASSIGN:
	      assign_with_reason (solver, other, watch);
	      ticks++;
	    }
	}
      while (p != end)
	*q++ = *p++;
      watches->end = q;
    }
  solver->statistics.ticks.search += ticks;
  if (conflict)
    {
      LOGCLAUSE (conflict->clause, "conflicting");
      solver->statistics.conflicts++;
    }
  return conflict;
}

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
      verbose ("updating target assigned to %u", assigned);
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
      verbose ("updating best assigned to %u", assigned);
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
  if (reason->binary)
    {
      unsigned other = reason->sum ^ not_lit;
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
minimize_clause (struct solver *solver)
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
  solver->statistics.learned.literals += learned;
  solver->statistics.minimized += minimized;
  solver->statistics.deduced += deduced;
  LOG ("minimized %zu literals out of %zu", minimized, deduced);
}

static void
bump_reason_side_literals (struct solver *solver)
{
  struct variable *variables = solver->variables;
  struct unsigneds *analyzed = &solver->analyzed;
  for (all_elements_on_stack (unsigned, lit, solver->clause))
    {
      const unsigned idx = IDX (lit);
      struct variable *v = variables + idx;
      if (!v->level)
	continue;
      struct watch *watch = v->reason;
      if (!watch)
	continue;
      assert (v->seen);
      struct clause *clause = watch->clause;
      const unsigned not_lit = NOT (lit);
      for (all_literals_in_clause (other, clause))
	{
	  if (other == not_lit)
	    continue;
	  unsigned other_idx = IDX (other);
	  struct variable *u = variables + other_idx;
	  if (!u->level)
	    continue;
	  if (u->seen)
	    continue;
	  u->seen = true;
	  if (!u->poison && !u->minimize)
	    PUSH (*analyzed, other_idx);
	  bump_variable_score (solver, other_idx);
	}
    }
}

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
      LOG ("conflict on root-level produces empty clause");
      solver->inconsistent = true;
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
      LOGCLAUSE (reason->clause, "analyzing");
      bump_reason (reason);
      if (reason->binary && uip != INVALID)
	{
	  assert (VAR (uip)->seen);
	  assert (VAR (uip)->level == level);
	  unsigned other = reason->sum ^ uip;
	  unsigned idx = IDX (other);
	  struct variable *v = variables + idx;
	  assert (v->level == level);
	  if (!v->seen)
	    {
	      v->seen = true;
	      PUSH (*analyzed, idx);
	      open++;
	    }
	}
      else
	{
	  for (all_literals_in_clause (lit, reason->clause))
	    {
	      unsigned idx = IDX (lit);
	      struct variable *v = variables + idx;
	      unsigned lit_level = v->level;
	      if (!lit_level)
		continue;
	      if (v->seen)
		continue;
	      v->seen = true;
	      PUSH (*analyzed, idx);
	      bump_variable_score (solver, idx);
	      if (lit_level == level)
		{
		  open++;
		  continue;
		}
	      PUSH (*clause, lit);
	      if (!used[lit_level])
		{
		  glue++;
		  used[lit_level] = true;
		  PUSH (*levels, lit_level);
		  if (lit_level > jump)
		    jump = lit_level;
		}
	    }
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
  averages->level += SLOW_ALPHA * (jump - averages->level);
  LOG ("glucose level (LBD) %u", glue);
  averages->glue.slow += SLOW_ALPHA * (glue - averages->glue.slow);
  averages->glue.fast += FAST_ALPHA * (glue - averages->glue.fast);
  unsigned assigned = SIZE (solver->trail);
  double filled = percent (assigned, solver->size);
  LOG ("assigned %u variables %.0f%% filled", assigned, filled);
  averages->trail += SLOW_ALPHA * (filled - averages->trail);
  unsigned *literals = clause->begin;
  const unsigned not_uip = NOT (uip);
  literals[0] = not_uip;
  LOGTMP ("first UIP %s", LOGLIT (uip));
  minimize_clause (solver);
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
      solver->iterating = true;
    }
  else
    {
      unsigned other = literals[1];
      if (VAR (other)->level != jump)
	{
	  unsigned *p = literals + 2, replacement;
	  while (assert (p != clause->end),
		 VAR (replacement = *p)->level != jump)
	    p++;
	  literals[1] = replacement;
	  *p = other;
	}
      struct watch *learned = new_clause (solver, size, literals, true, glue);
      assign_with_reason (solver, not_uip, learned);
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

static void
decide (struct solver *solver)
{
  assert (solver->unassigned);
  struct queue *queue = &solver->queue;
  signed char *values = solver->values;
  assert (queue->root);
  unsigned lit;
  size_t idx;
  for (;;)
    {
      struct node *root = queue->root;
      assert (root);
      idx = root - queue->nodes;
      lit = LIT (idx);
      if (!values[lit])
	break;
      pop_queue (queue, root);
    }
  assert (idx < solver->size);
  struct variable *v = solver->variables + idx;
  signed char phase = decide_phase (solver, v);
  if (phase < 0)
    lit = NOT (lit);
  solver->level++;
  assign_decision (solver, lit);
  solver->statistics.decisions++;
}

static size_t reported;

static void
report (struct solver *solver, char type)
{
  struct statistics *s = &solver->statistics;
  struct averages *a = solver->averages + solver->stable;
  lock_message_mutex ();
  if (!(reported++ % 20))
    printf ("c\nc    seconds MB level reductions restarts "
	    "conflicts redundant trail glue irredundant variables\nc\n");
  double t = wall_clock_time ();
  double m = current_resident_set_size () / (double) (1 << 20);
  printf ("c %c %6.2f %4.0f %5.0f %6zu %8zu "
	  "%12zu %9zu %3.0f%% %6.1f %9zu %9u %3.0f%%\n",
	  type, t, m, a->level, s->reductions, s->restarts,
	  s->conflicts, s->redundant, a->trail, a->glue.slow, s->irredundant,
	  solver->active, percent (solver->active, solver->size));
  fflush (stdout);
  unlock_message_mutex ();
}

static void
set_limits (struct solver *solver)
{
  if (solver->inconsistent)
    return;
  assert (!solver->stable);
  assert (!solver->statistics.conflicts);
  struct limits *limits = &solver->limits;
  limits->mode = MODE_INTERVAL;
  limits->reduce = REDUCE_INTERVAL;
  limits->restart = FOCUSED_RESTART_INTERVAL;
  limits->rephase = REPHASE_INTERVAL;
  verbose ("reduce interval of %zu conflict", limits->reduce);
  verbose ("restart interval of %zu conflict", limits->restart);
  verbose ("initial mode switching interval of %zu conflicts", limits->mode);
}

static bool
restarting (struct solver *solver)
{
  if (!solver->level)
    return false;
  struct statistics *s = &solver->statistics;
  struct limits *l = &solver->limits;
  if (!solver->stable)
    {
      struct averages *a = solver->averages;
      if (a->glue.fast <= RESTART_MARGIN * a->glue.slow)
	return false;
    }
  return l->restart < s->conflicts;
}

static void
restart (struct solver *solver)
{
  struct statistics *statistics = &solver->statistics;
  statistics->restarts++;
  verbose ("restart %zu at %zu conflicts",
	   statistics->restarts, statistics->conflicts);
  update_best_and_target_phases (solver);
  backtrack (solver, 0);
  struct limits *limits = &solver->limits;
  limits->restart = statistics->conflicts;
  if (solver->stable)
    {
      struct reluctant *reluctant = &solver->reluctant;
      size_t u = reluctant->u, v = reluctant->v;
      if ((u & -u) == v)
	u++, v = 1;
      else
	v *= 2;
      limits->restart += STABLE_RESTART_INTERVAL * v;
      reluctant->u = u, reluctant->v = v;
    }
  else
    limits->restart += FOCUSED_RESTART_INTERVAL;
  verbose ("next restart limit at %zu conflicts", limits->restart);
  if (verbosity > 0)
    report (solver, 'r');
}

static void
mark_reasons (struct solver *solver)
{
  for (all_literals_on_trail (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (watch)
	{
	  assert (!watch->reason);
	  watch->reason = true;
	}
    }
}

static void
unmark_reasons (struct solver *solver)
{
  for (all_literals_on_trail (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (watch)
	{
	  assert (watch->reason);
	  watch->reason = false;
	}
    }
}

static void
mark_satisfied_clauses_as_garbage (struct solver *solver)
{
  size_t marked = 0;
  signed char *values = solver->values;
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
	  if (VAR (lit)->level)
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
  verbose ("marked %zu satisfied clauses as garbage %.0f%%",
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
  verbose ("gathered %zu reduce candidates clauses %.0f%%",
	   SIZE (*candidates),
	   percent (SIZE (*candidates), solver->statistics.redundant));
}

static int
cmp_reduce_candidates (const void *p, const void *q)
{
  struct watch *u = *(struct watch **) p;
  struct watch *v = *(struct watch **) q;
  if (u->glue > v->glue)
    return -1;
  if (u->glue < v->glue)
    return 1;
  struct clause *c = u->clause;
  struct clause *d = v->clause;
  if (c->size > d->size)
    return -1;
  if (c->size < d->size)
    return 1;
  if (c->id < d->id)
    return -1;
  if (c->id > d->id)
    return 1;
  assert (c == d);
  return 0;
}

static void
sort_reduce_candidates (struct watches *candidates)
{
  struct watch **begin = candidates->begin;
  size_t size = SIZE (*candidates);
  if (size)
    qsort (begin, size, sizeof *begin, cmp_reduce_candidates);
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
  verbose ("reduced %zu clauses %.0f%%", reduced, percent (reduced, size));
}

static void
flush_garbage_watches_from_watch_lists (struct solver *solver)
{
  size_t flushed = 0;
  for (all_literals (lit))
    {
      struct watches *watches = &WATCHES (lit);
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end;
      for (struct watch ** p = begin; p != end; p++)
	{
	  struct watch *watch = *q++ = *p;
	  if (!watch->garbage)
	    continue;
	  if (watch->reason)
	    continue;
	  flushed++;
	  q--;
	}
      watches->end = q;
    }
  verbose ("flushed %zu garbage watches from watch lists", flushed);
}

static void
flush_garbage_watches_and_delete_unshared_clauses (struct solver *solver)
{
  struct watches *watches = &solver->watches;
  struct watch **begin = watches->begin, **q = begin;
  struct watch **end = watches->end;
  size_t flushed = 0, deleted = 0;
  for (struct watch ** p = begin; p != end; p++)
    {
      struct watch *watch = *q++ = *p;
      if (!watch->garbage)
	continue;
      if (watch->reason)
	continue;
      flushed++;
      q--;

      struct clause *clause = watch->clause;
      delete_watch (solver, watch);

      if (--clause->shared)
	continue;

      delete_clause (solver, clause);
      deleted++;
    }
  watches->end = q;
  verbose ("flushed %zu garbage watched and deleted %zu clauses %.0f%%",
	   flushed, deleted, percent (deleted, flushed));
}

static bool
reducing (struct solver *solver)
{
  return solver->limits.reduce < solver->statistics.conflicts;
}

static void
reduce (struct solver *solver)
{
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  statistics->reductions++;
  verbose ("reduction %zu at %zu conflicts",
	   statistics->reductions, statistics->conflicts);
  mark_reasons (solver);
  struct watches candidates;
  INIT (candidates);
  if (solver->last.fixed == solver->statistics.fixed)
    mark_satisfied_clauses_as_garbage (solver);
  gather_reduce_candidates (solver, &candidates);
  sort_reduce_candidates (&candidates);
  mark_reduce_candidates_as_garbage (solver, &candidates);
  RELEASE (candidates);
  flush_garbage_watches_from_watch_lists (solver);
  flush_garbage_watches_and_delete_unshared_clauses (solver);
  unmark_reasons (solver);
  limits->reduce = statistics->conflicts;
  limits->reduce += REDUCE_INTERVAL * sqrt (statistics->reductions + 1);
  verbose ("next reduce limit at %zu conflicts", limits->reduce);
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
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  limits->restart = statistics->conflicts + FOCUSED_RESTART_INTERVAL;
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
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  limits->restart = statistics->conflicts + STABLE_RESTART_INTERVAL;
  solver->reluctant.u = solver->reluctant.v = 1;
}

static bool
switching_mode (struct solver *solver)
{
  struct statistics *s = &solver->statistics;
  struct limits *l = &solver->limits;
  if (s->switched)
    return s->ticks.search > l->mode;
  else
    return s->conflicts > l->mode;
}

static size_t
square (size_t n)
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
    i->mode = s->ticks.search;
  if (solver->stable)
    switch_to_focused_mode (solver);
  else
    switch_to_stable_mode (solver);
  swap_scores (solver);
  l->mode = s->ticks.search + square (s->switched / 2 + 1) * i->mode;
  verbose ("next mode switching limit at %zu ticks", l->mode);
}

struct doubles
{
  double * begin, * end, * allocated;
};

struct counter
{
  unsigned count;
  unsigned pos;
  struct clause * clause;
};

struct walker
{
  struct solver * solver;
  struct unsigneds * occs;
  struct counter * counters;
  struct unsigneds unsatisfied;
  struct unsigneds literals;
  struct doubles scores;
  struct doubles breaks;
  double epsilon;
  unsigned maxbreak;
  size_t minimum;
};

#ifdef LOGGING

#define WOG(...) \
do { \
  struct solver * solver = walker->solver; \
  LOG (__VA_ARGS__); \
} while (0)

#define WOGCLAUSE(...) \
do { \
  struct solver * solver = walker->solver; \
  LOGCLAUSE (__VA_ARGS__); \
} while (0)

#else

#define WOG(...) do { } while (0)
#define WOGCLAUSE(...) do { } while (0)

#endif

static size_t
count_irredundant_non_garbage_clauses (struct solver * solver,
                                       struct clause ** last_ptr)
{
  size_t res = 0;
  struct clause * last = 0;
  for (all_watches (w, solver->watches))
    {
      if (w->garbage)
	continue;
      if (w->redundant)
	continue;
      struct clause * clause = w->clause;
      last = clause;
      res++;
    }
  *last_ptr = last;
  return res;
}

static void
initialize_break_table (struct walker * walker)
{
  double epsilon = 1;
  unsigned maxbreak = 0;
  for (;;)
    {
      double next = epsilon / 2.0;
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

static void
connect_counters (struct walker * walker, struct clause * last)
{
  struct solver * solver = walker->solver;
  signed char * values = solver->values;
  struct counter * p = walker->counters;
  unsigned cidx = 0;
  for (all_watches (w, solver->watches))
    {
      if (w->garbage)
	continue;
      if (w->redundant)
	continue;
      struct clause * clause = w->clause;
      unsigned count = 0;
      for (all_literals_in_clause (lit, clause))
	{
	  signed char value = values[lit];
	  if (!value)
	    continue;
	  count += (value > 0);
	  PUSH (walker->occs[lit], cidx);
	}
      p->count = count;
      p->clause = clause;
      if (!count)
	{
	  p->pos = SIZE (walker->unsatisfied);
	  PUSH (walker->unsatisfied, cidx);
	  LOGCLAUSE (clause, "initially broken");
	}
      else
	p->pos = INVALID;
      cidx++;
      p++;
      if (clause == last)
	break;
    }
}

static void
import_decisions (struct walker * walker)
{
  struct solver * solver = walker->solver;
  signed char *values = solver->values;
  unsigned pos = 0, neg = 0, ignored = 0;
  signed char *p = values;
  for (all_variables (v))
    {
      signed char phase = decide_phase (solver, v);
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
  assert (p == values + 2*solver->size);
  verbose ("imported %u positive %u negative decisions (%u ignored)",
           pos, neg, ignored);
}
 
static void
export_decisions (struct walker * walker)
{
  struct solver * solver = walker->solver;
  signed char * values = solver->values;
  memset (values, 0, 2*solver->size);
  for (all_elements_on_stack (unsigned, lit, solver->trail))
    {
      values[lit] = 1;
      values[NOT (lit)] = -1;
      VAR (lit)->level = 0;
    }
}

static void
set_walking_limits (struct walker * walker)
{
  struct solver * solver = walker->solver;
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  struct last * last = &solver->last;
  size_t ticks = statistics->ticks.search - last->walk;
  size_t effort = WALK_EFFORT * ticks;
  effort = 1000000;
  limits->walk = statistics->ticks.walk + effort;
  WOG ("limiting walking effort to %zu ticks", effort);
}

static bool
init_walker (struct solver * solver, struct walker * walker)
{
  struct clause * last = 0;
  size_t clauses = count_irredundant_non_garbage_clauses (solver, &last);
  if (clauses > UINT_MAX)
    {
      verbose ("too many clauses %zu for local search", clauses);
      return false;
    }

  verbose ("local search over %zu clauses %.0f%%", clauses,
           percent (clauses, solver->statistics.irredundant));

  walker->solver = solver;
  walker->counters =
    allocate_and_clear_array (clauses, sizeof *walker->counters);
  walker->occs =
    allocate_and_clear_array (2*solver->size, sizeof *walker->occs);
  INIT (walker->unsatisfied);
  INIT (walker->literals);
  INIT (walker->scores);
  INIT (walker->breaks);

  initialize_break_table (walker);
  import_decisions (walker);
  set_walking_limits (walker);
  connect_counters (walker, last);

  walker->minimum = SIZE (walker->unsatisfied);
  verbose ("initially %zu clauses unsatisfied", walker->minimum);

  return true;
} 

static void
release_walker (struct walker * walker)
{
  struct solver * solver = walker->solver;
  free (walker->counters);
  for (all_literals (lit))
    RELEASE (walker->occs [lit]);
  free (walker->occs);
  RELEASE (walker->unsatisfied);
  RELEASE (walker->literals);
  RELEASE (walker->scores);
  RELEASE (walker->breaks);
}

static size_t
random64 (struct solver * solver)
{
  size_t res = solver->random, next = res;
  next *= 6364136223846793005ul;
  next += 1442695040888963407ul;
  solver->random = next;
  return res;
}

static unsigned
random32 (struct solver * solver)
{
  return random64 (solver) >> 32;
}

static unsigned
random_modulo (struct solver * solver, unsigned mod)
{
  assert (mod);
  const unsigned tmp = random32 (solver);
  const double fraction = tmp / 4294967296.0;
  assert (0 <= fraction), assert (fraction < 1);
  const unsigned res = mod * fraction;
  assert (res < mod);
  return res;
}

static double
random_double (struct solver * solver)
{
  return random32 (solver) / 4294967296.0;
}

static unsigned
break_count (struct walker * walker, unsigned lit)
{
  unsigned not_lit = NOT (lit);
  assert (walker->solver->values[not_lit] > 0);
  unsigned res = 0;
  struct counter * counters = walker->counters;
  for (all_elements_on_stack (unsigned, cidx, walker->occs[not_lit]))
    if (counters[cidx].count == 1)
      res++;
  return res;
}

static double
break_score (struct walker * walker, unsigned lit)
{
  unsigned count = break_count (walker, lit);
  assert (SIZE (walker->breaks) == walker->maxbreak);
  double res;
  if (count >= walker->maxbreak)
    res = walker->epsilon;
  else
    res = walker->breaks.begin[count];
  WOG ("break count of %s is %u and score %g",
       LOGLIT (lit), count, res);
  return res;
}

static void
make_clause (struct walker * walker,
             struct counter * counter, unsigned cidx)
{
  assert (walker->counters + cidx == counter);
  unsigned pos = counter->pos;
  assert (pos < SIZE (walker->unsatisfied));
  assert (walker->unsatisfied.begin[pos] == cidx);
  unsigned other_cidx = *--walker->unsatisfied.end;
  walker->unsatisfied.begin[pos] = other_cidx;
  walker->counters[other_cidx].pos = pos;
  counter->pos = INVALID;
}

static void
break_clause (struct walker * walker,
              struct counter * counter, unsigned cidx)
{
  assert (walker->counters + cidx == counter);
  counter->pos = SIZE (walker->unsatisfied);
  PUSH (walker->unsatisfied, cidx);
}

static void
make_literal (struct walker * walker, unsigned lit)
{
  struct solver * solver = walker->solver;
  assert (walker->solver->values[lit] > 0);
  struct counter * counters = walker->counters;
  size_t ticks = 1;
  for (all_elements_on_stack (unsigned, cidx, walker->occs[lit]))
    {
      ticks++;
      struct counter * counter = counters + cidx;
      if (counter->count++)
	continue;
      LOGCLAUSE (counter->clause, "literal %s makes", LOGLIT (lit));
      make_clause (walker, counter, cidx);
      ticks++;
    }
  solver->statistics.ticks.walk += ticks;

  unsigned unsatisfied = SIZE (walker->unsatisfied);
  LOG ("making literal %s gives %u unsatisfied clauses",
       LOGLIT (lit), unsatisfied);
  if (unsatisfied >= walker->minimum)
    return;

  verbose ("new minimum %u of unsatisfied clauses", unsatisfied);
  walker->minimum = unsatisfied;
  signed char * p = solver->values;
  for (all_variables (v))
    v->saved = *p, p += 2;
}

static void
break_literal (struct walker * walker, unsigned lit)
{
  assert (walker->solver->values[lit] < 0);
  struct counter * counters = walker->counters;
  size_t ticks = 1;
  for (all_elements_on_stack (unsigned, cidx, walker->occs[lit]))
    {
      ticks++;
      struct counter * counter = counters + cidx;
      assert (counter->count);
      if (--counter->count)
	continue;
      ticks++;
      WOGCLAUSE (counter->clause, "literal %s breaks", LOGLIT (lit));
      break_clause (walker, counter, cidx);
    }
  walker->solver->statistics.ticks.walk += ticks;
}

static void
flip_literal (struct walker * walker, unsigned lit)
{
  struct solver * solver = walker->solver;
  signed char * values = solver->values;
  assert (values[lit] < 0);
  solver->statistics.flips++;
  unsigned not_lit = NOT (lit);
  values[lit] = 1, values[not_lit] = -1;
  break_literal (walker, not_lit);
  make_literal (walker, lit);
}

static void
flip_literal_in_clause (struct walker * walker, struct clause * clause)
{
  assert (EMPTY (walker->literals));
  assert (EMPTY (walker->scores));

  struct solver * solver = walker->solver;
  signed char * values = solver->values;

  LOGCLAUSE (clause, "flipping literal in");

  unsigned lit = INVALID;
  double total = 0, score = -1;
  for (all_literals_in_clause (other, clause))
    {
      if (!values[other])
	continue;
      PUSH (walker->literals, other);
      score = break_score (walker, other);
      PUSH (walker->scores, score);
      total += score;
      lit = other;
    }

  double random = random_double (solver);
  assert (0 <= random), assert (random < 1);
  double threshold = random * total;

  double sum = 0, * scores = walker->scores.begin;

  for (all_literals_in_clause (other, clause))
    {
      if (!values[other])
	continue;
      double other_score = *scores++;
      sum += other_score;
      if (threshold >= sum)
	continue;
      lit = other;
      score = other_score;
      break;
    }

  CLEAR (walker->literals);
  CLEAR (walker->scores);

  LOG ("flipping literal %s with score %g", LOGLIT (lit), score);
  flip_literal (walker, lit);
}

static void
walking_step (struct walker * walker)
{
  struct unsigneds * unsatisfied = &walker->unsatisfied;
  size_t size = SIZE (*unsatisfied);
  size_t pos = random_modulo (walker->solver, size);
  WOG ("picked clause %zu from %zu broken clauses", pos, size);
  unsigned cidx = unsatisfied->begin[pos];
  struct clause * clause = walker->counters[cidx].clause;
  flip_literal_in_clause (walker, clause);
}

static void
walking_loop (struct walker * walker)
{
  struct solver * solver = walker->solver;
  size_t * ticks = &solver->statistics.ticks.walk;
  size_t limit = solver->limits.walk;
  while (walker->minimum && *ticks <= limit)
    walking_step (walker);
}

static void
local_search (struct solver *solver)
{
  START (walk);
  solver->statistics.walked++;
  if (solver->level)
    backtrack (solver, 0);
  if (solver->last.fixed == solver->statistics.fixed)
    mark_satisfied_clauses_as_garbage (solver);
  struct walker walker;
  if (!init_walker (solver, &walker))
    goto DONE;
  walking_loop (&walker);
  release_walker (&walker);
  export_decisions (&walker);
DONE:
  solver->last.walk = solver->statistics.ticks.search;
  STOP (walk);
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
  return solver->stable &&
    solver->statistics.conflicts > solver->limits.rephase;
}

static void
rephase (struct solver *solver)
{
  if (solver->level)
    backtrack (solver, 0);
  struct statistics *statistics = &solver->statistics;
  struct limits *limits = &solver->limits;
  size_t rephased = ++statistics->rephased;
  size_t schedule = (rephased - 1) % 4;
  char type;
  if (schedule == 0)
    type = rephase_best (solver);
  else if (schedule == 1)
    type = rephase_walk (solver);
  else if (schedule == 2)
    type = rephase_inverted (solver);
  else if (schedule == 3)
    type = rephase_best (solver);
  else if (schedule == 4)
    type = rephase_walk (solver);
  else
    type = rephase_original (solver);
  verbose ("resetting number of target assigned %u", solver->target);
  solver->target = 0;
  if (type == 'B')
    {
      verbose ("resetting number of best assigned %u", solver->best);
      solver->best = 0;
    }
  limits->rephase = statistics->conflicts;
  limits->rephase += REPHASE_INTERVAL * rephased * sqrt (rephased);
  verbose ("next rephase limit at %zu conflicts", limits->rephase);
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

static int
solve (struct solver *solver)
{
  start_search (solver);
  int res = solver->inconsistent ? 20 : 0;
  while (!res)
    {
      struct watch *conflict = propagate (solver);
      if (conflict)
	{
	  if (!analyze (solver, conflict))
	    res = 20;
	}
      else if (!solver->unassigned)
	res = 10;
      else if (solver->iterating)
	iterate (solver);
      else if (reducing (solver))
	reduce (solver);
      else if (restarting (solver))
	restart (solver);
      else if (switching_mode (solver))
	switch_mode (solver);
      else if (rephasing (solver))
	rephase (solver);
      else
	decide (solver);
    }
  stop_search (solver, res);
  return res;
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
  fprintf (stderr, "gimbatul: parse error: at line %zu in '%s': ",
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

static void
parse_options (int argc, char **argv)
{
  for (int i = 1; i != argc; i++)
    {
      const char *arg = argv[i];
      if (!strcmp (arg, "-h"))
	{
	  fputs (usage, stdout);
	  exit (0);
	}
      else if (!strcmp (arg, "-l"))
#ifdef LOGGING
	{
	  logging = true;
	  verbosity = MAX_VERBOSITY;
	}
#else
	die ("invalid option '-l' (compiled without logging support)");
#endif
      else if (!strcmp (arg, "-n"))
	witness = false;
      else if (!strcmp (arg, "-v"))
	{
	  if (verbosity < MAX_VERBOSITY)
	    verbosity++;
	}
      else if (!strcmp (arg, "--version"))
	{
	  printf ("%s\n", VERSION);
	  exit (0);
	}
      else if (!strcmp (arg, "-a"))
	binary_proof_format = false;
      else if (!strcmp (arg, "-f"))
	force = true;
      else if (arg[0] == '-' && arg[1])
	die ("invalid option '%s' (try '-h')", arg);
      else if (proof.file)
	die ("too many arguments");
      else if (dimacs.file)
	{
	  if (!strcmp (arg, "-"))
	    {
	      proof.path = "<stdout>";
	      proof.file = stdout;
	      binary_proof_format = false;
	    }
	  else if (!force && looks_like_dimacs (arg))
	    die ("proof file '%s' looks like a DIMACS file (use '-f')", arg);
	  else if (!(proof.file = fopen (arg, "w")))
	    die ("can not open and write to '%s'", arg);
	  else
	    {
	      proof.path = arg;
	      proof.close = true;
	    }
	}
      else
	{
	  if (!strcmp (arg, "-"))
	    {
	      dimacs.path = "<stdin>";
	      dimacs.file = stdin;
	    }
	  else if (has_suffix (arg, ".bz2"))
	    {
	      dimacs.file = open_and_read_from_pipe (arg, "bzip2 -c -d %s");
	      dimacs.close = 2;
	    }
	  else if (has_suffix (arg, ".gz"))
	    {
	      dimacs.file = open_and_read_from_pipe (arg, "gzip -c -d %s");
	      dimacs.close = 2;
	    }
	  else if (has_suffix (arg, ".xz"))
	    {
	      dimacs.file = open_and_read_from_pipe (arg, "xz -c -d %s");
	      dimacs.close = 2;
	    }
	  else
	    {
	      dimacs.file = fopen (arg, "r");
	      dimacs.close = 1;
	    }
	  if (!dimacs.file)
	    die ("can not open and read from '%s'", arg);
	  dimacs.path = arg;
	}
    }

  if (!dimacs.file)
    {
      dimacs.path = "<stdin>";
      dimacs.file = stdin;
    }
}

static void
print_banner (void)
{
  lock_message_mutex ();
  printf ("c Gimbatul SAT Solver\n");
  printf ("c Copyright (c) 2022 Armin Biere University of Freiburg\n");
  fputs ("c\n", stdout);
  printf ("c Version %s%s\n", VERSION, GITID ? " " GITID : "");
  printf ("c %s\n", COMPILER);
  printf ("c %s\n", BUILD);
  unlock_message_mutex ();
}

#define CHECK_SIZE_OF_TYPE(TYPE,EXPECTED) \
do { \
  size_t ACTUAL = sizeof (TYPE); \
  if (ACTUAL == (EXPECTED)) \
    break; \
  fatal_error ("'sizeof (%s)' is %zu bytes in size but expected %zu", \
               # TYPE, (size_t) ACTUAL, (size_t) (EXPECTED)); \
} while (0)

static void
check_types (void)
{
  CHECK_SIZE_OF_TYPE (bool, 1);
  CHECK_SIZE_OF_TYPE (int, 4);
  CHECK_SIZE_OF_TYPE (unsigned, 4);
  if (sizeof (void *) != sizeof (size_t))
    fatal_error ("'sizeof (void*) = %zu' "
		 "different from 'sizeof (size_t) = %zu'",
		 sizeof (void *), sizeof (size_t));
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

static struct solver *
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
  while (ch == ' ' || ch == '\t')
    ch = next_char ();
  if (ch != '\n')
    goto INVALID_HEADER;
  struct solver *solver = new_solver (variables);
  signed char *marked = allocate_and_clear_block (variables);
  printf ("c\nc initialized solver of %d variables\n", variables);
  fflush (stdout);
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
	  if (!solver->inconsistent && !trivial)
	    {
	      const size_t size = SIZE (*clause);
	      assert (size <= solver->size);
	      if (!size)
		{
		  LOG ("found empty original clause");
		  solver->inconsistent = true;
		}
	      else if (size == 1)
		{
		  const unsigned unit = *clause->begin;
		  const signed char value = solver->values[unit];
		  if (value < 0)
		    {
		      LOG ("found inconsistent units");
		      solver->inconsistent = true;
		      TRACE_EMPTY ();
		    }
		  else if (!value)
		    assign_unit (solver, unit);
		}
	      else
		new_clause (solver, size, clause->begin, false, 0);
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
  message ("parsed 'p cnf %d %d' DIMACS file '%s'",
	   variables, parsed, dimacs.path);
  assert (dimacs.file);
  if (dimacs.close == 1)
    fclose (dimacs.file);
  if (dimacs.close == 2)
    pclose (dimacs.file);
  return solver;
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

static volatile bool caught_signal;
static volatile bool catching_signals;
static struct solver *solver;

#define SIGNALS \
SIGNAL(SIGABRT) \
SIGNAL(SIGBUS) \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGTERM)

// *INDENT-OFF*

// Saved previous signal handlers.

#define SIGNAL(SIG) \
static void (*saved_ ## SIG ## _handler)(int);
SIGNALS
#undef SIGNAL

// *INDENT-ON*

static void
reset_signal_handler (void)
{
  if (!catching_signals)
    return;
  catching_signals = false;
#define SIGNAL(SIG) \
  signal (SIG, saved_ ## SIG ## _handler);
  SIGNALS
#undef SIGNAL
}

static void print_profiles (struct solver *);
static void print_statistics (struct solver *);

static void
catch_signal (int sig)
{
  if (caught_signal)
    return;
  caught_signal = sig;
  const char *name = "SIGNUNKNOWN";
#define SIGNAL(SIG) \
  if (sig == SIG) name = #SIG;
  SIGNALS
#undef SIGNAL
  char buffer[80];
  sprintf (buffer, "c\nc caught signal %d (%s)\nc\n", sig, name);
  ssize_t bytes = strlen (buffer);
  if (write (1, buffer, bytes) != bytes)
    exit (0);
  reset_signal_handler ();
  print_profiles (solver);
  print_statistics (solver);
  raise (sig);
}

static void
init_signal_handler (void)
{
  assert (!catching_signals);
#define SIGNAL(SIG) \
  saved_ ## SIG ##_handler = signal (SIG, catch_signal);
  SIGNALS
#undef SIGNAL
    catching_signals = true;
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

static void
check_witness (void)
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
      lock_message_mutex ();
      fprintf (stderr, "gimbatul: error: unsatisfied clause[%zu]", clauses);
      for (unsigned *q = c; q != p; q++)
	fprintf (stderr, " %d", export_literal (*q));
      fputs (" 0\n", stderr);
      unlock_message_mutex ();
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

static void
flush_profiles (struct solver *solver)
{
  double time = current_time ();
  for (all_profiles (profile))
    if (profile->start >= 0)
      flush_profile (time, profile);

  flush_profile (time, &solver->profiles.total);
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
  lock_message_mutex ();
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
      printf ("c %10.2f seconds  %5.1f%%  %s\n",
	      next->time, percent (next->time, total), next->name);
      prev = next;
    }
  fputs ("c ---------------------------------------\n", stdout);
  printf ("c %10.2f seconds  100.0%%  total\n", total);
  fputs ("c\n", stdout);
  fflush (stdout);
  unlock_message_mutex ();
}

static void
print_statistics (struct solver *solver)
{
  lock_message_mutex ();
  double p = process_time ();
  double w = wall_clock_time ();
  double m = maximum_resident_set_size () / (double) (1 << 20);
  struct statistics *s = &solver->statistics;
  printf ("c %-19s %13zu %13.2f per second\n", "conflicts:", s->conflicts,
	  average (s->conflicts, w));
  printf ("c %-19s %13zu %13.2f %% variables\n", "fixed-variables:", s->fixed,
	  percent (s->fixed, solver->size));
  printf ("c %-19s %13zu %13.2f per learned clause\n", "learned-literals:",
	  s->learned.literals,
	  average (s->learned.literals, s->learned.clauses));
  printf ("c %-19s %13zu %13.2f %% per deduced literals\n",
	  "minimized-literals:", s->minimized, percent (s->minimized,
							s->deduced));
  printf ("c %-19s %13zu %13.2f per seccond\n", "propagations:",
	  s->propagations, average (s->propagations, w));
  printf ("c %-19s %13zu %13.2f conflict interval\n", "reductions:",
	  s->reductions, average (s->conflicts, s->reductions));
  printf ("c %-19s %13zu %13.2f conflict interval\n", "rephased:",
	  s->rephased, average (s->conflicts, s->rephased));
  printf ("c %-19s %13zu %13.2f conflict interval\n", "restarts:",
	  s->restarts, average (s->conflicts, s->restarts));
  printf ("c %-19s %13zu %13.2f conflict interval\n", "switched:",
	  s->switched, average (s->conflicts, s->switched));
  printf ("c %-19s %13zu %13.2f flips per walkinterval\n", "walked:",
	  s->walked, average (s->flips, s->walked));
  fputs ("c\n", stdout);
  printf ("c %-30s %16.2f sec\n", "process-time:", p);
  printf ("c %-30s %16.2f sec\n", "wall-clock-time:", w);
  printf ("c %-30s %16.2f MB\n", "maximum-resident-set-size:", m);
  fflush (stdout);
  unlock_message_mutex ();
}

/*------------------------------------------------------------------------*/

int
main (int argc, char **argv)
{
  start_time = current_time ();
  check_types ();
  parse_options (argc, argv);
  print_banner ();
  if (proof.file)
    {
      printf ("c\nc writing %s proof trace to '%s'\n",
	      binary_proof_format ? "binary" : "ASCII", proof.path);
      fflush (stdout);
    }
  solver = parse_dimacs_file ();
  init_signal_handler ();
  set_limits (solver);
  local_search (solver);
  int res = solve (solver);
  reset_signal_handler ();
  close_proof ();
  if (res == 20)
    {
      printf ("c\ns UNSATISFIABLE\n");
      fflush (stdout);
    }
  else if (res == 10)
    {
#ifndef NDEBUG
      check_witness ();
#endif
      printf ("c\ns SATISFIABLE\n");
      if (witness)
	print_witness (solver);
      fflush (stdout);
    }
  print_profiles (solver);
  print_statistics (solver);
  delete_solver (solver);
#ifndef NDEBUG
  RELEASE (original);
#endif
  printf ("c\nc exit %d\n", res);
  fflush (stdout);
  return res;
}
