// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimbatul [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-h    print this command line option summary\n"
#ifdef LOGGING
"-l    enable very verbose internal logging\n"
#endif
"-n    do not print satisfying assignments\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing).\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

#define INVALID UINT_MAX

#define IDX(LIT) ((LIT) >> 1)
#define LIT(IDX) ((IDX) << 1)
#define NOT(LIT) ((LIT) ^ 1u)
#define SGN(LIT) ((LIT) & 1)

#define VAR(LIT) (solver->variables + IDX (LIT))
#define WATCHES(LIT) (VAR(LIT)->watches[SGN (LIT)])

/*------------------------------------------------------------------------*/

#define SIZE(STACK) ((STACK).end - (STACK).begin)

#define CAPACITY(STACK) ((STACK).allocated - (STACK).begin)

#define EMPTY(STACK) ((STACK).end == (STACK).begin)

#define FULL(STACK) ((STACK).end == (STACK).allocated)

#define RELEASE(STACK) \
do { \
  free ((STACK).begin); \
  memset (&(STACK), 0, sizeof (STACK)); \
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

#define all_clauses(CLAUSE) \
  all_elements_on_stack (reference, CLAUSE, solver->clauses)

#define all_variables(VAR) \
  struct variable * VAR = solver->variables, \
                  * END_ ## VAR = VAR + solver->size; \
  (VAR != END_ ## VAR); \
  ++ VAR

#define all_nodes(NODE) \
  struct node * NODE = solver->queue.nodes, \
              * END_ ## NODE = (NODE) + solver->size; \
  NODE != END_ ## NODE; \
  ++NODE

#define all_indices(IDX) \
  unsigned IDX = 0, END_ ## IDX = solver->size; \
  IDX != END_ ## IDX; \
  ++IDX

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
  bool close;
  size_t lines;
};

struct unsigneds
{
  unsigned *begin, *end, *allocated;
};

struct trail
{
  unsigned *begin, *end, *propagate;
};

struct clause
{
#ifdef LOGGING
  size_t id;
#endif
  bool active;
  bool garbage;
  bool redundant;
  bool used;
  unsigned glue;
  unsigned size;
  unsigned literals[];
};

typedef struct clause *reference;

struct clauses
{
  struct clause **begin, **end, **allocated;
};

struct watch
{
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
  signed char phase;
  bool seen:1;
  struct clause * reason;
  struct watches watches[2];
};

struct node
{
  double score;
  struct node *child, *prev, *next;
};

struct queue
{
  double increment;
  struct node *nodes;
  struct node *root;
};

struct limits
{
  size_t mode;
  size_t reduce;
  size_t restart;
};

struct statistics
{
  size_t conflicts;
  size_t propagations;
  size_t reductions;
  size_t restarts;
#ifdef LOGGING
  size_t clauses;
#endif
};

struct solver
{
  bool inconsistent;
  unsigned size;
  unsigned level;
  unsigned unassigned;
  struct clauses clauses;
  struct variable *variables;
  signed char *values;
  bool * used;
  struct unsigneds levels;
  struct queue queue;
  struct unsigneds clause;
  struct unsigneds analyzed;
  struct trail trail;
  struct limits limits;
  struct statistics statistics;
};

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
wall_clock_time (void)
{
  struct timeval tv;
  if (gettimeofday (&tv, 0))
    return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

static size_t
maximum_resident_set_size (void)
{
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  return ((size_t) u.ru_maxrss) << 10;
}

#if 0

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

#endif

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

/*------------------------------------------------------------------------*/

#ifdef LOGGING

static bool logging;
static char loglitbuf[4][32];
static unsigned loglitpos;

#define loglitsize (sizeof loglitbuf / sizeof *loglitbuf)

static const char *
loglit (struct solver * solver, unsigned unsigned_lit)
{
  char * res = loglitbuf[loglitpos++];
  if (loglitpos == loglitsize)
    loglitpos = 0;
  int signed_lit = unsigned_lit/2 + 1;
  if (SGN (unsigned_lit))
    signed_lit *= -1;
  sprintf (res, "%u(%d)", unsigned_lit, signed_lit);
  signed char value = solver->values[unsigned_lit];
  if (value)
    sprintf (res + strlen (res),
             "=%d@%u", (int) value, VAR (unsigned_lit)->level);
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

#define LOGCLAUSE(CLAUSE, ...) \
do { \
  LOGPREFIX (__VA_ARGS__); \
  if ((CLAUSE)->redundant) \
    printf (" redundant glue %u", (CLAUSE)->glue); \
  else \
    printf (" irredundant"); \
  printf (" size %u clause[%zu]", (CLAUSE)->size, (CLAUSE)->id); \
  for (all_literals_in_clause (LIT, (CLAUSE))) \
    printf (" %s", LOGLIT (LIT)); \
  LOGSUFFIX (); \
} while (0)

#else

#define LOG(...) do { } while (0)
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
bump_score (struct solver *solver, unsigned idx)
{
  struct queue * queue = &solver->queue;
  struct node * node = queue->nodes + idx;
  double old_score = node->score;
  double new_score = old_score + queue->increment;
  update_queue (queue, node, new_score);
}

/*------------------------------------------------------------------------*/

static struct solver *
new_solver (unsigned size)
{
  assert (size < (1u << 30));
  struct solver *solver = allocate_and_clear_block (sizeof *solver);
  solver->size = size;
  solver->values = allocate_and_clear_array (2, size);
  solver->used = allocate_and_clear_block (size);
  solver->variables =
    allocate_and_clear_array (size, sizeof *solver->variables);
  struct trail * trail = &solver->trail;
  trail->begin = allocate_array (size, sizeof *trail->begin);
  trail->end = trail->propagate = trail->begin;
  struct queue *queue = &solver->queue;
  queue->nodes = allocate_and_clear_array (size, sizeof *queue->nodes);
  queue->increment = 1;
  for (all_nodes (node))
    push_queue (queue, node);
  solver->unassigned = size;
  return solver;
}

static void
release_clauses (struct solver *solver)
{
  for (all_clauses (c))
    free (c);
  RELEASE (solver->clauses);
}

static void
release_watches (struct solver *solver)
{
  unsigned lit = 0;
  for (all_variables (v))
    {
      for (unsigned i = 0; i != 2; i++)
	{
	  struct watches *watches = v->watches + i;
	  assert (watches == &WATCHES (lit));
	  for (all_watches (w, *watches))
	    {
	      unsigned other = w->sum ^ lit;
	      if (other < lit)
		free (w);
	    }
	  RELEASE (*watches);
	  lit++;
	}
    }
  assert (lit == 2 * solver->size);
}

static void
delete_solver (struct solver *solver)
{
  RELEASE (solver->clause);
  RELEASE (solver->analyzed);
  RELEASE (solver->trail);
  RELEASE (solver->levels);
  release_watches (solver);
  release_clauses (solver);
  free (solver->queue.nodes);
  free (solver->variables);
  free (solver->values);
  free (solver->used);
  free (solver);
}

/*------------------------------------------------------------------------*/

static struct clause *
new_clause (struct solver *solver,
	    size_t size, unsigned *literals, bool redundant, unsigned glue)
{
  assert (2 <= size);
  assert (size <= solver->size);
  size_t bytes = size * sizeof (unsigned);
  struct clause *clause = allocate_block (sizeof *clause + bytes);
#ifdef LOGGING
  clause->id = ++solver->statistics.clauses;
#endif
  clause->active = false;
  clause->garbage = false;
  clause->redundant = redundant;
  clause->used = false;
  clause->glue = glue;
  clause->size = size;
  memcpy (clause->literals, literals, bytes);
  PUSH (solver->clauses, clause);
  LOGCLAUSE (clause, "new");
  struct watch * watch = allocate_block (sizeof *watch);
  watch->clause = clause;
  watch->sum = literals[0] ^ literals[1];
  PUSH (WATCHES (literals[0]), watch);
  PUSH (WATCHES (literals[1]), watch);
  return clause;
}

/*------------------------------------------------------------------------*/

static void
assign (struct solver * solver, unsigned lit, struct clause * reason)
{
  const unsigned not_lit = NOT (lit);
  assert (!solver->values[lit]);
  assert (!solver->values[not_lit]);
  assert (solver->unassigned);
  solver->unassigned--;
  solver->values[lit] = 1;
  solver->values[not_lit] = -1;
  *solver->trail.end++ = lit;
  struct variable * v = VAR (lit);
  v->phase = SGN (lit) ? -1 : 1;
  unsigned level = solver->level;
  v->level = level;
  v->reason = level ? reason : 0;
}

static void
assign_with_reason (struct solver * solver,
                    unsigned lit, struct clause * reason)
{
  assert (reason);
  assign (solver, lit, reason);
  LOGCLAUSE (reason, "assign %s with reason", LOGLIT (lit));
}

static void
assign_unit (struct solver *solver, unsigned unit)
{
  assert (!solver->level);
  assign (solver, unit, 0);
  LOG ("assign %s unit", LOGLIT (unit));
}

static void
assign_decision (struct solver * solver, unsigned decision)
{
  assert (solver->level);
  assign (solver, decision, 0);
  LOG ("assign %s decision score %g",
       LOGLIT (decision), solver->queue.nodes[IDX (decision)].score);
}

static struct clause *
propagate (struct solver * solver)
{
  assert (!solver->inconsistent);
  struct trail * trail = &solver->trail;
  struct clause * conflict = 0;
  signed char * values = solver->values;
  while (!conflict && trail->propagate != trail->end)
    {
      unsigned lit = *trail->propagate++;
      LOG ("propagating %s", LOGLIT (lit));
      solver->statistics.propagations++;
      unsigned not_lit = NOT (lit);
      struct watches * watches = &WATCHES (not_lit);
      struct watch ** begin = watches->begin, ** q = begin;
      struct watch ** end = watches->end, ** p = begin;
      while (!conflict && p != end)
	{
	  struct watch * watch = *q++ = *p++;
	  unsigned other = watch->sum ^ not_lit;
	  signed char other_value = values[other];
	  if (other_value > 0)
	    continue;
	  unsigned replacement = INVALID;
	  signed char replacement_value = -1;
	  struct clause * clause = watch->clause;
	  unsigned * r = clause->literals;
	  unsigned * end_literals = r + clause->size;
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
	  if (replacement_value >= 0)
	    {
	      watch->sum = other ^ replacement;
	      struct watches * replacement_watches = &WATCHES (replacement);
	      PUSH (*replacement_watches, watch);
	      q--;
	    }
	  else if (other_value)
	    {
	      assert (other_value < 0);
	      conflict = clause;
	    }
	  else
	    assign_with_reason (solver, other, clause);
	}
      while (p != end)
	*q++ = *p++;
      watches->end = q;
    }
  if (conflict)
    {
      LOGCLAUSE (conflict, "conflicting");
      solver->statistics.conflicts++;
    }
  return conflict;
}

static void
backtrack (struct solver * solver, unsigned level)
{
  assert (solver->level > level);
  struct trail * trail = &solver->trail;
  struct variable * variables = solver->variables;
  signed char * values = solver->values;
  struct queue * queue = &solver->queue;
  struct node * nodes = queue->nodes;
  unsigned * t = trail->end;
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
      struct node * node = nodes + idx;
      if (!queue_contains (queue, node))
	push_queue (queue, node);
      t--;
    }
  trail->end = trail->propagate = t;
  solver->level = level;
}

static bool
analyze (struct solver * solver, struct clause * reason)
{
  if (!solver->level)
    return false;
  struct unsigneds * clause = &solver->clause;
  struct unsigneds * analyzed = &solver->analyzed;
  struct unsigneds * levels = &solver->levels;
  assert (EMPTY (*clause));
  assert (EMPTY (*analyzed));
  assert (EMPTY (*levels));
  struct variable * variables = solver->variables;
  struct trail * trail = &solver->trail;
  bool * used = solver->used;
  unsigned * t = trail->end;
  PUSH (*clause, INVALID);
  const unsigned level = solver->level;
  unsigned uip, jump = 0, glue = 0, open = 0;
  for (;;)
    {
      LOGCLAUSE (reason, "analyzing");
      for (all_literals_in_clause (lit, reason))
	{
	  unsigned idx = IDX (lit);
	  struct variable * v = variables + idx;
	  unsigned lit_level = v->level;
	  if (!lit_level)
	    continue;
	  if (v->seen)
	    continue;
	  v->seen = true;
	  PUSH (*analyzed, idx);
	  bump_score (solver, idx);
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
	      PUSH (*levels, level);
	      if (lit_level > jump)
		jump = lit_level;
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
      reason = variables[ IDX (uip) ].reason;
      assert (reason);
    }
  LOG ("back jump level %u", jump);
  LOG ("glucose level (LBD) %u", glue);
  LOG ("first UIP %s", LOGLIT (uip));
  backtrack (solver, jump);
  const unsigned not_uip = NOT (uip);
  unsigned * literals = clause->begin;
  literals[0] = not_uip;
  unsigned size = SIZE (*clause);
  assert (size);
  if (size == 1)
    assign_unit (solver, not_uip);
  else
    {
      struct clause * learned = new_clause (solver, size, literals, 1, glue);
      assign_with_reason (solver, not_uip, learned);
    }
  CLEAR (*clause);
  for (all_elements_on_stack (unsigned, idx, *analyzed))
    VAR (idx)->seen = false;
  CLEAR (*analyzed);
  for (all_elements_on_stack (unsigned, used_level, *levels))
    used[used_level] = false;
  CLEAR (*levels);
  return true;
}

static void
decide (struct solver * solver)
{
  assert (solver->unassigned);
  struct queue * queue = &solver->queue;
  signed char * values = solver->values;
  assert (queue->root);
  unsigned lit;
  size_t idx;
  for (;;)
    {
      struct node * root = queue->root;
      assert (root);
      idx = root - queue->nodes;
      lit = LIT (idx);
      if (!values[lit])
	break;
      pop_queue (queue, root);
    }
  assert (idx < solver->size);
  struct variable * v = solver->variables + idx;
  if (v->phase < 0)
    lit = NOT (lit);
  solver->level++;
  assign_decision (solver, lit);
}

static int
solve (struct solver *solver)
{
  int res = solver->inconsistent ? 20 : 0;
  while (!res)
    {
      struct clause * conflict = propagate (solver);
      if (conflict)
	{
	  if (!analyze (solver, conflict))
	    res = 20;
	}
      else if (!solver->unassigned)
	res = 10;
      else
	decide (solver);
    }
  return res;
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

static bool witness = true, binary = true;

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
	logging = true;
#else
	die ("invalid option '-l' (compiled without logging support)");
#endif
      else if (!strcmp (arg, "-n"))
	witness = false;
      else if (!strcmp (arg, "-a"))
	binary = false;
      else if (arg[0] == '-' && arg[1])
	die ("invalid option '%s' (try '-h')", arg);
      else if (dimacs.file)
	die ("too many arguments");
      else
	{
	  if (!strcmp (arg, "-"))
	    {
	      dimacs.path = "<stdin>";
	      dimacs.file = stdin;
	    }
	  else if (!(dimacs.file = fopen (arg, "r")))
	    die ("can not open and read from '%s'", arg);
	  else
	    {
	      dimacs.path = arg;
	      dimacs.close = true;
	    }
	}
    }

  if (!dimacs.file)
    {
      dimacs.path = "<stdin>";
      dimacs.file = stdin;
    }
}

#include "config.h"

static void
print_banner (void)
{
  lock_message_mutex ();
  printf ("c Gimbatul SAT Solver\n");
  printf ("c Copyright (c) 2022 Armin Biere University of Freiburg\n");
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
		 sizeof (void*), sizeof (size_t));
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
  struct solver * solver = new_solver (variables);
  signed char *marked = allocate_and_clear_block (variables);
  message ("initialized solver of %d variables", variables);
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
	  if (mark < 0)
	    trivial = true;
	  else if (!mark)
	    {
	      unsigned unsigned_lit = 2 * idx + (sign < 0);
	      PUSH (*clause, unsigned_lit);
	      marked[idx] = sign;
	    }
	}
      else
	{
	  parsed++;
	  if (!trivial)
	    {
	      const size_t size = SIZE (*clause);
	      assert (size <= solver->size);
	      if (!size)
		solver->inconsistent = true;
	      else if (size == 1)
		{
		  const unsigned unit = *clause->begin;
		  const signed char value = solver->values[unit];
		  if (value < 0)
		    solver->inconsistent = true;
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
  if (dimacs.close)
    fclose (dimacs.file);
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
print_unsigned_literal (signed char * values, unsigned unsigned_lit)
{
  assert (unsigned_lit < (unsigned) INT_MAX);
  int signed_lit = IDX (unsigned_lit) + 1;
  signed_lit *= values[unsigned_lit];
  print_signed_literal (signed_lit);
}

static void
print_witness (struct solver * solver)
{
  signed char * values = solver->values;
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
  sprintf (buffer,
	   "c\nc caught signal %d (%s)\nc\n", sig, name);
  ssize_t bytes = strlen (buffer);
  if (write (1, buffer, bytes) != bytes)
    exit (0);
  reset_signal_handler ();
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

static double start_time;

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

static void
print_statistics (void)
{
  double p = process_time ();
  double w = wall_clock_time () - start_time;
  double m = maximum_resident_set_size () / (double) (1<<20);
  struct statistics * s = &solver->statistics;
  lock_message_mutex ();
  printf ("c %-14s %19zu %12.2f per sec\n", "conflicts:", s->conflicts,
           average (s->conflicts, w));
  printf ("c %-14s %19zu %12.2f per sec\n", "propagations:", s->propagations,
           average (s->propagations, w));
  printf ("c %-14s %19zu %12.2f conflict interval\n", "reductions:",
           s->reductions, average (s->reductions, s->conflicts));
  printf ("c %-14s %19zu %12.2f conflict interval\n", "restarts:",
           s->restarts, average (s->restarts, s->conflicts));
  printf ("c %-30s %16.2f sec\n", "process-time:", p);
  printf ("c %-30s %16.2f sec\n", "wall-clock-time:", w);
  printf ("c %-30s %16.2f MB\n", "maximum-resident-set-size:", m);
  fflush (stdout);
  unlock_message_mutex ();
}

/*------------------------------------------------------------------------*/

int
main (int argc, char ** argv)
{
  start_time = wall_clock_time ();
  parse_options (argc, argv);
  print_banner ();
  check_types ();
  solver = parse_dimacs_file ();
  init_signal_handler ();
  int res = solve (solver);
  if (res == 20)
    {
      printf ("s UNSATISFIABLE\n");
      fflush (stdout);
    }
  else if (res == 10)
    {
      printf ("s SATISFIABLE\n");
      if (witness)
	print_witness (solver);
      fflush (stdout);
    }
  reset_signal_handler ();
  print_statistics ();
  delete_solver (solver);
  message ("exit %d", res);
  return res;
}
