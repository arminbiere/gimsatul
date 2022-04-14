// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimbatul [ <option> ... ] [ <dimacs> ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-h    print this command line option summary\n"
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
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

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
  (STACK).begin = reallocate ((STACK).begin, NEW_BYTES); \
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

#define ALL(TYPE,ELEM,STACK) \
  TYPE * P_ ## ELEM = (STACK).begin, * END_ ## ELEM = (STACK).end, ELEM; \
  (P_ ## ELEM != END_ ## ELEM) && ((ELEM) = *P_ ## ELEM, true); \
  ++P_ ## ELEM

#define all_clauses(CLAUSE) \
  ALL (reference, CLAUSE, solver->clauses)

#define all_variables(VAR) \
  struct variable * VAR = solver->variables + 1, \
                  * END_ ## VAR = VAR + solver->size; \
  (VAR != END_ ## VAR); ++ VAR

/*------------------------------------------------------------------------*/

struct file
{
  const char * path;
  FILE * file;
  bool close;
  size_t lines;
};

struct literals
{
  int * begin, * end, * allocated;
};

struct trail
{
  int * begin, * end, * propagate;
};

struct clause
{
  bool active;
  bool garbage;
  bool redundant;
  bool used;
  int glue;
  int size;
  int literals[];
};

typedef struct clause * reference;

struct clauses
{
  struct clause ** begin, ** end, ** allocated;
};

struct watch
{
  int blocking;
  struct clause * clause;
};

struct watches
{
  struct watch * begin, * end, * allocated;
};

struct reason
{
  int literal;
  struct clause * clause;
};

struct variable;


struct variable
{
  int level;
  signed char phase;
  signed char value;
  signed char mark;
  bool seen;
  bool poison;
  bool minimize;
  struct reason reason;
  struct watches watches[2];
  struct variable * child, * prev, * next;
  double score;
};

struct limits
{
  size_t mode;
  size_t reduce;
  size_t restart;
};

struct intervals
{
  size_t mode;
};

struct statistics
{
  size_t conflicts;
  size_t switches;
  size_t reductions;
  size_t restarts;
};

struct solver
{
  bool stable;
  int size;
  int unassigned;
  int level;
  signed char * values;
  double increment;
  struct variable * root;
  struct trail trail;
  struct variable * variables;
  struct literals clause;
  struct literals marked;
  struct clauses clauses;
  struct limits limits;
  struct intervals intervals;
  struct statistics statistics;
};

/*------------------------------------------------------------------------*/

static struct file dimacs;

static double start_time;

static volatile bool caught_signal;
static volatile bool catching_signals;

static struct solver * solver;

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

static void die (const char*, ...)  __attribute__((format (printf, 1, 2)));

static void
die (const char * fmt, ...)
{
  fputs ("gimbatul: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void fatal_error (const char*, ...)  __attribute__((format (printf, 1, 2)));

static void
fatal_error (const char * fmt, ...)
{
  fputs ("gimbatul: fatal error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  abort ();
}

static void parse_error (const char*, ...)  __attribute__((format (printf, 1, 2)));

static void
parse_error (const char * fmt, ...)
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

static void message (const char*, ...)  __attribute__((format (printf, 1, 2)));

static void
message (const char * fmt, ...)
{
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

static bool witness = true, binary = true;

static void
parse_options (int argc, char ** argv)
{
  for (int i = 1; i != argc; i++)
    {
      const char * arg = argv[i];
      if (!strcmp (arg, "-h"))
	{
	  fputs (usage, stdout);
	  exit (0);
	}
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

static void
print_banner (void)
{
  message ("Gimbatul SAT Solver");
  message ("Copyright (c) 2022 Armin Biere University of Freiburg");
}

/*------------------------------------------------------------------------*/

static void *
allocate (size_t bytes)
{
  void * res = malloc (bytes);
  if (bytes && !res)
    fatal_error ("out-of-memory allocating %zu bytes", bytes);
  return res;
}

static void *
callocate (size_t num, size_t bytes)
{
  void * res = calloc (num, bytes);
  if (num && bytes && !res)
    fatal_error ("out-of-memory allocating %zu*%zu bytes", num, bytes);
  return res;
}

static void *
reallocate (void * ptr, size_t bytes)
{
  void * res = realloc (ptr, bytes);
  if (bytes && !res)
    fatal_error ("out-of-memory reallocating %zu bytes", bytes);
  return res;
}

/*------------------------------------------------------------------------*/

static bool
contains (struct solver * solver, struct variable * node)
{
  return solver->root == node || node->prev;
}

static struct variable *
merge (struct variable * a, struct variable * b)
{
  if (!a)
    return b;
  if (!b)
    return a;
  assert (a != b);
  struct variable * parent, *child;
  if (b->score > a->score)
    parent = b, child = a;
  else
    parent = a, child = b;
  struct variable * parent_child = parent->child;
  child->next = parent_child;
  if (parent_child)
    parent_child->prev = child;
  child->prev = parent;
  parent->child = child;
  parent->prev = parent->next = 0;

  return parent;
}

static void
push (struct solver * solver, struct variable * node)
{
  assert (!contains (solver, node));
  node->child = 0;
  solver->root = merge (solver->root, node);
  assert (contains (solver, node));
}

#if 0

static struct variable *
collapse (struct variable * node)
{
  if (!node)
    return 0;

  struct variable * next = node, * tail = 0;

  do
    {
      struct variable * a = next;
      assert (a);
      struct variable * b = a->next;
      if (b)
        {
          next = b->next;
          struct variable * tmp = merge (a, b);
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

  struct variable * res = 0;
  while (tail)
    {
      struct variable * prev = tail->prev;
      res = merge (res, tail);
      tail = prev;
    }

  return res;
}

static void
dequeue (struct variable * node)
{
  assert (node);
  struct variable * prev = node->prev;
  struct variable * next = node->next;
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
pop (struct solver * solver, struct variable * node)
{
  struct variable * root = solver->root;
  struct variable * child = node->child;
  if (root == node)
    solver->root = collapse (child);
  else
    {
      dequeue (node);
      struct variable * collapsed = collapse (child);
      solver->root = merge (root, collapsed);
    }
  assert (!contains (solver, node));
}

static void
update (struct solver * solver, struct variable * node, double new_score)
{
  double old_score = node->score;
  assert (old_score <= new_score);
  if (old_score == new_score)
    return;
  node->score = new_score;
  struct variable * root = solver->root;
  if (root == node)
    return;
  if (!node->prev)
    return;
  dequeue (node);
  solver->root = merge (root, node);
}

#endif

/*------------------------------------------------------------------------*/

static struct solver *
new_solver (int size)
{
  struct solver * solver = callocate (1, sizeof *solver);
  solver->size = size;
  solver->values = callocate (2u * size + 1, 1);
  solver->values += size;
  solver->variables = callocate (size + 1u, sizeof *solver->variables);
  solver->trail.begin = solver->trail.end = solver->trail.propagate =
    allocate (size * sizeof *solver->trail.begin);
  for (all_variables (v))
    push (solver, v);
  return solver;
}

static void
delete_solver (struct solver * solver)
{
  for (all_clauses (c))
    free (c);
  RELEASE (solver->clauses);
  RELEASE (solver->clause);
  RELEASE (solver->marked);
  RELEASE (solver->trail);
  solver->values -= solver->size;
  free (solver->values);
  for (all_variables (v))
    for (unsigned i = 0; i != 2; i++)
      RELEASE (v->watches[i]);
  free (solver->variables);
  free (solver);
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
parse_int (int * res_ptr, int prev, int * next)
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

static void
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
      ch != ' ' ||
      !parse_int (&expected, EOF, &ch) ||
      expected < 0)
INVALID_HEADER:
    parse_error ("invalid 'p cnf ...' header line");
  while (ch == ' ' || ch == '\t')
    ch = next_char ();
  if (ch != '\n')
    goto INVALID_HEADER;
  solver = new_solver (variables);
  message ("initialized solver of %d variables", variables);
  int lit = 0, parsed = 0;
  for (;;)
    {
      ch = next_char ();
      if (ch == EOF)
	{
	  if (lit)
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
      if (!parse_int (&lit, ch, &ch))
	parse_error ("failed to parse literal");
      if (lit == INT_MIN ||abs (lit) > variables)
	parse_error ("invalid literal %d", lit);
      if (parsed == expected)
	parse_error ("too many clauses");
      if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n')
	parse_error ("invalid character after '%d'", lit);
      if (lit)
	{
	  PUSH (solver->clause, lit);
	}
      else
	{
	  parsed++;
	  CLEAR (solver->clause);
	}
      if (ch == 'c')
	goto SKIP_BODY_COMMENT;
    }
  message ("parsed 'p cnf %d %d' DIMACS file '%s'",
           variables, expected, dimacs.path);
  assert (dimacs.file);
  if (dimacs.close)
    fclose (dimacs.file);
}

/*------------------------------------------------------------------------*/

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
  message ("%-14s %19zu %12.2f per sec", "conflicts:", s->conflicts,
           average (s->conflicts, w));
  message ("%-14s %19zu %12.2f conflict interval", "reductions:",
           s->reductions, average (s->reductions, s->conflicts));
  message ("%-14s %19zu %12.2f conflict interval", "restarts:",
           s->restarts, average (s->restarts, s->conflicts));
  message ("%-30s %16.2f sec", "process-time:", p);
  message ("%-30s %16.2f sec", "wall-clock-time:", w);
  message ("%-30s %16.2f MB", "maximum-resident-set-size:", m);
}

/*------------------------------------------------------------------------*/

int
main (int argc, char ** argv)
{
  start_time = wall_clock_time ();
  parse_options (argc, argv);
  print_banner ();
  parse_dimacs_file ();
  init_signal_handler ();
  int res = 0;
  reset_signal_handler ();
  print_statistics ();
  delete_solver (solver);
  message ("exit %d", res);
  return res;
}
