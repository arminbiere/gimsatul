// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimsatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -a|--ascii               use ASCII format for proof output\n"
"  -f|--force               force reading and writing\n"
"  -h|--help                print this command line option summary\n"
#ifdef LOGGING   
"  -l|--log[ging]           enable very verbose internal logging\n"
#endif                   
"  -n|--no-witness          do not print satisfying assignments\n"
"  -O|-O<level>             increase simplification ticks and round limits\n"
"  -q|--quiet               disable all additional messages\n"
"  -v|--verbose             increase verbosity\n"
"  --version                print version\n"
"\n"
"  --conflicts=<conflicts>  limit conflicts (0,1,... - default unlimited)\n"
"  --threads=<number>       set number of threads (1,...,%zu - default 1)\n"
"  --time=<seconds>         limit time (1,2,3,... - default unlimited)\n"
"\n"
"  --no-simplify            disable preprocessing\n"
"  --no-walk                disable local search\n"
"  --walk-initially         initial local search\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof output file in 'DRAT' format (no proof if missing).\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include "allocate.h"
#include "assign.h"
#include "backtrack.h"
#include "clause.h"
#include "clone.h"
#include "config.h"
#include "export.h"
#include "logging.h"
#include "macros.h"
#include "message.h"
#include "options.h"
#include "report.h"
#include "ring.h"
#include "random.h"
#include "ruler.h"
#include "simplify.h"
#include "search.h"
#include "stack.h"
#include "solve.h"
#include "tagging.h"
#include "trace.h"
#include "utilities.h"
#include "walk.h"

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
#include <stdint.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

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

static bool
is_positive_number_string (const char *arg)
{
  const char * p = arg;
  int ch;
  if (!(ch = *p++))
    return false;
  if (!isdigit (ch))
    return false;
  while ((ch = *p++))
    if (!isdigit (ch))
      return false;
  return true;
}

static const char *
parse_long_option (const char *arg, const char *match)
{
  if (arg[0] != '-')
    return 0;
  if (arg[1] != '-')
    return 0;
  const char *p = arg + 2;
  for (const char *q = match; *q; q++, p++)
    if (*q != *p)
      return 0;
  if (*p++ != '=')
    return 0;
  return is_positive_number_string (p) ? p : 0;
}

static bool force = false;

static void
parse_options (int argc, char **argv, struct options *opts)
{
  memset (opts, 0, sizeof *opts);
  opts->conflicts = -1;
  const char *quiet_opt = 0;
  const char *verbose_opt = 0;
  for (int i = 1; i != argc; i++)
    {
      const char *opt = argv[i], *arg;
      if (!strcmp (opt, "-a") || !strcmp (opt, "--ascii"))
	binary_proof_format = false;
      else if (!strcmp (opt, "-f") || !strcmp (opt, "--force"))
	force = true;
      else if (!strcmp (opt, "-h") || !strcmp (opt, "--help"))
	{
	  printf (usage, (size_t) MAX_THREADS);
	  exit (0);
	}
      else if (!strcmp (opt, "-l") ||
	       !strcmp (opt, "--log") || !strcmp (opt, "logging"))
#ifdef LOGGING
	verbosity = INT_MAX;
#else
	die ("invalid option '%s' (compiled without logging support)", opt);
#endif
      else if (!strcmp (opt, "-n") || !strcmp (opt, "--no-witness"))
	witness = false;
      else if (!strcmp (opt, "-O"))
	opts->optimize = 1;
      else if (opt[0] == '-' && opt[1] == 'O')
	{
	  arg = opt + 2;
	  if (!is_positive_number_string (arg) ||
	      sscanf (arg, "%u", &opts->optimize) != 1)
	    die ("invalid '-O' option '%s'", opt);

	}
      else if (!strcmp (opt, "-q") || !strcmp (opt, "--quiet"))
	{
	  if (quiet_opt)
	    die ("two quiet options '%s' and '%s'", quiet_opt, opt);
	  if (verbose_opt)
	    die ("quiet option '%s' follows verbose '%s'", opt, verbose_opt);
	  quiet_opt = opt;
	  verbosity = -1;
	}
      else if (!strcmp (opt, "-v") || !strcmp (opt, "--verbose"))
	{
	  if (quiet_opt)
	    die ("verbose option '%s' follows quiet '%s'", opt, quiet_opt);
	  verbose_opt = opt;
	  if (verbosity < INT_MAX)
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
	    die ("multiple '--conflicts=%lld' and '%s'", opts->conflicts,
		 opt);
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
	    die ("invalid argument in '%s' (maximum %u)", opt, MAX_THREADS);
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
      else if (!strcmp (opt, "--no-simplify"))
	opts->no_simplify = true;
      else if (!strcmp (opt, "--no-walk"))
	{
	  if (opts->walk_initially)
	    die ("can not combine '--walk-initially' and '--no-walk'");
	  opts->no_walk = true;
	}
      else if (!strcmp (opt, "--walk-initially"))
	{
	  if (opts->no_walk)
	    die ("can not combine '--no-walk' and '--walk-initially'");
	  opts->walk_initially = true;
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
print_banner (void)
{
  if (verbosity < 0)
    return;
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

static void
parse_dimacs_header (int * variables_ptr, int * clauses_ptr)
{
  if (verbosity >= 0)
    {
      printf ("c\nc parsing DIMACS file '%s'\n", dimacs.path);
      fflush (stdout);
    }
  int ch;
  while ((ch = next_char ()) == 'c')
    {
      while ((ch = next_char ()) != '\n')
	if (ch == EOF)
	  parse_error ("unexpected end-of-file in header comment");
    }
  if (ch != 'p')
    parse_error ("expected 'c' or 'p'");
  int variables, clauses;
  if (next_char () != ' ' ||
      next_char () != 'c' ||
      next_char () != 'n' ||
      next_char () != 'f' ||
      next_char () != ' ' ||
      !parse_int (&variables, EOF, &ch) ||
      variables < 0 ||
      ch != ' ' || !parse_int (&clauses, EOF, &ch) || clauses < 0)
  INVALID_HEADER:
    parse_error ("invalid 'p cnf ...' header line");
  if (variables > MAX_VAR)
    parse_error ("too many variables (maximum %u)", MAX_VAR);
  while (ch == ' ' || ch == '\t')
    ch = next_char ();
  if (ch != '\n')
    goto INVALID_HEADER;
  message (0, "parsed 'p cnf %d %d' header", variables, clauses);
  *variables_ptr = variables;
  *clauses_ptr = clauses;
}

static void
parse_dimacs_body (struct ruler * ruler, int variables, int expected)
{
  double start_parsing = START (ruler, parsing);
  signed char *marked = ruler->marks;
  struct unsigneds clause;
  INIT (clause);
  int signed_lit = 0, parsed = 0;
  bool trivial = false;
  for (;;)
    {
      int ch = next_char ();
      if (ch == EOF)
	{
      END_OF_FILE:
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
      if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n' && ch != EOF)
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
	      ROG ("skipping trivial clause");
	      trivial = true;
	    }
	  else if (!mark)
	    {
	      PUSH (clause, unsigned_lit);
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
	  unsigned *literals = clause.begin;
	  if (!ruler->inconsistent && !trivial)
	    {
	      const size_t size = SIZE (clause);
	      assert (size <= ruler->size);
	      if (!size)
		{
		  assert (!ruler->inconsistent);
		  very_verbose (0, "%s", "found empty original clause");
		  ruler->inconsistent = true;
		}
	      else if (size == 1)
		{
		  const unsigned unit = *clause.begin;
		  const signed char value = ruler->values[unit];
		  if (value < 0)
		    {
		      assert (!ruler->inconsistent);
		      very_verbose (0, "found inconsistent unit");
		      ruler->inconsistent = true;
		      trace_add_empty (&ruler->buffer);
		    }
		  else if (!value)
		    assign_ruler_unit (ruler, unit);
		}
	      else if (size == 2)
		new_ruler_binary_clause (ruler, literals[0], literals[1]);
	      else
		{
		  struct clause *large_clause =
		    new_large_clause (size, literals, false, 0);
		  ROGCLAUSE (large_clause, "new");
		  PUSH (ruler->clauses, large_clause);
		}
	    }
	  else
	    trivial = false;
	  for (all_elements_on_stack (unsigned, unsigned_lit, clause))
	      marked[IDX (unsigned_lit)] = 0;
	  CLEAR (clause);
	}
      if (ch == 'c')
	goto SKIP_BODY_COMMENT;
      if (ch == EOF)
	goto END_OF_FILE;
    }
  assert (parsed == expected);
  assert (dimacs.file);
  if (dimacs.close == 1)
    fclose (dimacs.file);
  if (dimacs.close == 2)
    pclose (dimacs.file);
  RELEASE (clause);
  ruler->statistics.original = parsed;
  double end_parsing = STOP (ruler, parsing);
  message (0, "parsing took %.2f seconds", end_parsing - start_parsing);
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
extend_witness (struct ring * ring)
{
  LOG ("extending witness");
  struct ruler * ruler = ring->ruler;
#ifndef NDEBUG
  bool * eliminated = ruler->eliminated;
#endif
  signed char * ring_values = ring->values;
  signed char * ruler_values = (signed char*) ruler->values;
  unsigned initialized = 0;
  for (all_ring_indices (idx))
    {
      unsigned lit = LIT (idx);
      if (ring_values[lit])
	continue;
      signed char value = ruler_values[lit];
      if (!value)
	{
	  assert (eliminated[idx]);
	  value = INITIAL_PHASE;
	}
      else
	assert (!eliminated[idx]);
      unsigned not_lit = NOT (lit);
      ring_values[lit] = value;
      ring_values[not_lit] = -value;
      initialized++;
    }
  LOG ("initialized %u unassigned/eliminated variables", initialized);
  struct unsigneds * extension = &ruler->extension;
  unsigned * begin = extension->begin;
  unsigned * p = extension->end;
  unsigned pivot = INVALID;
  bool satisfied = false;
  size_t flipped = 0;
  LOG ("going through extension stack of size %zu", (size_t)(p - begin));
#ifdef LOGGING
  if (verbosity == INT_MAX)
    {
      LOG ("extension stack in reverse order:");
      unsigned * q = p;
      while (q != begin)
	{
	  unsigned * next = q;
	  while (*--next != INVALID)
	    ;
	  LOGPREFIX ("extension clause");
	  for (unsigned * c = next + 1; c != q; c++)
	    printf (" %s", LOGLIT (*c));
	  LOGSUFFIX ();
	  q = next;
	}
    }
#endif
  while (p != begin)
    {
      unsigned lit = *--p;
      if (lit == INVALID)
	{
	  if (!satisfied)
	    {
	      LOG ("flipping %s", LOGLIT (pivot));
	      assert (pivot != INVALID);
	      unsigned not_pivot = NOT (pivot);
	      assert (ring_values[pivot] < 0);
	      assert (ring_values[not_pivot] > 0);
	      ring_values[pivot] = 1;
	      ring_values[not_pivot] = -1;
	      flipped++;
	    }
	  satisfied = false;
	}
      else if (!satisfied)
	{
	  signed char value = ring_values[lit];
	  if (value > 0)
	    satisfied = true;
	}
      pivot = lit;
    }
  verbose (ring, "flipped %zu literals", flipped);
}

static void
print_witness (struct ring *ring)
{
  signed char *values = ring->values;
  for (all_ring_indices (idx))
    print_unsigned_literal (values, LIT (idx));
  print_signed_literal (0);
  if (buffered)
    flush_line ();
}

/*------------------------------------------------------------------------*/
static void *
detach_and_delete_ring (void *ptr)
{
  struct ring *ring = ptr;
  detach_ring (ring);
  delete_ring (ring);
  return ring;
}

static void
start_detaching_and_deleting_ring (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  assert (ruler->threads);
  pthread_t *thread = ruler->threads + ring->id;
  if (pthread_create (thread, 0, detach_and_delete_ring, ring))
    fatal_error ("failed to create deletion thread %u", ring->id);
}

static void
stop_detaching_and_deleting_ring (struct ruler *ruler, unsigned id)
{
  assert (ruler->threads);
  pthread_t *thread = ruler->threads + id;
  if (pthread_join (*thread, 0))
    fatal_error ("failed to join deletion thread %u", id);
}

static void
detach_and_delete_rings (struct ruler *ruler)
{
  size_t threads = SIZE (ruler->rings);
  if (threads > 1)
    {
      if (verbosity > 0)
	{
	  printf ("c deleting %zu rings in parallel\n", threads);
	  fflush (stdout);
	}
#if 1
      for (all_rings (ring))
	start_detaching_and_deleting_ring (ring);

      for (unsigned i = 0; i != threads; i++)
	stop_detaching_and_deleting_ring (ruler, i);
#else
      for (all_rings (ring))
	detach_and_delete_ring (ring);
#endif
    }
  else
    {
      if (verbosity > 0)
	{
	  printf ("c deleting single ring in main thread\n");
	  fflush (stdout);
	}

      struct ring *ring = first_ring (ruler);
      detach_and_delete_ring (ring);
    }
}

/*------------------------------------------------------------------------*/

static volatile int caught_signal;
static volatile bool catching_signals;
static volatile bool catching_alarm;

static struct ruler *ruler;

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

static void print_ruler_statistics (struct ruler *);

static void
caught_message (int sig)
{
  if (verbosity < 0)
    return;
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
  if (ruler)
    print_ruler_statistics (ruler);
  raise (sig);
}

static void
catch_alarm (int sig)
{
  assert (sig == SIGALRM);
  if (!catching_alarm)
    catch_signal (sig);
  if (atomic_exchange (&caught_signal, sig))
    return;
  if (verbosity > 0)
    caught_message (sig);
  reset_alarm_handler ();
  assert (ruler);
  ruler->terminate = true;
  caught_signal = 0;
}

static void
set_alarm_handler (unsigned seconds)
{
  assert (seconds);
  assert (!catching_alarm);
  saved_SIGALRM_handler = signal (SIGALRM, catch_alarm);
  alarm (seconds);
  catching_alarm = true;
}

static void
set_signal_handlers (unsigned seconds)
{
  assert (!catching_signals);
  // *INDENT-OFF*
#define SIGNAL(SIG) \
  saved_ ## SIG ##_handler = signal (SIG, catch_signal);
  SIGNALS
#undef SIGNAL
  // *INDENT-ON*
  catching_signals = true;
  if (seconds)
    set_alarm_handler (seconds);
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

static void
check_witness (struct ring *ring)
{
  signed char *values = ring->values;
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

#else

#define check_witness(...) do { } while (0)

#endif

/*------------------------------------------------------------------------*/

#define begin_ring_profiles ((struct profile *)(&ring->profiles))
#define end_ring_profiles (&ring->profiles.solving)

#define all_ring_profiles(PROFILE) \
struct profile * PROFILE = begin_ring_profiles, \
               * END_ ## PROFILE = end_ring_profiles; \
PROFILE != END_ ## PROFILE; \
++PROFILE

#define begin_ruler_profiles ((struct profile *)(&ruler->profiles))
#define end_ruler_profiles (&ruler->profiles.total)

#define all_ruler_profiles(PROFILE) \
struct profile * PROFILE = begin_ruler_profiles, \
               * END_ ## PROFILE = end_ruler_profiles; \
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
flush_ring_profiles (struct ring *ring)
{
  double time = current_time ();
  for (all_ring_profiles (profile))
    if (profile->start >= 0)
      flush_profile (time, profile);

  flush_profile (time, &ring->profiles.solving);
  return time;
}

static double
flush_ruler_profiles (struct ruler *ruler)
{
  double time = current_time ();
  for (all_ruler_profiles (profile))
    if (profile->start >= 0)
      flush_profile (time, profile);

  flush_profile (time, &ruler->profiles.total);
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
print_ring_profiles (struct ring *ring)
{
  flush_ring_profiles (ring);
  double solving = ring->profiles.solving.time;
  struct profile *prev = 0;
  fputs ("c\n", stdout);
  for (;;)
    {
      struct profile *next = 0;
      for (all_ring_profiles (tmp))
	if (cmp_profiles (tmp, prev) < 0 && cmp_profiles (next, tmp) < 0)
	  next = tmp;
      if (!next)
	break;
      PRINTLN ("%10.2f seconds  %5.1f %%  %s",
	       next->time, percent (next->time, solving), next->name);
      prev = next;
    }
  PRINTLN ("-----------------------------------------");
  PRINTLN ("%10.2f seconds  100.0 %%  solving", solving);
  fputs ("c\n", stdout);
  fflush (stdout);
}

static void
print_ruler_profiles (struct ruler *ruler)
{
  struct ring * ring = 0;
  flush_ruler_profiles (ruler);
  double total = ruler->profiles.total.time;
  struct profile *prev = 0;
  //fputs ("c\n", stdout);
  for (;;)
    {
      struct profile *next = 0;
      for (all_ruler_profiles (tmp))
	if (cmp_profiles (tmp, prev) < 0 && cmp_profiles (next, tmp) < 0)
	  next = tmp;
      if (!next)
	break;
      PRINTLN ("%10.2f seconds  %5.1f %%  %s",
	       next->time, percent (next->time, total), next->name);
      prev = next;
    }
  PRINTLN ("--------------------------------------------");
  PRINTLN ("%10.2f seconds  100.0 %%  total", total);
  fputs ("c\n", stdout);
  fflush (stdout);
}

static void
print_ring_statistics (struct ring *ring)
{
  print_ring_profiles (ring);
  double search = ring->profiles.search.time;
  double walk = ring->profiles.solving.time;
  struct ring_statistics *s = &ring->statistics;
  uint64_t conflicts = s->contexts[SEARCH_CONTEXT].conflicts;
  uint64_t decisions = s->contexts[SEARCH_CONTEXT].decisions;
  uint64_t propagations = s->contexts[SEARCH_CONTEXT].propagations;
  PRINTLN ("%-21s %17" PRIu64 " %13.2f per second", "conflicts:",
	   conflicts, average (conflicts, search));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f per second", "decisions:",
	   decisions, average (decisions, search));
  PRINTLN ("%-21s %17u %13.2f %% variables", "solving-fixed:",
	   s->fixed, percent (s->fixed, ring->size));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f thousands per second",
	   "flips:", s->flips, average (s->flips, 1e3 * walk));

  PRINTLN ("%-21s %17" PRIu64 " %13.2f per learned clause",
	   "learned-literals:", s->literals.learned,
	   average (s->literals.learned, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f times learned literals",
	   "  deduced-literals:", s->literals.deduced,
	   average (s->literals.deduced, s->literals.learned));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% per deduced literal",
	   "  minimized-literals:", s->literals.minimized,
	   percent (s->literals.minimized, s->literals.deduced));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% per deduced literal",
	   "  shrunken-literals:", s->literals.shrunken,
	   percent (s->literals.shrunken, s->literals.deduced));

  PRINTLN ("%-21s %17" PRIu64 " %13.2f per second",
	   "learned-clauses:", s->learned.clauses,
	   average (s->learned.clauses, search));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-units:", s->learned.units,
	   percent (s->learned.units, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-binary:", s->learned.binary,
	   percent (s->learned.binary, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-glue1:", s->learned.glue1,
	   percent (s->learned.glue1, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-tier1:", s->learned.tier1,
	   percent (s->learned.tier1, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-tier2:", s->learned.tier2,
	   percent (s->learned.tier2, s->learned.clauses));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	   "  learned-tier3:", s->learned.tier3,
	   percent (s->learned.tier3, s->learned.clauses));

  if (ring->pool)
    {
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	       "imported-clauses:", s->imported.clauses,
	       percent (s->imported.clauses, s->learned.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% imported",
	       "  imported-units:", s->imported.units,
	       percent (s->imported.units, s->imported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% imported",
	       "  imported-binary:", s->imported.binary,
	       percent (s->imported.binary, s->imported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% imported",
	       "  imported-glue1:", s->imported.glue1,
	       percent (s->imported.glue1, s->imported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% imported",
	       "  imported-tier1:", s->imported.tier1,
	       percent (s->imported.tier1, s->imported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% imported",
	       "  imported-tier2:", s->imported.tier2,
	       percent (s->imported.tier2, s->imported.clauses));

      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% learned",
	       "exported-clauses:", s->exported.clauses,
	       percent (s->exported.clauses, s->learned.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% exported",
	       "  exported-units:", s->exported.units,
	       percent (s->exported.units, s->exported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% exported",
	       "  exported-binary:", s->exported.binary,
	       percent (s->exported.binary, s->exported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% exported",
	       "  exported-glue1:", s->exported.glue1,
	       percent (s->exported.glue1, s->exported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% exported",
	       "  exported-tier1:", s->exported.tier1,
	       percent (s->exported.tier1, s->exported.clauses));
      PRINTLN ("%-21s %17" PRIu64 " %13.2f %% exported",
	       "  exported-tier2:", s->exported.tier2,
	       percent (s->exported.tier2, s->exported.clauses));
    }

  PRINTLN ("%-21s %17" PRIu64 " %13.2f millions per second",
	   "propagations:", propagations, average (propagations,
						   1e6 * search));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f conflict interval",
	   "reductions:", s->reductions, average (conflicts, s->reductions));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f conflict interval",
	   "rephased:", s->rephased, average (conflicts, s->rephased));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f conflict interval",
	   "restarts:", s->restarts, average (conflicts, s->restarts));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f conflict interval",
	   "switched:", s->switched, average (conflicts, s->switched));
  PRINTLN ("%-21s %17" PRIu64 " %13.2f flips per walkinterval",
	   "walked:", s->walked, average (s->flips, s->walked));
  fflush (stdout);
}

static void
print_ruler_statistics (struct ruler *ruler)
{
  if (verbosity < 0)
    return;

  for (all_rings (ring))
    {
      print_ring_statistics (ring);
      printf ("c\n");
    }

  print_ruler_profiles (ruler);

  double process = process_time ();
  double total = current_time () - start_time;
  double memory = maximum_resident_set_size () / (double) (1 << 20);

  struct ruler_statistics * s = &ruler->statistics;

  unsigned variables = ruler->size;

  printf ("c %-22s %17u %13.2f %% variables\n", "eliminated:",
          s->eliminated, percent (s->eliminated, variables));
  printf ("c %-22s %17u %13.2f %% eliminated variables\n", "definitions:",
          s->definitions, percent (s->definitions, s->eliminated));
  printf ("c %-22s %17u %13.2f %% variables\n", "substituted:",
          s->substituted, percent (s->substituted, variables));
  printf ("c %-22s %17u %13.2f %% subsumed clauses\n", "deduplicated:",
          s->deduplicated, percent (s->deduplicated, s->subsumed));
  printf ("c %-22s %17u %13.2f %% subsumed clauses\n", "self-subsumed::",
          s->selfsubsumed, percent (s->selfsubsumed, s->subsumed));
  printf ("c %-22s %17u %13.2f %% original clauses\n", "strengthened:",
          s->strengthened, percent (s->strengthened, s->original));
  printf ("c %-22s %17u %13.2f %% original clauses\n", "subsumed:",
          s->subsumed, percent (s->subsumed, s->original));
  printf ("c %-22s %17u %13.2f %% total-fixed\n", "simplifying-fixed:",
          s->fixed.simplifying, percent (s->fixed.simplifying, s->fixed.total));
  printf ("c %-22s %17u %13.2f %% total-fixed\n", "solving-fixed:",
          s->fixed.solving, percent (s->fixed.solving, s->fixed.total));
  printf ("c %-22s %17u %13.2f %% variables\n", "total-fixed:",
          s->fixed.total, percent (s->fixed.total, variables));

  printf ("c\n");

  printf ("c %-30s %23.2f %%\n", "utilization:",
	  percent (process / SIZE (ruler->rings), total));
  printf ("c %-30s %23.2f seconds\n", "process-time:", process);
  printf ("c %-30s %23.2f seconds\n", "wall-clock-time:", total);
  printf ("c %-30s %23.2f MB\n", "maximum-resident-set-size:", memory);

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
  CHECK_TYPE (void *, 8);
  
  {
    if (MAX_THREADS & 7)
      fatal_error ("'MAX_THREADS = %u' not byte aligned", MAX_THREADS);
    size_t bytes_of_shared_field = sizeof ((struct clause *) 0)->shared;
    if ((MAX_THREADS >> 3) > (1u << (bytes_of_shared_field * 8 - 3)))
      fatal_error ("shared field of clauses with %zu bytes "
                   "does not fit 'MAX_THREADS = %u'",
		   bytes_of_shared_field, MAX_THREADS);
  }

  {
    size_t glue_in_clause_bytes = sizeof ((struct clause *) 0)->glue;
    if (glue_in_clause_bytes << 8 <= MAX_GLUE)
      fatal_error ("'MAX_GLUE = %u' exceeds 'sizeof (clause.glue) = %zu'",
		   MAX_GLUE, glue_in_clause_bytes);
  }

  {
    size_t glue_in_watch_bytes = sizeof ((struct watch *) 0)->glue;
    if (glue_in_watch_bytes << 8 <= MAX_GLUE)
      fatal_error ("'MAX_GLUE = %u' exceeds 'sizeof (watch.glue) = %zu'",
		   MAX_GLUE, glue_in_watch_bytes);
  }

  if (verbosity > 0)
    {
      fputs ("c\n", stdout);
      printf ("c sizeof (struct watch) = %zu\n", sizeof (struct watch));
      printf ("c sizeof (struct clause) = %zu\n", sizeof (struct clause));
      print_walker_types ();
    }
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
  if (verbosity >= 0 && proof.file)
    {
      printf ("c\nc writing %s proof trace to '%s'\n",
	      binary_proof_format ? "binary" : "ASCII", proof.path);
      fflush (stdout);
    }
  int variables, clauses;
  parse_dimacs_header (&variables, &clauses);
  ruler = new_ruler (variables, &options);
  set_signal_handlers (options.seconds);
  parse_dimacs_body (ruler, variables, clauses);
  simplify_ruler (ruler);
  clone_rings (ruler);
  run_rings (ruler);
  struct ring *winner = (struct ring *) ruler->winner;
  int res = winner ? winner->status : 0;
  reset_signal_handlers ();
  close_proof ();
  if (res == 20)
    {
      if (verbosity >= 0)
	printf ("c\n");
      printf ("s UNSATISFIABLE\n");
      fflush (stdout);
    }
  else if (res == 10)
    {
      extend_witness (winner);
      check_witness (winner);
      if (verbosity >= 0)
	printf ("c\n");
      printf ("s SATISFIABLE\n");
      if (witness)
	print_witness (winner);
      fflush (stdout);
    }
  print_ruler_statistics (ruler);
  detach_and_delete_rings (ruler);
  delete_ruler (ruler);
#ifndef NDEBUG
  RELEASE (original);
#endif
  if (verbosity >= 0)
    {
      printf ("c\nc exit %d\n", res);
      fflush (stdout);
    }
  return res;
}
