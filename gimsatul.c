// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

const char * gimsatul_usage =
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
#include "build.h"
#include "backtrack.h"
#include "clause.h"
#include "clone.h"
#include "config.h"
#include "detach.h"
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
#include "types.h"
#include "utilities.h"
#include "walk.h"
#include "witness.h"

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

static void parse_error (struct file * dimacs, const char *, ...)
  __attribute__((format (printf, 2, 3)));

static void
parse_error (struct file * dimacs, const char *fmt, ...)
{
  fprintf (stderr, "gimsatul: parse error: at line %" PRIu64 " in '%s': ",
	   dimacs->lines, dimacs->path);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

/*------------------------------------------------------------------------*/

static int
next_char (struct file * dimacs)
{
  int res = getc (dimacs->file);
  if (res == '\r')
    {
      res = getc (dimacs->file);
      if (res != '\n')
	return EOF;
    }
  if (res == '\n')
    dimacs->lines++;
  return res;
}

static bool
parse_int (struct file * dimacs, int *res_ptr, int prev, int *next)
{
  int ch = prev == EOF ? next_char (dimacs) : prev;
  int sign = 1;
  if (ch == '-')
    {
      sign = -1;
      ch = next_char (dimacs);
      if (!isdigit (ch) || ch == '0')
	return false;
    }
  else if (!isdigit (ch))
    return false;
  unsigned tmp = ch - '0';
  while (isdigit (ch = next_char (dimacs)))
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

static void
parse_dimacs_header (struct file * dimacs,
                     int * variables_ptr, int * clauses_ptr)
{
  if (verbosity >= 0)
    {
      printf ("c\nc parsing DIMACS file '%s'\n", dimacs->path);
      fflush (stdout);
    }
  int ch;
  while ((ch = next_char (dimacs)) == 'c')
    {
      while ((ch = next_char (dimacs)) != '\n')
	if (ch == EOF)
	  parse_error (dimacs, "unexpected end-of-file in header comment");
    }
  if (ch != 'p')
    parse_error (dimacs, "expected 'c' or 'p'");
  int variables, clauses;
  if (next_char (dimacs) != ' ' ||
      next_char (dimacs) != 'c' ||
      next_char (dimacs) != 'n' ||
      next_char (dimacs) != 'f' ||
      next_char (dimacs) != ' ' ||
      !parse_int (dimacs, &variables, EOF, &ch) || variables < 0 ||
      ch != ' ' || !parse_int (dimacs, &clauses, EOF, &ch) || clauses < 0)
  INVALID_HEADER:
    parse_error (dimacs, "invalid 'p cnf ...' header line");
  if (variables > MAX_VAR)
    parse_error (dimacs, "too many variables (maximum %u)", MAX_VAR);
  while (ch == ' ' || ch == '\t')
    ch = next_char (dimacs);
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
  struct file * dimacs = &ruler->options.dimacs;
  signed char *marked = ruler->marks;
  struct unsigneds clause;
  INIT (clause);
  int signed_lit = 0, parsed = 0;
  struct unsigneds * original = ruler->original;
  bool trivial = false;
  for (;;)
    {
      int ch = next_char (dimacs);
      if (ch == EOF)
	{
      END_OF_FILE:
	  if (signed_lit)
	    parse_error (dimacs, "terminating zero missing");
	  if (parsed != expected)
	    parse_error (dimacs, "clause missing");
	  break;
	}
      if (ch == ' ' || ch == '\t' || ch == '\n')
	continue;
      if (ch == 'c')
	{
	SKIP_BODY_COMMENT:
	  while ((ch = next_char (dimacs)) != '\n')
	    if (ch == EOF)
	      parse_error (dimacs, "invalid end-of-file in body comment");
	  continue;
	}
      if (!parse_int (dimacs, &signed_lit, ch, &ch))
	parse_error (dimacs, "failed to parse literal");
      if (signed_lit == INT_MIN || abs (signed_lit) > variables)
	parse_error (dimacs, "invalid literal %d", signed_lit);
      if (parsed == expected)
	parse_error (dimacs, "too many clauses");
      if (ch != 'c' && ch != ' ' && ch != '\t' && ch != '\n' && ch != EOF)
	parse_error (dimacs, "invalid character after '%d'", signed_lit);
      if (signed_lit)
	{
	  unsigned idx = abs (signed_lit) - 1;
	  assert (idx < (unsigned) variables);
	  signed char sign = (signed_lit < 0) ? -1 : 1;
	  signed char mark = marked[idx];
	  unsigned unsigned_lit = 2 * idx + (sign < 0);
	  if (original)
	    PUSH (*original, unsigned_lit);
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
	  if (original)
	    PUSH (*original, INVALID);
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
		      trace_add_empty (&ruler->trace);
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
  assert (dimacs->file);
  if (dimacs->close == 1)
    fclose (dimacs->file);
  if (dimacs->close == 2)
    pclose (dimacs->file);
  RELEASE (clause);
  ruler->statistics.original = parsed;
  double end_parsing = STOP (ruler, parsing);
  message (0, "parsing took %.2f seconds", end_parsing - start_parsing);
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

int
main (int argc, char **argv)
{
  start_time = current_time ();
  struct options options;
  parse_options (argc, argv, &options);
  print_banner ();
  check_types ();
  if (verbosity >= 0 && options.proof.file)
    {
      printf ("c\nc writing %s proof trace to '%s'\n",
	      options.binary ? "binary" : "ASCII", options.proof.path);
      fflush (stdout);
    }
  int variables, clauses;
  parse_dimacs_header (&options.dimacs, &variables, &clauses);
  ruler = new_ruler (variables, &options);
  set_signal_handlers (options.seconds);
  parse_dimacs_body (ruler, variables, clauses);
  simplify_ruler (ruler);
  clone_rings (ruler);
  run_rings (ruler);
  struct ring *winner = (struct ring *) ruler->winner;
  int res = winner ? winner->status : 0;
  reset_signal_handlers ();
  close_proof (&options.proof);
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
      check_witness (winner, ruler->original);
      if (verbosity >= 0)
	printf ("c\n");
      printf ("s SATISFIABLE\n");
      if (options.witness)
	print_witness (winner);
      fflush (stdout);
    }
  print_ruler_statistics (ruler);
  detach_and_delete_rings (ruler);
  delete_ruler (ruler);
  if (verbosity >= 0)
    {
      printf ("c\nc exit %d\n", res);
      fflush (stdout);
    }
  return res;
}
