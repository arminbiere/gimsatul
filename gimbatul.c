// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

static const char * usage =
"usage: gimbatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-h    print this command line option summary\n"
"-n    do not print satisfying assignments\n"
"-a    use ASCII proof format\n"
"\n"
"and '<dimacs>' is the path to the input DIMACS file ('<stdin>' if missing)\n"
"and '<proof>' the path to the output 'DRAT' proof file.\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <inttypes.h>
#include <pthread.h>
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

struct file
{
  const char * path;
  FILE * file;
  bool close;
  size_t lines;
};

static struct file dimacs, proof;

static double start_time;

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
parse_command_line_options (int argc, char ** argv)
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
      else if (proof.file)
	die ("too many file arguments");
      else if (dimacs.file)
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
      else
	{
	  if (!strcmp (arg, "-"))
	    {
	      proof.path = "<stdout>";
	      proof.file = stdout;
	      binary = false;
	    }
	  else if (!(proof.file = fopen (arg, "w")))
	    die ("can not open and write to '%s'", arg);
	  else
	    {
	      proof.path = arg;
	      proof.close = true;
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

static int
next_char (void)
{
  int res = getc (dimacs.file);
  if (res == '\n')
    dimacs.lines++;
  return res;
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
    parser_error ("expected 'c' or 'p'");
  unsigned variables, clauses;
  if (next_char () != ' ' ||
      next_char () != 'c' ||
      next_char () != 'n' ||
      next_char () != 'f' ||
      next_char () != ' ' ||
      !parse_int (&variables, 
  assert (dimacs.file);
  if (dimacs.close)
    fclose (dimacs.file);
}

static void
close_proof (void)
{
  if (!proof.file)
    return;
  if (proof.close)
    fclose (proof.file);
  message ("closing proof file '%s' after writing %zu lines",
           proof.path, proof.lines);
}

static void
print_statistics (void)
{
  double p = process_time ();
  double w = wall_clock_time () - start_time;
  double m = maximum_resident_set_size () / (double) (1<<20);
  message ("%-30s%.2f sec", "process-time:", p);
  message ("%-30s%.2f sec", "wall-clock-time:", w);
  message ("%-30s%.2f MB", "maximum-resident-set-size:", m);
}

int
main (int argc, char ** argv)
{
  start_time = wall_clock_time ();
  parse_command_line_options (argc, argv);
  print_banner ();
  parse_dimacs_file ();
  int res = 0;
  close_proof ();
  print_statistics ();
  message ("exit %d", res);
  return res;
}
