// Copyright 2022 (c) Armin Biere, University of Freiburg, Germany

// *INDENT-OFF*

static const char * usage =
"usage: gimbatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"-h    print this command line option summary\n"
"-n    do not print satisfying assignments\n"
"\n"
"and '<dimacs>' is the path to the input DIMACS file ('<stdin>' if missing)\n"
"and '<proof>' the path to the output 'DRAT' proof file.\n"
;

// *INDENT-ON*

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>

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

struct file
{
  const char * path;
  FILE * file;
  bool close;
  long lines;
};

static struct file dimacs, proof;
static bool witness = true;

int
main (int argc, char ** argv)
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
  int res = 0;
  if (dimacs.close)
    fclose (dimacs.file);
  if (proof.close)
    fclose (proof.file);
  return res;
}
