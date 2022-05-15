#include "allocate.h"
#include "build.h"
#include "file.h"
#include "options.h"
#include "message.h"

#include <ctype.h>
#include <string.h>

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

static FILE *
open_and_read_from_pipe (const char *path, const char *fmt)
{
  char *cmd = allocate_block (strlen (path) + strlen (fmt));
  sprintf (cmd, fmt, path);
  FILE *file = popen (cmd, "r");
  free (cmd);
  return file;
}

extern const char * gimsatul_usage;

void
parse_options (int argc, char **argv, struct options *opts)
{
  memset (opts, 0, sizeof *opts);
  opts->conflicts = -1;
  opts->witness = true;
  opts->binary = true;
  const char *quiet_opt = 0;
  const char *verbose_opt = 0;
  for (int i = 1; i != argc; i++)
    {
      const char *opt = argv[i], *arg;
      if (!strcmp (opt, "-a") || !strcmp (opt, "--ascii"))
	opts->binary = false;
      else if (!strcmp (opt, "-f") || !strcmp (opt, "--force"))
	opts->force = true;
      else if (!strcmp (opt, "-h") || !strcmp (opt, "--help"))
	{
	  printf (gimsatul_usage, (size_t) MAX_THREADS);
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
	opts->witness = false;
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
	  print_version ();
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
	    die ("multiple '--threads=%u' and '%s'", opts->threads, opt);
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
      else if (opts->proof.file)
	die ("too many arguments");
      else if (opts->dimacs.file)
	{
	  if (!strcmp (opt, "-"))
	    {
	      opts->proof.path = "<stdout>";
	      opts->proof.file = stdout;
	      opts->binary = false;
	    }
	  else if (!opts->force && looks_like_dimacs (opt))
	    die ("proof file '%s' looks like a DIMACS file (use '-f')", opt);
	  else if (!(opts->proof.file = fopen (opt, "w")))
	    die ("can not open and write to '%s'", opt);
	  else
	    {
	      opts->proof.path = opt;
	      opts->proof.close = true;
	    }
	}
      else
	{
	  if (!strcmp (opt, "-"))
	    {
	      opts->dimacs.path = "<stdin>";
	      opts->dimacs.file = stdin;
	    }
	  else if (has_suffix (opt, ".bz2"))
	    {
	      opts->dimacs.file = open_and_read_from_pipe (opt, "bzip2 -c -d %s");
	      opts->dimacs.close = 2;
	    }
	  else if (has_suffix (opt, ".gz"))
	    {
	      opts->dimacs.file = open_and_read_from_pipe (opt, "gzip -c -d %s");
	      opts->dimacs.close = 2;
	    }
	  else if (has_suffix (opt, ".xz"))
	    {
	      opts->dimacs.file = open_and_read_from_pipe (opt, "xz -c -d %s");
	      opts->dimacs.close = 2;
	    }
	  else
	    {
	      opts->dimacs.file = fopen (opt, "r");
	      opts->dimacs.close = 1;
	    }
	  if (!opts->dimacs.file)
	    die ("can not open and read from '%s'", opt);
	  opts->dimacs.path = opt;
	}
    }

  if (!opts->dimacs.file)
    {
      opts->dimacs.path = "<stdin>";
      opts->dimacs.file = stdin;
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

