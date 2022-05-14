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
#include "catch.h"
#include "clause.h"
#include "clone.h"
#include "config.h"
#include "detach.h"
#include "export.h"
#include "logging.h"
#include "macros.h"
#include "message.h"
#include "options.h"
#include "parse.h"
#include "report.h"
#include "ring.h"
#include "random.h"
#include "ruler.h"
#include "simplify.h"
#include "search.h"
#include "stack.h"
#include "solve.h"
#include "statistics.h"
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
  struct ruler * ruler = new_ruler (variables, &options);
  set_signal_handlers (ruler);
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
