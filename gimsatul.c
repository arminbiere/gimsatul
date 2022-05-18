// Copyright (c) 2022 Armin Biere University of Freiburg

// *INDENT-OFF*

const char * gimsatul_usage =
"usage: gimsatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -a|--ascii|--no-binary   use ASCII format for proof output\n"
"  -f|--force               force reading and writing\n"
"  -h|--help                print this command line option summary\n"
#ifdef LOGGING   
"  -l|--log[ging]           enable very verbose internal logging\n"
#endif                   
"  -n|--no-witness          do not print satisfying assignments\n"
"  -O|-O<level>             increase simplification ticks and round limits\n"
"  -q|--quiet               disable all additional messages\n"
"  -v|--verbose             increase verbosity\n"
"  -V|--version             print version\n"
"\n"
"  --conflicts=<conflicts>  limit conflicts (0,1,... - default unlimited)\n"
"  --threads=<number>       set number of threads (1,...,%zu - default 1)\n"
"  --time=<seconds>         limit time (1,2,3,... - default unlimited)\n"
"\n"
"  --walk-initially         one additional round of initial local search\n"
"\n"
"  --no-fail                disable failed literal probing\n"
"  --no-eliminate           disable clause subsumption and strengthening\n"
"  --no-probe               disable probing (fail + vivify)\n"
"  --no-simplify            disable all preprocessing and inprocessing\n"
"  --no-substitute          disable equivalent literal substitution\n"
"  --no-subsume             disable failed literal probing\n"
"  --no-vivify              disable redundant clause vivification\n"
"  --no-walk                disable local search during rephasing\n"
"\n"
"  --reduce-interval        clause reduction conflict interval\n"
"  --probe-interval         clause reduction conflict interval\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof trace file in 'DRAT' format (no proof if missing).\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

#include "build.h"
#include "catch.h"
#include "clone.h"
#include "detach.h"
#include "message.h"
#include "parse.h"
#include "ruler.h"
#include "simplify.h"
#include "solve.h"
#include "statistics.h"
#include "types.h"
#include "witness.h"

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
	      options.no_binary ? "ASCII" : "binary", options.proof.path);
      fflush (stdout);
    }
  int variables, clauses;
  parse_dimacs_header (&options.dimacs, &variables, &clauses);
  struct ruler * ruler = new_ruler (variables, &options);
  set_signal_handlers (ruler);
  parse_dimacs_body (ruler, variables, clauses);
  simplify_ruler (ruler);
  clone_rings (ruler);
  struct ring *winner = solve_rings (ruler);
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
      if (!options.no_witness)
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
