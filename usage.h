// *INDENT-OFF*

static char * compact_usage = 

"usage: gimsatul [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -a | --ascii                use ASCII format for proof output\n"
"  -f | --force                force reading and writing\n"
"  -h | --help  | --full       command line options ('--full' for full list)\n"
"  -i | --id                   source code version identifier (GIT hash)\n"
#ifdef LOGGING                
"  -l | --log   | --logging    enable very verbose internal logging\n"
#endif                        
"  -n | --no-witness           do not print satisfying assignments\n"
"  -O | -O<level>              increase simplification ticks and round limits\n"
#ifndef QUIET                 
"  -q | --quiet                disable all additional messages\n"
#endif                        
"  -r | --resources            summarize used resources\n"
#ifndef QUIET                 
"  -v | --verbose              increase verbosity\n"
#endif                        
"  -V | --version              print version\n"
"\n"                          
"  --conflicts=<conflicts>     limit conflicts (0... - default unlimited)\n"
"  --threads=<number>          set number of threads (1..%zu - default 1)\n"
"  --time=<seconds>            limit time (1... - default unlimited)\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof trace file in 'DRAT' format (no proof if missing).\n"

;

static char * additional_less_common_options =

"  --embedded                  print options to embed them in CNF (delta debugging)\n"
"  --range                     print option ranges (fuzzing)\n"

;

// *INDENT-ON*
