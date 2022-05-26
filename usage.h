// *INDENT-OFF*

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
#ifndef QUIET
"  -q|--quiet               disable all additional messages\n"
"  -v|--verbose             increase verbosity\n"
#endif
"  -V|--version             print version\n"
"\n"
"  --conflicts=<conflicts>  limit conflicts (0,1,... - default unlimited)\n"
"  --threads=<number>       set number of threads (1,...,%zu - default 1)\n"
"  --time=<seconds>         limit time (1,2,3,... - default unlimited)\n"
"\n"
"and '<dimacs>' is the input file in 'DIMACS' format ('<stdin>' if missing)\n"
"and '<proof>' the proof trace file in 'DRAT' format (no proof if missing).\n"

// *INDENT-ON*
