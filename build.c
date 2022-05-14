#include "build.h"
#include "config.h"

#include <stdio.h>

extern int verbosity;

void
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

void
print_version (void)
{
  printf ("%s\n", VERSION);
}
