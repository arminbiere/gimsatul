#ifndef _variable_h_INCLUDED
#define _variable_h_INCLUDED

#include <stdbool.h>

struct watch;

struct variable
{
  unsigned level;
  signed char best;
  signed char saved;
  signed char target;
  bool minimize:1;
  bool poison:1;
  bool seen:1;
  bool shrinkable:1;
  struct watch *reason;
};

#endif
