#ifndef _variable_h_INCLUDED
#define _variable_h_INCLUDED

#include <stdbool.h>

struct watch;

struct phases
{
  signed char best:2;
  signed char saved:2;
  signed char target:2;
};

struct variable
{
  unsigned level;
  bool minimize:1;
  bool poison:1;
  bool seen:1;
  bool shrinkable:1;
  struct watch *reason;
};

#endif
