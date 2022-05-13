#ifndef _eliminate_h_INCLUDED
#define _eliminate_h_INCLUDED

#include <stdbool.h>

struct ruler;
bool eliminate_variables (struct ruler *, unsigned round);

#endif
