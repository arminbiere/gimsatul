#ifndef _subsume_h_INCLUDED
#define _subsume_h_INCLUDED

#include <stdbool.h>

struct ruler;

bool subsume_clauses (struct ruler *, unsigned round);

#endif
