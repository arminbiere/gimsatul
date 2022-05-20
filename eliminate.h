#ifndef _eliminate_h_INCLUDED
#define _eliminate_h_INCLUDED

#include <stdbool.h>

struct simplifier;
bool eliminate_variables (struct simplifier *, unsigned round);

#endif
