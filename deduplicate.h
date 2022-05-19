#ifndef _deduplicate_h_INCLUDED
#define _deduplicate_h_INCLUDED

#include <stdbool.h>

struct ruler;

bool remove_duplicated_binaries (struct ruler *, unsigned round);

#endif
