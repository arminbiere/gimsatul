#ifndef _import_h_INCLUDED
#define _import_h_INCLUDED

#include <stdbool.h>

struct ring;
bool import_shared (struct ring *);
void flush_import (struct ring *);

#endif
