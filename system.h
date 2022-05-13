#ifndef _system_h_INCLUDED
#define _system_h_INCLUDED

#include <stdlib.h>

extern double start_time;

double process_time (void);
double current_time (void);
double wall_clock_time (void);
size_t maximum_resident_set_size (void);
size_t current_resident_set_size (void);

#endif
