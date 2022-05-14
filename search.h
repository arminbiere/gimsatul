#ifndef _search_h_INCLUDED
#define _search_h_INCLUDED

struct ring;

void warming_up_saved_phases (struct ring *);
void backtrack (struct ring *, unsigned level);
int solve (struct ring *) ;

#endif
