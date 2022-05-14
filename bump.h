#ifndef _bump_h_INCLUDED
#define _bump_h_INCLUDED

struct ring;

void bump_variable (struct ring *, unsigned idx);
void bump_score_increment (struct ring *);
void rebuild_heap (struct ring *);

#endif
