#ifndef _bump_h_INCLUDED
#define _bump_h_INCLUDED

struct ring;

void bump_variable_score (struct ring *, unsigned idx);
void bump_score_increment (struct ring *);
void swap_scores (struct ring *);

#endif
