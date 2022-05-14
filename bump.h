#ifndef _bump_h_INCLUDED
#define _bump_h_INCLUDED

struct ring;

void bump_variable_on_heap (struct ring *, unsigned idx);
void sort_and_bump_analyzed_variables_on_queue (struct ring *);
void bump_score_increment (struct ring *);
void rebuild_heap (struct ring *);

#endif
