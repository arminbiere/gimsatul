#ifndef _promote_h_INCLUDED
#define _promote_h_INCLUDED

struct ring;
struct clause;

unsigned recompute_glue (struct ring *, struct clause *);
void promote_clause (struct ring *, struct clause *, unsigned new_glue);

#endif
