#ifndef _export_h_INCLUDED
#define _export_h_INCLUDED

struct clause;
struct ring;
struct watch;

void export_units (struct ring *);
void export_binary (struct ring *, struct watch *);
void export_glue1_clause (struct ring *, struct clause *);
void export_tier1_clause (struct ring *, struct clause *);
void export_tier2_clause (struct ring *, struct clause *);

#endif

