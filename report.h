#ifndef _report_h_INCLUDED
#define _report_h_INCLUDED

struct ring;

void report (struct ring *, char);
void verbose_report (struct ring *, char, int level);

#endif
