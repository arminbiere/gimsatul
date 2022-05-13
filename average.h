#ifndef _average_h_INCLUDED
#define _average_h_INCLUDED

struct average
{
  double value, biased, exp;
};

void update_average (struct average *, double alpha, double y);

#endif
