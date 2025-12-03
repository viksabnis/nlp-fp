#ifndef	TIMER_H
#define	TIMER_H

#include	<stdio.h>

// allocate a new timer
int	new_timer(char	*name);

// start the specified timer
void start_timer(int	timer);

// stop the specified timer, and optionally
//   treat the elapsed time as `count' separate
//   events when producing reports
double stop_timer(int	timer, int	count);

// print the given time interval in the most
//   appropriate units (e.g. microseconds, or minutes)
void	fprint_time(FILE	*f, double seconds);

// show the state of every registered timer on stdout
void	report_timers();
void	freport_timers(FILE	*f);

// write an XML representation of the state of every registered
//   timer to the stream `f', with schema:
//    <timers>
//      <timer name='countdown' total='3m 20s' events='374' per='0.535s'/>
//    </timers>
void	xml_timers(FILE	*f);

// log a single line record to `fname',
//   consisting of tab-separated total elapsed times for each timer
void	log_timers(char	*fname);

#endif
