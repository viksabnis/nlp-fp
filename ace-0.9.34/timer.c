#include	<sys/time.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>
#include	<stdlib.h>
#include	"timer.h"

static struct timeval	times[100];
static char				*timernames[100];
static double			total[100], lap[100];
static long long		events[100];
static long long		int_calls[100];
static long long		calls[100];
static long long		ocount, ostart[100];
static int				ntimers;

int	new_timer(char	*name)
{
	timernames[ntimers] = strdup(name);
	return ntimers++;
}

void start_timer(int	i)
{
	gettimeofday(&times[i], 0);
	ostart[i] = ocount;
}

double stop_timer(int	i, int	count)
{
	struct timeval	tv;
	double t;
	gettimeofday(&tv, 0);
	t = tv.tv_sec - times[i].tv_sec;
	ocount++;
	t += 0.000001 * (double)(tv.tv_usec - times[i].tv_usec);// - 0.000002116 * (ocount - ostart[i]);
	int_calls[i] += ocount - ostart[i] - 1;
	calls[i] += 1;
	total[i] += t;
	times[i] = tv;
	events[i]+=count;
	return t;
}

void	fprint_time(FILE	*f, double s)
{
	int m = s/60, h = m/60;
	if(h) { fprintf(f, "%dh ", h); m -= 60*h; s -= 60*60*h; }
	if(h || m) { fprintf(f, "%dm ", m); s -= 60*m; }
	if(h || m)fprintf(f, "%ds", (int)s);
	else if(s > 0.5)fprintf(f, "%.3fs", s);
	else if(s > 0.0005)fprintf(f, "%.1fms", s*1000);
	else fprintf(f, "%.1fµs", s*1000000);
}

//const double k_overhead = 0.000002116
const double k_int_overhead = 0.000000137;
const double k_self_overhead = 0.000000064;

void	freport_timers(FILE	*f)
{
	int i;
	fprintf(f, "TIMERS (%lld calls = ~ ", ocount);
	fprint_time(f, k_int_overhead * ocount);
	fprintf(f, " overhead):\n");
	for(i=0;i<ntimers;i++)
	{
		double	t_minus_oh = total[i] - k_int_overhead * int_calls[i] - k_self_overhead * calls[i];
		fprintf(f, "%-32s	", timernames[i]);
		fprint_time(f, t_minus_oh);
		if(events[i]>0)
		{
			fprintf(f, "	for %lld events = ", events[i]);
			fprint_time(f, events[i]?(t_minus_oh / events[i]):t_minus_oh);
			fprintf(f, " per event\n");
		}
		else fprintf(f, "\n");
	}
}

void	report_timers()
{
	freport_timers(stdout);
}

void	xml_timers(FILE	*f)
{
	int i;
	fprintf(f, "<timers>\n");
	for(i=0;i<ntimers;i++)
	{
		fprintf(f, "<timer name='%s' total='", timernames[i]);
		fprint_time(f, total[i]);
		fprintf(f, "' events='%lld' per='", events[i]);
		fprint_time(f, events[i]?(total[i] / events[i]):total[i]);
		fprintf(f, "'/>\n");
	}
	fprintf(f, "</timers>\n");
}

void	log_timers(char	*fname)
{
	int i;
	FILE	*f = fopen(fname, "a"); assert(f!=0);
	for(i=0;i<ntimers;i++)
	{
		fprintf(f, "%f%c", total[i] - lap[i], (i==(ntimers-1))?'\n':'	');
		lap[i] = total[i];
	}
	fclose(f);
}
