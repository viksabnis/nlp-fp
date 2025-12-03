#include	<sys/time.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>
#include	<stdlib.h>
#include	"profiler.h"

struct profiler	*new_profiler(char	*name, struct profiler	*parent)
{
	struct profiler	*p = calloc(sizeof(*p),1);
	if(parent)
	{
		parent->nsub++;
		parent->sub = realloc(parent->sub, sizeof(struct profiler*)*parent->nsub);
		parent->sub[parent->nsub-1] = p;
	}
	p->name = strdup(name);
	return p;
}

void	start_profiler(struct profiler	*prof)
{
	if(prof->isrunning)
		fprintf(stderr, "ERROR: can't start profiler `%s'; it's already running.\n", prof->name);
	prof->isrunning = 1;
	gettimeofday(&prof->started, NULL);
}

void	start_and_alloc_profiler(struct profiler	**prof, char	*name, struct profiler	*parent, struct profiler	*tostop)
{
	if(!*prof)
		*prof = new_profiler(name, parent);
	start_profiler(*prof);
	if(tostop)stop_profiler(tostop, 1);
}

double	stop_profiler(struct profiler	*prof, int	nevents)
{
	if(!prof->isrunning)
	{
		fprintf(stderr, "ERROR: can't stop profiler `%s'; it's not running.\n", prof->name);
		return 0;
	}
	prof->isrunning = 0;
	struct timeval	stopped;
	gettimeofday(&stopped, NULL);
	double	dt = stopped.tv_sec - prof->started.tv_sec;
	dt += 0.000001 * (stopped.tv_usec - prof->started.tv_usec);
	prof->elapsed += dt;
	prof->ncalls++;
	prof->nevents += nevents;
	return dt;
}

void	sort_profiler(struct profiler	*prof)
{
	int pcmp(const struct profiler	**a, const struct profiler	**b)
	{
		if((*a)->elapsed > (*b)->elapsed)return -1;
		if((*a)->elapsed < (*b)->elapsed)return +1;
		return 0;
	}
	qsort(prof->sub, prof->nsub, sizeof(struct profiler*), (int(*)(const void*,const void*))pcmp);
}

void	freport_profiler_indent(FILE	*fout, struct profiler	*prof, int	ind)
{
	int i;
	for(i=0;i<ind;i++)
		fprintf(fout, "    ");
	fprintf(fout, "%32s \033[1;34m:\033[0m ", prof->name);
	fprint_time(fout, prof->elapsed);
	if(prof->nevents)
	{
		fprintf(fout, " for %d events = ", prof->nevents);
		fprint_time(fout, prof->elapsed / prof->nevents);
		fprintf(fout, " per event");
	}
	fprintf(fout, "\n");
	if(prof->sortable)sort_profiler(prof);
	for(i=0;i<prof->nsub;i++)
	{
		if(prof->sortable && i >= prof->sortable)break;
		freport_profiler_indent(fout, prof->sub[i], ind+1);
	}
}

void	report_profiler(struct profiler	*prof)
{
	if(!prof)return;
	freport_profiler_indent(stdout, prof, 0);
}

void	stop_profilers_recursively(struct profiler	*prof)
{
	int	i;
	if(prof->isrunning)stop_profiler(prof, 1);
	for(i=0;i<prof->nsub;i++)
		stop_profilers_recursively(prof->sub[i]);
}

struct profiler	*parse_profiler;
struct profiler	*preprocess_profiler;
struct profiler	*token_mapping_profiler;
struct profiler	*lexical_lookup_profiler;
struct profiler		*orth_profiler;
struct profiler	*lexical_parsing_profiler;
struct profiler	*lexical_filtering_profiler;
struct profiler	*ubertagging_profiler;
struct profiler	*chart_parsing_profiler;
struct profiler	  *packing_profiler;
struct profiler	*unpacking_profiler;
struct profiler	*post_generation_mapping_profiler;
struct profiler	*transfer_profiler;
struct profiler	*generation_profiler;
struct profiler	  *fixup_profiler;
struct profiler	  *semlook_profiler;
