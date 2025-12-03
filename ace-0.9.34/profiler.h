#ifndef	PROFILER_H
#define	PROFILER_H

#include	<stdio.h>

struct profiler
{
	int				nsub;
	struct profiler	**sub;

	int	ncalls, nevents, isrunning;
	struct timeval	started;
	double	elapsed;
	char	*name;
	int	sortable;
};

extern struct profiler *parse_profiler;
extern struct profiler	*preprocess_profiler;
extern struct profiler	*token_mapping_profiler;
extern struct profiler	*lexical_lookup_profiler;
extern struct profiler		*orth_profiler;
extern struct profiler	*lexical_parsing_profiler;
extern struct profiler	*lexical_filtering_profiler;
extern struct profiler	*ubertagging_profiler;
extern struct profiler	*chart_parsing_profiler;
extern struct profiler	  *packing_profiler;
extern struct profiler	*unpacking_profiler;
extern struct profiler	*post_generation_mapping_profiler;
extern struct profiler	*transfer_profiler;
extern struct profiler	*generation_profiler;
extern struct profiler		*fixup_profiler;
extern struct profiler		*semlook_profiler;
extern int g_profiling;

extern struct profiler	*mrs_profiler;

void	start_profiler(struct profiler	*prof);
void	start_and_alloc_profiler(struct profiler	**prof, char	*name, struct profiler	*parent, struct profiler	*tostop);
double	stop_profiler(struct profiler	*prof, int	nevents);
void	stop_profilers_recursively(struct profiler	*prof);

struct profiler	*new_profiler(char	*name, struct profiler	*parent);
void	freport_profiler_indent(FILE	*fout, struct profiler	*prof, int	ind);
void	report_profiler(struct profiler	*prof);

#endif
