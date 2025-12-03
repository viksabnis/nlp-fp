#define		_GNU_SOURCE
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>

#include	"unicode.h"
#include	"transfer.h"
#include	"freeze.h"
#include	"chart.h"
#include	"dag.h"
#include	"type.h"
#include	"hash.h"
#include	"conf.h"
#include	"profiler.h"

struct transfer_rule	**idiom_rules;
int						nidiom_rules;

char	*non_idiom_root = NULL;

int	study_idiom_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	//printf("loading idiom rule '%s'\n", name);
	//printf("	dg type '%s'\n", dg->xtype->name);
	struct transfer_rule	*tr = dg_to_transfer_rule(name, dg, output_override);
	if(!tr)return -1;
	idiom_rules = realloc(idiom_rules, sizeof(struct idiom_rule*)*(nidiom_rules+1));
	idiom_rules[nidiom_rules++] = tr;
	return 0;
}

int	is_idiom_ep(char	*ep)
{
	// normalized predicates: idioms end with _i and -i
	if(strlen(ep) < 2)return 0;
	char	*tail = ep + strlen(ep) - 2;
	if(!strcmp(tail, "_i"))return 1;
	if(!strcmp(tail, "-i"))return 1;
	// unnormalized predicates: idioms end with _i_rel and -i_rel
	if(strlen(ep) < 6)return 0;
	tail = ep + strlen(ep) - 6;
	if(!strcmp(tail, "_i_rel"))return 1;
	if(!strcmp(tail, "-i_rel"))return 1;
	if(tail>ep && !strcmp(tail-1, "_i_rel\""))return 1;
	if(tail>ep && !strcmp(tail-1, "-i_rel\""))return 1;
	return 0;
}

int	is_idiom_free(struct mrs	*m)
{
	int	i;
	for(i=0;i<m->nrels;i++)
		if(is_idiom_ep(m->rels[i].pred))return 0;
	return 1;
}

void	prevent_mrs_aliases(struct mrs	*m)
{
	clear_mrs();
	int i;
	for(i=0;i<m->vlist.nvars;i++)
		m->vlist.vars[i]->dg = NULL;
}

int	check_idioms(struct dg	*dg, struct mrs	*m)
{
	if(!non_idiom_root)
		return 1; // hack to make idiom analyses succeed if non_idiom_root is not declared

	extern int enable_dublin;
	if(enable_dublin)return 1;	// hack to skip idiom check when we are operating in "dublin" robust mode

	static struct profiler	*idiom_profiler = NULL;
	if(g_profiling)start_and_alloc_profiler(&idiom_profiler, "idiom check", unpacking_profiler, NULL);
	//printf("non_idiom_root = %s\n", non_idiom_root);
	static struct dg	*non_idiom_root_dg = NULL;
	if(!non_idiom_root_dg)
	{
		non_idiom_root_dg = find_instance(non_idiom_root);
		if(!non_idiom_root_dg)
		{
			fprintf(stderr, "runtime error: unable to find instance `%s'\n", non_idiom_root);
			exit(-1);
		}
	}
	int res = unify_dg_tmp(dg, non_idiom_root_dg, -1);
	forget_tmp();
	if(res == 0)goto idiomatic;	// no further checking necessary.

	if(!m)m = extract_mrs(dg);
	//printf("ready to transfer for idiom check\n");

	struct mrs	**results;
	extern struct profiler	**transfer_rule_profilers, **idiom_profilers;
	transfer_rule_profilers = idiom_profilers;
	struct mrs	*mc = external_to_internal_mrs(m);	// unnecessary in light of what follows?
	struct mrs	*reformat_mrs_for_transfer(struct mrs	*m);
	mc = reformat_mrs_for_transfer(mc);	// this essentially re-extracts 'mc' from its ->dg pointers, with no VPM
	int	n = transfer_mrs(nidiom_rules, idiom_rules, mc, &results, 0);
	idiom_profilers = transfer_rule_profilers;
	//printf("%d idiom rule transfer result[s] from %d idiom rules\n", n, nidiom_rules);

	// at this point, 'mc' and 'm' share ->dg pointers, but the MRS extraction machinery
	// is set up to associate those dgs with the 'mc' no-vpm 'struct mrs_var's.
	prevent_mrs_aliases(mc);

	int	i;
	for(i=0;i<n;i++)
	{
		//print_mrs(results[i]);
		if(is_idiom_free(results[i]))
		{
			//printf("idiom free.\n");
			goto idiomatic;
		}
	}
	if(g_profiling)stop_profiler(idiom_profiler, 1);
	return 0;
idiomatic:
	if(g_profiling)stop_profiler(idiom_profiler, 1);
	return 1;
}
