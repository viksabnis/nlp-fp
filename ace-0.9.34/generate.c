#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<sys/time.h>
#include	<signal.h>

#define	DISJUNCTIVE_GENERATION	0

#include	"dag.h"
#include "mrs.h"
#include "lexicon.h"
#include "chart.h"
#include "unpack.h"
#include	"conf.h"
#include	"transfer.h"
#include	"profiler.h"
#include	"timeout.h"

void	itsdb_report_gen(int readings, double	fixup_time);

extern int	disable_subsumption_test;
extern int	question, exhaustive, lui_mode, inhibit_pack, trace, debug_level, inhibit_results, do_itsdb, best_only;
extern int show_gen_chart;
extern char	*master_addr;

int	require_neps = 0, n_epsbv = 0, n_avsbv = 0;
unsigned long long	*can_be_ccont_ep_bv;

int			enable_index_accessibility_filtering = 0;
extern int show_realization_trees;
extern int show_realization_mrses;

void collect_vars(struct dg	*dg, unsigned long long	*bv)
{
	int	i;
	dg = p_dereference_dg(dg);
	struct dg	**arcs = DARCS(dg);
	static int instloc = -1;
	if(instloc ==-1)instloc = lookup_fname("INSTLOC");

	for(i=0;i<dg->narcs;i++)
	{
		if(dg->label[i] == instloc)
		{
			struct type	*t = arcs[i]->xtype;
			if(t->name[0]=='"')
			{
				int	tnum = t->tnum;
				assert(tnum < n_avsbv*64);
				bitvec_set(bv, tnum);
			}
			return;
		}
		else collect_vars(arcs[i], bv);
	}
}

void accessible_vars(struct edge	*e, unsigned long long	*bv)
{
	// look at SYNSEM.LKEYS
//	static int	save[3] = {-1,-1,-1};
//	struct dg	*lkeys = walk_dg(e->dg, save, "SYNSEM", "LKEYS", NULL);

//	printf("lkeys:\n");
//	print_dg(lkeys);
//	printf("\n");

	//assert(lkeys != NULL);
	//return collect_vars(lkeys);
	collect_vars(e->dg, bv);
}

struct mrs	*current_input_mrs;
struct mrs	*current_internal_input_mrs;

int	index_accessibility_filter_one_var(struct edge	*e, struct mrs_var	*v)
{
	return bitvec_test(e->inaccessible_vars_bv, v->vnum);
	//return e->inaccessible_vars & (((unsigned long long)1)<<v->vnum);
}

int index_accessibility_filter_one_ep(struct edge	*e, struct mrs_ep	*ep)
{
	int i;
	if(index_accessibility_filter_one_var(e, ep->lbl))return 1;
	for(i=0;i<ep->nargs;i++)
		if(index_accessibility_filter_one_var(e, ep->args[i].value))
		{
			//printf("%s %s inaccessible\n", ep->pred, ep->args[i].name);
			return 1;
		}
	return 0;
}

int	index_accessibility_filter(struct edge	*e)
{
	int	i;
	for(i=0;i<current_internal_input_mrs->nrels;i++)
		if(!bitvec_test(e->ep_span_bv, i))
			if(index_accessibility_filter_one_ep(e, current_internal_input_mrs->rels+i))
				return 1;
	return 0;
}

#if DISJUNCTIVE_GENERATION
// disjunctive generation test

int	nroot_epspans = 0;
unsigned long long	**root_epspans;

setup_disjunctive_generation_test()
{
	unsigned long long	*r1 = bitvec_slab_alloc(1);
	bitvec_clear_all(r1, 1);
	bitvec_set(r1, 0);	// the
	bitvec_set(r1, 1);	// dog
	bitvec_set(r1, 3);	// sleep
	unsigned long long	*r2 = bitvec_slab_alloc(1);
	bitvec_clear_all(r2, 1);
	bitvec_set(r2, 0);	// the
	bitvec_set(r2, 2);	// cat
	bitvec_set(r2, 3);	// sleep
	unsigned long long	*r3 = bitvec_slab_alloc(1);
	bitvec_clear_all(r3, 1);
	bitvec_set(r3, 0);	// the
	bitvec_set(r3, 1);	// dog
	bitvec_set(r3, 4);	// bark
	unsigned long long	*r4 = bitvec_slab_alloc(1);
	bitvec_clear_all(r4, 1);
	bitvec_set(r4, 0);	// the
	bitvec_set(r4, 2);	// cat
	bitvec_set(r4, 5);	// arrive

	nroot_epspans = 4;
	root_epspans = malloc(sizeof(void*)*nroot_epspans);
	root_epspans[0] = r1;
	root_epspans[1] = r2;
	root_epspans[2] = r3;
	root_epspans[3] = r4;
	enable_index_accessibility_filtering = 0;
}

int	ep_span_is_root(unsigned long long	*eps, int	neps)
{
	int	i;
	for(i=0;i<nroot_epspans;i++)
		if(bitvec_equal(root_epspans[i], eps, n_epsbv))
			return 1;
	return 0;
}

int	ep_span_subsumed_by_root(unsigned long long	*eps)
{
	int	i;
	for(i=0;i<nroot_epspans;i++)
		if(bitvec_subsume(root_epspans[i], eps, n_epsbv))
			return 1;
	return 0;
}
#else
int	ep_span_is_root(unsigned long long	*eps, int	neps)
{
	return (neps == require_neps)?1:0;
}
#endif

// chart

int	ep_spans_are_adjacent(unsigned long long	*e1, unsigned long long	*e2)
{
	if(bitvec_and(e1, e2, NULL, n_epsbv))
		return 0;
#if DISJUNCTIVE_GENERATION
	unsigned long long	tmp[n_epsbv];
	bitvec_or(e1, e2, tmp, n_epsbv);
	if(!ep_span_subsumed_by_root(tmp))return 0;
#endif
	return 1;
}

int	gen_process_edge(struct edge	*e)
{
	struct chart_cell	*c = cells;
	int	i, pack = 0;

	e->accessible_vars_bv = bitvec_slab_alloc(n_avsbv);
	bitvec_clear_all(e->accessible_vars_bv, n_avsbv);
	e->inaccessible_vars_bv = bitvec_slab_alloc(n_avsbv);
	bitvec_clear_all(e->inaccessible_vars_bv, n_avsbv);
	unsigned long long	*temp_bv = bitvec_slab_alloc(n_avsbv);
	bitvec_clear_all(temp_bv, n_avsbv);

	unsigned long long	*previously_accessible = temp_bv;					// use as scratch space
	unsigned long long	*previously_inaccessible = e->inaccessible_vars_bv;	// use as scratch space

	//printf("process #%d\n", e->id);
	if(e->daughters)
	{
		// genuine edge
		for(i=0;i<e->have;i++)
		{
			if(e->daughters[i]->frozen==1)
			{
				//printf("not processing edge #%d ; daughter #%d is frozen\n", e->id, e->daughters[i]->id);
				return 0;
			}
			bitvec_or(e->daughters[i]->accessible_vars_bv, previously_accessible, previously_accessible, n_avsbv);
			bitvec_or(e->daughters[i]->inaccessible_vars_bv, previously_inaccessible, previously_inaccessible, n_avsbv);
		}
	}
	else
	{
		// generalization edge
		// ... for now, the accessibility bitmaps are inherited from one of the edges that this generalizes over. it seems to me we should be requiring that two edges have identical accessibility bitmaps to let them pack -- but we don't seem to be requiring that yet. hmm.
	}

	if(e->have == e->need && enable_index_accessibility_filtering)
	{
		// compute the set of variables actually accessible on 'e'
		accessible_vars(e, e->accessible_vars_bv);
		/*void print_varset(char	*name, unsigned long long	*bv)
		{
			int	i;
			printf("%s	", name);
			for(i=0;i<current_internal_input_mrs->vlist.nvars;i++)
				if(bitvec_test(bv, i))
				{
					struct mrs_var	*v = current_internal_input_mrs->vlist.vars[i];
					printf(" %s%d", v->type, v->vnum);
				}
			printf("\n");
		}
		print_varset("prev inaccessible", previously_inaccessible);
		print_varset("prev   accessible", previously_accessible);
		print_varset("now    accessible", e->accessible_vars_bv);
		printf("EPs covered:  ");
		for(i=0;i<current_internal_input_mrs->nrels;i++)
			if(bitvec_test(e->ep_span_bv, i))
				printf(" [%d]=%s", i, current_internal_input_mrs->rels[i].pred);
		printf("\n");*/
		// inaccessible variables are ones that were once accessible but no longer are
		// newly inaccessible variables are ones that were accessible on a daughter but are not accessible on 'e'
		// variables that were inaccessible on a daughter are still inaccessible on 'e'
		// inaccessible = previously_inaccessible | (previously accessible & ~currently accessible)
		unsigned long long	*newly_inaccessible = temp_bv;
		bitvec_andnot(previously_accessible, e->accessible_vars_bv, newly_inaccessible, n_avsbv);
		bitvec_or(previously_inaccessible, newly_inaccessible, e->inaccessible_vars_bv, n_avsbv);
		if(index_accessibility_filter(e))
		{
			//printf("filtered edge #%d.\n", e->id);
			return 0;
		}
	}

	if(!inhibit_pack && e->have == e->need)
	{
		pack = pack_edge(e);
		if(pack==1)
			return 0;	// big savings! woohoo!
	}
	if(pack==0)add_edge_to_chart(e);

	// try to combine against any other edge with disjoint ep_span
	if(e->have == e->need)
	{
		// passive edge
		for(i=0;i<c->al_nedges;i++)
			if(ep_spans_are_adjacent(e->ep_span_bv, c->al_edges[i]->ep_span_bv))
				if(combine(c->al_edges[i], e) == -1)return -1;
		for(i=0;i<c->ar_nedges;i++)
			if(ep_spans_are_adjacent(e->ep_span_bv, c->ar_edges[i]->ep_span_bv))
				if(combine(c->ar_edges[i], e) == -1)return -1;
	}
	else
	{
		// active edge
		for(i=0;i<c->p_nedges;i++)
			if(ep_spans_are_adjacent(e->ep_span_bv, c->p_edges[i]->ep_span_bv))
				if(combine(e, c->p_edges[i]) == -1)return -1;
	}
	return 0;
}

float timer()
{
	float ret;
	static struct timeval tvstart = {0,0}, tv;
	if(!tvstart.tv_sec)gettimeofday(&tvstart, 0);
	gettimeofday(&tv, 0);
	ret = tv.tv_sec - tvstart.tv_sec + 0.000001 * (tv.tv_usec - tvstart.tv_usec);
	tvstart = tv;
	return ret;
}

struct realization
{
	char			*surface;
	struct hypothesis	*hyp;
	struct mrs		*mrs;
};
struct realization	*saved_realizations;
int			saved_nrealizations;

int	get_nth_realization(int	idx, char	**s, struct hypothesis	**h, struct mrs	**m)
{
	if(idx < 0 || idx >= saved_nrealizations)return -1;
	*s = saved_realizations[idx].surface;
	*h = saved_realizations[idx].hyp;
	*m = saved_realizations[idx].mrs;
	return 0;
}

// driver

int	generate(struct mrs	*mrs)
{
	extern struct edge *sentential;
	struct edge	*edge;
	char		*str;
	int			i, count = 0;

	if(g_profiling)
	{
		if(generation_profiler)stop_profilers_recursively(generation_profiler);
		start_and_alloc_profiler(&generation_profiler, "generation", NULL, NULL);
	}
	extern int tsdb_notes;
	if(tsdb_notes)tsdb_parse_note_start();

#if DISJUNCTIVE_GENERATION
	setup_disjunctive_generation_test();
#endif

	current_input_mrs = mrs;

	timer();
	reset_edges();
	clear_chart(1);

	cancel_task = 0;
	did_timeout = 0;
	signal(SIGALRM, alarm_handler);

	if(timeout_seconds > 0)
		alarm(timeout_seconds);

	struct mrs	*external_mrs = mrs;
	mrs = external_to_internal_mrs(mrs);

	if(debug_level)
	{
		printf("\n");
		printf("external MRS:\n");
		print_mrs(external_mrs); printf("\n");
		printf("internal MRS:\n");
		print_mrs(mrs); printf("\n");
	}

	//fprintf(stderr, "NOTE: input semantics had %d EPs and %d variables\n", mrs->nrels, mrs->vlist.nvars);

	// XXX now that we are doing skolemize_for_generation(),
	// and now that fixup() is undoing the following skolemization work,
	// it would probably make sense to just not do this work.
	// XXX ... we have to at least do the dagify() work here,
	// since some grammars have no fixup rules, and fixup_mrs() does not (re)dagify if there are no rules

	// set up the skolemization and specialization dags we'll need.
	struct dg	*skar[mrs->vlist.nvars];
	struct type_hierarchy	*th = default_type_hierarchy();
	for(i=0;i<mrs->vlist.nvars;i++)
	{
		struct dg			*skolem;
		skolem = atomic_dg(top_type);
		assert(i<th->nstrings);
		skolem->type = skolem->xtype = th->strings[i];
		skar[i] = skolem;
	}
	for(i=0;i<mrs->nhcons;i++)
	{
		//skar[mrs->hcons[i].hi->vnum] = skar[mrs->hcons[i].lo->vnum];
		struct dg	*hi = skar[mrs->hcons[i].hi->vnum];
		struct dg	*lo = skar[mrs->hcons[i].lo->vnum];
		hi->type = hi->xtype = lo->xtype;
	}
	for(i=0;i<mrs->vlist.nvars;i++)
	{
		int dagify_result = dagify_mrs_var(mrs->vlist.vars[i], skar[i]);
		if(dagify_result != 0)goto illformed;
		//printf("dag for %s: \n", mrs->vlist.vars[i]->name);
		//print_dg(mrs->vlist.vars[i]->dg);
		//printf("\n");
	}
	for(i=0;i<mrs->nrels;i++)
	{
		int dagify_result = dagify_mrs_ep(mrs->rels+i);
		if(dagify_result != 0)goto illformed;
	}
	if(debug_level)printf("mrs-to-dg %.4f\n", timer());

	if(g_profiling)start_and_alloc_profiler(&fixup_profiler, "fixup", generation_profiler, NULL);
	struct mrs	*fixed_up_mrs = fixup_mrs(mrs);
	double fixup_time = 0;
	if(g_profiling)
	{
		double	tfix = stop_profiler(fixup_profiler, 1);
		/*static FILE	*f = NULL;
		if(!f)f = fopen("/tmp/fixup-timing.txt", "w");
		fprintf(f, "%d %d %f\n", mrs->nrels, fixed_up_mrs->nrels, tfix);
		fflush(f);*/
		fixup_time = tfix;
	}
	if(debug_level)
	{
		printf("fixup result:\n");
		print_mrs(fixed_up_mrs);
	}
	skolemize_for_generation(fixed_up_mrs);
	current_internal_input_mrs = fixed_up_mrs;	// used by index accessibility filter

	require_neps = fixed_up_mrs->nrels;
	n_epsbv = bitvec_n(fixed_up_mrs->nrels);
	n_avsbv = bitvec_n(fixed_up_mrs->vlist.nvars);

	can_be_ccont_ep_bv = bitvec_slab_alloc(n_epsbv);
	bitvec_clear_all(can_be_ccont_ep_bv, n_epsbv);

	// set up some lexemes and rules for the generator to play with
	// XXX for testing fixup speed, don't look anything up into the chart
	if(g_profiling)start_and_alloc_profiler(&semlook_profiler, "semantic lookup", generation_profiler, NULL);
	semantic_lookup(fixed_up_mrs);
	if(g_profiling)stop_profiler(semlook_profiler, 1);

	if(debug_level)printf("semlook %.4f\n", timer());

	if(!inhibit_pack)enable_packing(2);

	int	npassive_edges = 0;
	sentential = 0;
	while( !cancel_task && (edge = next_agenda(0)) )
	{
		if(edge->have == edge->need)npassive_edges++;
		//printf("... process %p = #%d  ; %d EPs\n", edge, edge->id, edge->neps);
		if(gen_process_edge(edge)){break;}
	}
	if(debug_level)printf("packed %.4f\n", timer());

	enable_packing(0);

	/*struct mrs	*hax_ref = external_to_internal_mrs(mrs);
	if(trace)
	{
		printf("internal version of MRS:\n");
		print_mrs(hax_ref);
		printf("\n");
	}*/

	struct realization	*realizations=NULL;
	int	nrealizations=0, arealizations = 0;

#define SEMI_SIDE_SUBSUMPTION_TEST
//#define POST_FIXUP_SUBSUMPTION_TEST

#ifndef	SEMI_SIDE_SUBSUMPTION_TEST
	// map back and forth, since that will happen to the results...
	current_internal_input_mrs = external_to_internal_mrs(internal_to_external_mrs(current_internal_input_mrs));
#endif

#ifdef	POST_FIXUP_SUBSUMPTION_TEST
	// map back and forth, since that will happen to the results...
	current_input_mrs = internal_to_external_mrs(current_internal_input_mrs);
#endif

	int show_result(struct hypothesis	*hyp, struct mrs	*mrs_res, double	prob)
	{
		// LKB compares *internal* MRSes, by going through the VPM *twice* "to get defaults".
		// see comment in lkb/mrs/generate.lisp near line 765.
		// Note that "x subsumes y" does not technically imply "vpm(x) subsumes vpm(y)"
		// (for either forward or backwards vpm), *but* for sane vpm's it *should*.
		// VPM is a lossy map.
		// What is really false is that "vpm(x) subsumes vpm(y)" implies "x subsumes y".
		// So, testing whether (input) subsumes vpm(result) *should* be
		// *stricter* than testing whether (ivpm(input) subsumes ivpm(vpm(result))).
		// ACE is going to try doing that stricter test and see what happens...
		// Note that other processors may not have this option, due to not loading the SEMI signature.
		//if(!mrs_subsumes(mrs, mrs_res))
		//if(!mrs_subsumes(hax_ref, hax_res))
#ifdef	SEMI_SIDE_SUBSUMPTION_TEST
		extern struct type_hierarchy	*main_th, *semi_th;
		set_default_type_hierarchy(semi_th);
		int	sst_result = (disable_subsumption_test==0) && !mrs_subsumes(current_input_mrs, mrs_res);
		set_default_type_hierarchy(main_th);
		if(sst_result)	// totally SEMI-side comparison
#else
		struct mrs	*hax_res = external_to_internal_mrs(mrs_res);
		if((disable_subsumption_test==0) && !mrs_subsumes(current_internal_input_mrs, hax_res))	// grammar-side comparison
#endif
		{
			if(trace)
			{
				printf("NICE TRY! `%s' has incompatible semantics:\n", hyp->string);
#ifdef	SEMI_SIDE_SUBSUMPTION_TEST
				print_mrs(mrs_res); printf("\n");
#else
				print_mrs(hax_res); printf("\n");
#endif
			}
			//print_mrs(mrs_res); printf("\n");
			free_mrs(mrs_res);
			return 0;
		}
		if((nrealizations+1) > arealizations)
		{
			arealizations = (arealizations+2)*2;
			realizations = realloc(realizations, sizeof(struct realization)*arealizations);
		}
		struct realization	*R = &realizations[nrealizations++];
		R->surface = hyp->string;
		R->hyp = hyp;
		R->mrs = mrs_res;
		if(debug_level)printf("probability = %f:\n", prob);
		if(trace>0)printf("edge #%d has a correct unpacking\n", hyp->edge->id);
		if(trace>1){print_dg(hyp->dg); printf("\n");}
		if(master_addr)printf("SURFACE = %s\n", hyp->string);
		else if(!inhibit_results && !do_itsdb)printf("%s\n", hyp->string);
		if(do_itsdb)itsdb_report_genresult(hyp, mrs_res, count);
		count++;
		//if(trace>0){ print_mrs(mrs_res); printf("\n"); }
		if(trace>0)
		{
			//print_mrs(hax_res);
			print_mrs(mrs_res);
			printf("\n");
			char	*dstr = hypothesis_to_dstring(hyp);
			puts(dstr);
		}
		if(show_realization_trees && !do_itsdb)
		{
			char	*dstr = hypothesis_to_dstring(hyp);
			printf("DTREE = %s\n", dstr);
		}
		if(show_realization_mrses && !do_itsdb)
		{
			printf("MRS = ");
			print_mrs(mrs_res);
		}
		free_mrs(mrs_res);
		if(master_addr)printf("END RESULT\n");
		return 1;
	}
	if(do_itsdb)itsdb_start_results();
	if(master_addr)printf("SENT: mrs\n");
	if(g_profiling)start_and_alloc_profiler(&unpacking_profiler, "unpacking", generation_profiler, NULL);
	iterate_cell_root_hypotheses(cells, show_result, best_only);
	if(g_profiling)stop_profiler(unpacking_profiler, 1);
	if(do_itsdb)itsdb_end_results();
	if(do_itsdb)itsdb_report_gen(count, fixup_time);
	if(debug_level)printf("unpacked %.4f\n", timer());

	if(lui_mode)
	{
		if(nrealizations == 0)lui_text("No realization results.");
		else
		{
			int i;
			lui_begin_gen_results(nrealizations);
			for(i=0;i<nrealizations;i++)
				lui_gen_result(i, realizations[i].surface);
			lui_end_gen_results();
			saved_realizations = realizations;
			saved_nrealizations = nrealizations;
		}
		if(show_gen_chart)
			lui_gen_chart(fixed_up_mrs);
	}

	if(0)
	{
		illformed:
		itsdb_error("illformed input MRS");
		fprintf(stderr, "WARNING: illformed input MRS\n");
	}

	if(tsdb_notes)tsdb_parse_note_end();
	fflush(stdout);

	fprintf(stderr, "NOTE: %d passive, %d active edges in final generation chart; built %d passives total. [%d results]\n",
		cells->p_nedges, cells->al_nedges + cells->ar_nedges, npassive_edges, count);
	printf("\n");
	fflush(stdout);

	/*if(lui_chart)
	{
		char	*words[] = {"generate"};
		output_lui_chart(words);
	}*/
	if(g_profiling)stop_profiler(generation_profiler, 1);

	return count;
}
