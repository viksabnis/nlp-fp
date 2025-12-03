#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<signal.h>
#include	<unistd.h>
#include	<sys/time.h>
#include	<time.h>
#include	<assert.h>

#include	"conf.h"
#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"freeze.h"
#include	"morpho.h"

#include	"timer.h"

//#define	RULE_STATS

//int	nofragments = 1;
int	nofragments = 0;

int	enable_generalize_edge_top_types = 0;

// this is a bit dangerous -- subgraph sharing can mean that this edits parts of other edges,
// including lexical edges, which causes bugs in unpacking.
// if we decide in the future to try the SYNSEM and MODIFD generalization ideas again,
// go back to unpack.c and turn unspecialization on again (with token information).
static inline generalize_certain_paths(struct dg	*d, int	hyper)
{
	static struct type	*synsemtype = NULL, *modifdtype = NULL;
	static struct type *signtype = 0;
	if(!synsemtype)synsemtype = lookup_type("synsem");
	if(!modifdtype)modifdtype = lookup_type("xmod_min");
	if(!signtype)signtype = lookup_type("sign");

	static int	synsem_f = -1, modifd_f = -1;
	if(synsem_f == -1)synsem_f = lookup_fname("SYNSEM");
	if(modifd_f == -1)modifd_f = lookup_fname("MODIFD");

	struct dg	*ss = dg_hop(d, synsem_f);
	struct dg	*m = ss?dg_hop(ss, modifd_f):NULL;

	d->type = signtype;
	if(!hyper)d->xtype = signtype;
	/*if(ss)
	{
		ss->type = synsemtype;
		if(!hyper)ss->xtype = synsemtype;
	}*/
	/*if(m)
	{
		m->type = modifdtype;
		if(!hyper)m->xtype = modifdtype;
	}*/
}

callable_generalize_certain_paths(struct dg	*d) { if(enable_generalize_edge_top_types)generalize_certain_paths(d,0); }

int	inhibit_results = 0;
extern int inhibit_pack;

int			chart_size;
struct chart_cell	*cells;
int	total_edges, real_edges, passive_edges, used_edges, pused_edges;
unsigned long long total_passives;

extern int	debug_level;
extern int	question, exhaustive;

int		edge_id;

extern int	*nused, *nhactive, *nactive, *npassive, *nrecomb, *natries, *nptries, used_total, pused_total;

char	*show_orth_leaves(struct edge	*e);
static void	hyperactive_excursion(struct edge	*e);
int	combine(struct edge	*a, struct edge	*b);

unsigned long long unify_attempts_total, unify_attempts_pass_rf, unify_attempts_pass_qc, unify_attempts_success, unify_attempts_bad_orth;
#ifdef	CLOCKCOUNT
unsigned long long unify_clock, unify_count;
#endif

//int	*rtried;

struct edge	*sentential = 0;

extern int max_chart_megabytes;
//#define	MAX_CHUNKS	60000	// when to give up on a parse
//#define	MAX_CHUNKS	6000	// when to give up on a parse
//#define	MAX_CHUNKS	2560	// when to give up on a parse
//#define	MAX_CHUNKS	1200		// when to give up on a parse
//#define	MAX_CHUNKS	800		// when to give up on a parse
//#define	MAX_CHUNKS	71	// when to give up on a parse

//#define	EXCURSION

extern unsigned int	generation;

void	reset_edges()
{
	edge_id = 1;
}

void	clear_chart(int	size)
{
	int	i;

	// guard against generation overflow;
	// reset the grammar if we are above 4-billion generations
	if(generation > MAX_GEN_RESET)//4000000000UL)
		reload_frozen_grammar();

	if(cells)
	{
		for(i=0;i<chart_size*chart_size;i++)
		{
			if(cells[i].p_nedges)
				free(cells[i].p_edges);
			if(cells[i].al_nedges)
				free(cells[i].al_edges);
			if(cells[i].ar_nedges)
				free(cells[i].ar_edges);
		}
		free(cells);
	}
	clear_agenda();

	//clear_slab();

	passive_edges = real_edges = total_edges = used_edges = pused_edges = 0;
	chart_size = size;
	cells = calloc(sizeof(struct chart_cell) , chart_size*chart_size);
	sentential = 0;
}

int	next_eid() { return edge_id++; }

void	add_edge_to_chart_cell(struct chart_cell	*cell, struct edge	*edge)
{
	//printf(" -- edge type %s, %d-%d\n", edge->rule?edge->rule->name:"lex", edge->from, edge->to);
	if(edge->have==edge->need)
	{
		cell->p_nedges++;
		cell->p_edges = realloc(cell->p_edges, sizeof(struct edge*) * cell->p_nedges);
		cell->p_edges[cell->p_nedges-1] = edge;
		passive_edges++;
	}
	else if(edge->rtl)
	{
		cell->ar_nedges++;
		cell->ar_edges = realloc(cell->ar_edges, sizeof(struct edge*) * cell->ar_nedges);
		cell->ar_edges[cell->ar_nedges-1] = edge;
	}
	else
	{
		cell->al_nedges++;
		cell->al_edges = realloc(cell->al_edges, sizeof(struct edge*) * cell->al_nedges);
		cell->al_edges[cell->al_nedges-1] = edge;
	}

	total_edges++;
	if(edge->have != 0)real_edges++;
}

void	add_edge_to_chart(struct edge	*edge)
{
	int	k = edge->from*chart_size + edge->to;

	add_edge_to_chart_cell(cells+k, edge);
}

int	trace = 0, gen_qc = 0;

double base_unify_time = 0, base_finalize_time = 0;
long long nbase_unify = 0, nbase_finalize = 0;

void	setup_lexrule_edge(struct edge	*e)
{
	struct edge	*b = e->daughters[0];
	e->lex = b->lex;
	if(g_mode == PARSING)
	{
		if(!e->rule->orth)
		{
			e->north_routes = b->north_routes;
			e->orth_routes = b->orth_routes;
		}
		else
		{
			int i;
			if(b->north_routes==-1)
			{
				e->north_routes = -1;
				e->orth_routes = 0;
			}
			else
			{
				e->north_routes = 0;
				e->orth_routes = slab_alloc(sizeof(struct orth_route)*b->north_routes);
				for(i=0;i<b->north_routes;i++)
				{
					struct orth_route *r = b->orth_routes+i;
					if(r->len && r->rules[0]==e->rule->rnum)
					{
						e->north_routes++;
						e->orth_routes[e->north_routes-1].len = r->len-1;
						e->orth_routes[e->north_routes-1].rules = slab_alloc(sizeof(int)*(r->len-1));
						memcpy(e->orth_routes[e->north_routes-1].rules, r->rules+1, sizeof(int)*(r->len-1));
					}
				}
			}
			//printf("realloc %d routes down to %d\n", b->north_routes, e->north_routes);
			//e->orth_routes = slab_realloc(e->orth_routes, sizeof(struct orth_route)*b->north_routes, sizeof(struct orth_route)*e->north_routes);
		}
	}
	else // (g_mode == GENERATING)
	{
		e->north_routes = 0;
		e->orth_routes = 0;
	}
}

int	build_edge(struct edge	*a, struct edge	*b, int	arg, struct dg	*dg, struct edge	**Eout, int force_noha)
{
	struct edge	*e;
	struct dg	*u;
	struct qc	*qc, *hqc;
	int		nhave, nneed, hyperactive = 0, from, to, spanning = 0;
	extern int	__qc_use_heap;
#ifdef	TIM
	struct timeval	tv1, tv2;
#endif

	if(Eout)*Eout = NULL;

	if(a->rtl)
	{
		from = b->from;
		to = a->to;
	}
	else
	{
		from = a->from;
		to = b->to;
	}
	spanning = (from==0) && (to==chart_size-1);

	nhave = a->have+1;
	nneed = a->need;
	if(nhave == nneed)
	{
		// building passive
		if(a->dg && b->dg && !spanning && !force_noha && 0)
		{
			// hyperpassive
			hyperactive = 1;
			__qc_use_heap = 1;
			if(enable_generalize_edge_top_types)
				generalize_certain_paths(dg, 1);
			hqc = extract_qc_arg(dg, -1);
			__qc_use_heap = 0;
			forget_tmp();
			qc = copy_qc(hqc);
			free(hqc);
			u = 0;
			//printf("built hyperpassive on #%d+#%d\n", a->id, b->id);
		}
		else
		{
			// regular passive
#ifdef	TIM
			gettimeofday(&tv1, 0);
#endif
//static int	pft = -1;
//if(pft==-1)pft = new_timer("passive copy");
//start_timer(pft);
			if(g_mode == GENERATING)
			{
				// in principal, the same phrase could appear multiple times in
				// a realization.
				// I believe this should only happen when the phrase is semantically vacuous.
				// XXX Is there a reason not to allow subgraph sharing
				// when none of the immediate daughters is semantically vacuous?

				//u = finalize_tmp_noss(dg, 1);

				int cant_share = 0;
				if(b->neps == 0)cant_share = 1;
				int k;
				for(k=0;k<a->have;k++)
					if(a->daughters[k]->neps == 0)cant_share = 1;
				if(cant_share)
					u = finalize_tmp_noss(dg, 1);
				else u = finalize_tmp(dg, 1);
			}
			else u = finalize_tmp(dg, 1);
			//u = copy_dg(u);
//stop_timer(pft, 1);
#ifdef	TIM
			gettimeofday(&tv2, 0);
			base_finalize_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
			nbase_finalize++;
#endif
			if(!u)return -1;	// cycles might happen, check for them.
			if(enable_generalize_edge_top_types)
				generalize_certain_paths(u, 0);
			qc = extract_qc_arg(u, -1);
		}
		e = slab_alloc(sizeof(struct edge));
		bzero(e, sizeof(*e));
		e->qc = qc;
		e->dg = u;
		e->ha_par = a->dg;
		e->ha_dg = b->dg;
		e->ha_arg = arg;
	}
	else
	{
		// building active
		//a->rule->hyper = 1;	// XXX test; we've been parsing nonhyperactively
		if(a->rule->hyper && !force_noha)
		{
			// hyperactive
			//if(check_cycles(dg))return -1;
			hyperactive = 1;

			__qc_use_heap = 1;
			hqc = extract_qc_arg(dg, a->rtl?(nneed-nhave-1):nhave);
			__qc_use_heap = 0;
#ifdef	EXCURSION
			// with hyperactive excursion, we can't free the extra space later since the QC is above us on the slab
			// and we can't free it now since we need it after building the edge! :(
#else
			forget_tmp();
#endif
			qc = copy_qc(hqc);
			free(hqc);

			u = 0;
#ifdef	RULE_STATS
			nhactive[a->rule->rnum]++;
#endif
		}
		else
		{
			// standard active
#ifdef	TIM
			gettimeofday(&tv1, 0);
#endif
//static int	aft = -1;
//if(aft==-1)aft = new_timer("active copy");
//start_timer(aft);
			/*if(g_mode == GENERATING)
			{
				u = finalize_tmp_noss(dg, 0);
			}
			else */u = finalize_tmp(dg, 0);
//stop_timer(aft, 1);
#ifdef	TIM
			gettimeofday(&tv2, 0);
			base_finalize_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
			nbase_finalize++;
#endif
			if(!u)return -1;	// cycles might happen, check for them.
			qc = extract_qc_arg(u, a->rtl?(nneed-nhave-1):nhave);
		}
		e = slab_alloc(sizeof(struct edge));
		bzero(e, sizeof(*e));
		e->dg = u;
		e->ha_par = dg;
		e->ha_dg = b->dg;
		e->ha_arg = arg;
		e->qc = qc;
		//printf("active qc %p (copy of %p)\n", e->qc, qc);
	}
	//e->prio = a->prio+1;
	//if(e->prio>20)e->prio = 20;
	e->prio = a->prio;
	if(nneed==nhave)
	{
		e->prio = 0;
		//e->prio=20;
		//e->prio = (e->to-e->from - 1)/2;
		//if(e->prio>10)e->prio = 10;
	}
	e->need = nneed;
	e->have = nhave;
	e->rule = a->rule;
	e->built_on = 0;
	e->frozen = 0;
	b->built_on = 1;
	//printf("new edge qc %p\n", e->qc);

	if(!a->have && !a->used){a->used = 1;used_edges++;}
	if(!b->used){b->used=1;pused_edges++;}
	if(b->lex && a->rule->orth)
	{
		//printf("promoted lexeme %s to word %s via rule %s\n", b->dg->xtype->name, u->xtype->name, a->rule->name);
	}
	e->id = next_eid();
	//fprintf(stderr, "build #%d %s on #%d\n", e->id, e->rule->name, b->id);
	e->daughters = slab_alloc(sizeof(struct edge*) * e->have);
	e->rtl = a->rtl;
	e->used = 0;
	if(e->rtl)
	{
		e->from = b->from;
		e->to = a->to;
		memcpy(e->daughters+1, a->daughters, sizeof(struct edge*) * a->have);
		e->daughters[0] = b;
	}
	else
	{
		e->from = a->from;
		e->to = b->to;
		memcpy(e->daughters, a->daughters, sizeof(struct edge*) * a->have);
		e->daughters[arg] = b;
	}

	if(e->rule->lexical)
		setup_lexrule_edge(e);
	else
	{
		e->lex = 0;
		e->north_routes = 0;
		e->orth_routes = 0;
	}

	if(g_mode == GENERATING)
	{
		e->neps = a->neps + b->neps;
		e->ep_span_bv = bitvec_slab_alloc(n_epsbv);
		bitvec_or(a->ep_span_bv, b->ep_span_bv, e->ep_span_bv, n_epsbv);
	}
	e->npack=0;
	e->pack=0;

	extern int enable_dublin;
	if(g_mode==PARSING && enable_dublin && e->have<e->need)
	{
		// mark active edges as 'dublin' (neps=-1) if they might spawn a dublin passive edge
		if((a->neps==-1 || a->have==0) && b->neps==-1)
		{
			//printf("possibly building an active edge that could spawn dublin edge...\n");
			if(dublin_tree_contains(e->rule->name, -1,-1, b->rule?b->rule->name:b->lex->word, b->from, b->to))
			{
				if(trace>1)printf("active edge #%d has the potential to spawn a redundant dublin edge\n", e->id);
				e->neps=-1;
			}
			//else printf("but %s[%d-%d] over %s[%d-%d] is not in dublin tree\n",e->rule->name, e->from, e->to, b->rule?b->rule->name:b->lex->word, b->from, b->to);
		}
	}

	if(trace)
	{
		if(g_mode == GENERATING)
		{
			printf("generated #%d %d/%d from #%d, #%d for %d EPs with rule %s: ",
				e->id, e->have, e->need, a->id, b->id, e->neps, e->rule->name);
			printf("%s\n", show_orth_leaves(e));
		}
		else // (g_mode == PARSING)
		{
			printf("generated #%d %d/%d from #%d, #%d for [%d-%d] with rule %s: ",
				e->id, e->have, e->need, a->id, b->id, e->from, e->to, e->rule->name);
			printf("%s\n", show_orth_leaves(e));
		}
		if(e->have==e->need && trace>1){print_dg(u); printf("\n\n");}
	}
	if(e->need==e->have)
	{
		//printf("\n generated %d/%d for [%d-%d] %s with rule %s\n", e->have, e->need, e->from, e->to, u->xtype->name, e->rule->name);
		//print_dg(u);
		//printf("\n");
#ifdef	RULE_STATS
		npassive[e->rule->rnum]++;
#endif

		if(!exhaustive &&
			((g_mode == GENERATING && e->neps == require_neps) ||
			(g_mode == PARSING && e->from==0 && e->to==chart_size-1)) &&
			is_root(e->dg))
		{
			fprintf(stderr, "sentential -- stopping\n");
			e->used = 1;pused_edges++;
			add_edge_to_chart(e);
			sentential = e;	// stop the parser
			return -2;
		}
	}
#ifdef	RULE_STATS
	else nactive[e->rule->rnum]++;
#endif

	e->hex = 0;
#ifdef	EXCURSION
	//if(hyperactive && e->have==e->need)	// this looks wrong -- go on hyperactive excursions with passive edges???
	if(hyperactive)
	{
		if(e->have!=e->need)
		{
			e->dg = dg;
			hyperactive_excursion(e);
			e->dg = 0;
		}
		generation++;
		// why we can't forget_tmp():
		// ``e'', ``e->daughters'' and ``e->qc'' are on the slab,
		// perhaps along with some other stuff.
		//forget_tmp();
	}
#endif

	*Eout = e;
	return 0;
}

#ifdef	EXCURSION
// try to find another passive edge to combine with while 'e' is still valid
static void	hyperactive_excursion(struct edge	*e)
{
	int					i, j, remain, arg;
	struct chart_cell	*c;
	struct edge			*b;
	extern int highest; // XXX snooping on agenda.c

	if(g_mode == GENERATING)return;	// XXX why do we need to do this?

	if(e->prio < highest)return;

	// active edge
	remain = e->need - e->have;
	if(e->rtl)
	{
		arg = e->need - e->have - 1;
		for(i=0;i<=e->from;i++)
		{
			c = cells + e->from + i*chart_size;
			for(j=0;j<c->p_nedges;j++)
				if(c->p_edges[j]->from - (remain-1) >= 0)
				{
					b = c->p_edges[j];
					if(!b->dg)continue;	// can't play with hyperpassive edges
					if(b->rule && !check_rf(e->rule, b->rule, arg))continue;	// rule filter rejected this combination
					if(!gen_qc && quickcheck(e->qc, b->qc))continue;			// quickcheck rejected this combination
					//fprintf(stderr, "HEX %d+%d\n", e->id, b->id);
					if(combine(e, b) == 1)
					{
						//fprintf(stderr, " +\n");
					}
					e->hex = b;
					return;
				}
		}
	}
	else
	{
		arg = e->have;
		for(i=e->to;i<chart_size;i++)
		{
			c = cells + i + e->to*chart_size;
			for(j=0;j<c->p_nedges;j++)
				if(c->p_edges[j]->to + (remain-1) < chart_size)
				{
					b = c->p_edges[j];
					if(!b->dg)continue;	// can't play with hyperpassive edges
					if(b->rule && !check_rf(e->rule, b->rule, arg))continue;	// rule filter rejected this combination
					if(!gen_qc && quickcheck(e->qc, b->qc))continue;			// quickcheck rejected this combination
					//fprintf(stderr, "HEX %d+%d\n", e->id, b->id);
					if(combine(e, b) == 1)
					{
						//fprintf(stderr, " +\n");
					}
					e->hex = b;
					return;
				}
		}
	}
}
#endif

hyperfailure(struct edge	*e)
{
	printf("hyper reconstruction failed! edge #%d\n", e->id);
	printf("rule: %s\n", e->rule->name);
	printf("parent dag:\n");print_dg(e->ha_par);printf("\n");
	printf("argument dag:\n");print_dg(e->ha_dg);printf("\n");
	unify_backtrace();
	print_current_sentence();
	exit(-1);
}

int	recall_hyper(struct edge	*b)
{
#ifdef	TIM
	struct timeval	tv1, tv2;
	gettimeofday(&tv1, 0);
#endif

#ifdef	RULE_STATS
	nrecomb[b->rule->rnum]++;
#endif
	//printf("hyper reconstruct #%d from %p[%d] <- %p\n", b->id, b->ha_dg, b->ha_arg, b->ha_par);
	if(unify_dg_tmp(b->ha_dg, b->ha_par, b->ha_arg))
		hyperfailure(b);
	//if(g_mode == GENERATING)// && b->have==b->need)
	if(g_mode == GENERATING && b->have==b->need)
	{
		b->dg = finalize_tmp_noss(b->ha_par, (b->have==b->need)?1:0);
	}
	else b->dg = finalize_tmp(b->ha_par, (b->have==b->need)?1:0);
#ifdef	TIM
	gettimeofday(&tv2, 0);
	base_unify_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
	nbase_unify++;
#endif
	if(!b->dg)
	{
		// latent cycle detection
		//fprintf(stderr, "NOTE: hyperpassive: latent cycle\n");
		b->have = -1;
		return -1;
	}
	return 0;
}

int	edge_is_ready_for_syntax(struct edge	*b)
{
	int i;
	for(i=0;i<b->north_routes;i++)
		if(b->orth_routes[i].len == 0)break;
	if(i==b->north_routes)return 0;
	return 1;
}

int	check_lexical_rule_constraints(struct rule	*rule, struct edge	*b)
{
	if(rule->lexical)
	{
		if(!b->lex)return -1;	// lexical rules may apply only to lexical edges
		// if 'a' is orthographemic, make sure it's the right one
		if(rule->orth && g_mode == PARSING && b->north_routes != -1)
		{
			// look at each route 'b' allows and see if this is the first rule on it
			int i;
			for(i=0;i<b->north_routes;i++)
			{
				struct orth_route *r = b->orth_routes+i;
				if(r->len && r->rules[0] == rule->rnum)
					break;
			}
			if(i==b->north_routes)
			{
				//printf(" #%d rejects rule %s as a next orthographemic\n", b->id, rule->name);
				return -1;
			}
			//printf(" #%d admits rule %s as a next orthographemic\n", b->id, rule->name);
		}
		else if(!rule->orth && g_mode == PARSING && b->north_routes != -1)
		{
			extern char	**rf_tc;
			// look at each route 'b' allows and see if this fits in the first rule on it
			int i;
			for(i=0;i<b->north_routes;i++)
			{
				struct orth_route *r = b->orth_routes+i;
				if(!r->len || rf_tc[r->rules[0]][rule->rnum])
					break;
			}
			if(i==b->north_routes)
			{
				//printf(" #%d rejects rule %s as a next nonorthographemic\n", b->id, rule->name);
				return -1;
			}
		}
	}
	else if(b->lex && g_mode == PARSING)
	{
		// 'b' is lexical but 'a' is a syntax rule; see if 'b' might be done with its orthographemics
		if(! edge_is_ready_for_syntax(b))return -1;
	}
	return 0;
}

int	filter(struct edge	*a, struct edge	*b)
{
	int	i, arg, gmode = g_mode;

	if(a->hex == b)return 0;	// already did this
	if(a->have==-1)return 0;	// ghosted hyperactive edge -- got kicked out of the chart for a latent cycle
	if(b->have==-1)return 0;	// ghosted hyperpassive edge -- got kicked out of the chart for a latent cycle

//	if(b->lex && b->north_routes==-1 && a->need==1)return 0;	// unknown-word edges may not undergo unaries

	//printf("FR: [%d-%d] + [%d-%d]?\n", a->from, a->to, b->from, b->to);
	//printf("    <%d/%d> + <%d/%d>\n", a->have, a->need, b->have, b->need);
	//printf("    %s   + %s\n", a->dg->xtype->name, b->dg->xtype->name);

	if(trace>1)printf("[#%d [lex %d orth %p] + #%d [lex %p]] rule %s?\n",
		a->id, a->rule->lexical, a->rule->orth, b->id, b->lex, a->rule->name);

	// see if a or b is lexical and incompatible
	if(check_lexical_rule_constraints(a->rule, b))return 0;

	if(a->rtl)arg = a->need - a->have - 1;
	else arg = a->have;

	int rf = 0;
	if((a->have==0||a->daughters||a->lex) && (b->daughters||b->lex))
		rf = (b->rule && !check_rf(a->rule, b->rule, arg));
	//int rf = 0;//(b->rule && !check_rf(a->rule, b->rule, arg));

	// don't allow span-only rules to finish on a non-span
	if(nofragments && a->rule->frag_only)return 0;

	if(gmode == PARSING)
	{
		int	rfrom = a->from, rto = a->to;
		if(b->from<rfrom)rfrom = b->from;
		if(b->to>rto)rto = b->to;
		if(a->have == a->need-1)
		{
			// building a passive edge
			if(rfrom==0 && rto==chart_size-1)
			{
				// spanning edge
				extern char	*rule_root_utc;
				if(!rule_root_utc[a->rule->rnum])
				{
					// yes, this fires a lot!
					if(trace>1)printf("not using rule '%s' in spanning cell\n", a->rule->name);
					return 0;
				}
			}
			else
			{
				// non-spanning edge
				if(a->rule->span_only) return 0;
			}
			if((a->neps==-1 || a->have==0) && b->neps==-1)
			{
				// building a passive edge that might come from the dublin tree...
				//printf("possibly building a passive that is in dublin...\n");
				if(dublin_tree_contains(a->rule->name, rfrom, rto, b->rule?b->rule->name:b->lex->word, b->from, b->to))
				{
					if(trace>1)
						printf("not using rule '%s'[%d-%d] since dublin already has it\n", a->rule->name, rfrom, rto);
					return 0;	// this passive edge already exists in the dublin tree
				}
				//else printf("but it wasn't in dublin\n");
			}
		}
		else
		{
			// building an active edge
			// these tests are done in parse_process_edge()...
			//if(a->rtl && rfrom == 0)return 0;	// would have no room to grow left
			//if(!a->rtl && rto == chart_size - 1)return 0;	// would have no room to grow right
		}
	}

	/*if(gmode == GENERATING && a->have == a->need-1)
	{
		// contemplating building a passive edge
		if(a->rule->span_only)
		{
			// if there are unrealized EPs that cannot be supplied by C-CONT rules,
			// then we can't be at the top of the final tree (must add more lexemes)
			// so we shouldn't allow span_only rules to fire.
			// purely_lexical_eps = ~can_be_ccont_eps
			// if(~(a->ep_span | b->ep_span) & purely_lexical_eps)return 0;
			// = ~ (a->ep_span | b->ep_span | can_be_ccont_eps)
			int n_reachable_eps = bitvec_three_way_or_count(a->ep_span_bv, b->ep_span_bv, can_be_ccont_ep_bv, n_epsbv);
			printf("spanning only rule '%s' wants to combine #%d and #%d; could reach %d / %d EPs\n", a->rule->name, a->id, b->id, n_reachable_eps, require_neps);
			if(n_reachable_eps < require_neps)
			{
				printf("not allowing spanning only rule '%s' to combine #%d and #%d\n", a->rule->name, a->id, b->id);
				return 0;
			}
		}
	}*/

	unify_attempts_total++;
	if(trace>2)return 1;	// no filtering
	if(rf)return 0;

	unify_attempts_pass_rf++;
	if(!gen_qc && quickcheck(a->qc, b->qc))return 0;	// quickcheck rejected this combination
	unify_attempts_pass_qc++;
	return 1;
}

int	unify_and_build1(struct edge	*a, struct edge	*b, struct edge	**Eout, int	force_noha)
{
	int	i, arg, res;
	struct dg	*rdg, *pdg;
#ifdef	TIM
	struct timeval	tv1, tv2;
#endif

	if(Eout)*Eout = NULL;

	if(a->rtl)arg = a->need - a->have - 1;
	else arg = a->have;

	//rtried[a->rule->rnum]++;

#ifdef	RULE_STATS
	if(a->ntries==0)natries[a->rule->rnum]++;
	a->ntries++;
	if(b->ntries==0)
	{
		if(b->rule)nptries[b->rule->rnum]++;
		else nptries[nrules]++;
	}
	b->ntries++;
#endif

	if(!a->dg)
	{
		// hyperactive parsing: we don't save active edges' dg's until they're actually used
		if(trace>1)printf("reconstructing hyperactive #%d [%d]\n", a->id, a->ha_use);
		if(a->ha_use > 200 || !b->dg)
		{
			if(recall_hyper(a))return 0;
			rdg = a->dg;
		}
		else
		{
#ifdef	RULE_STATS
			nrecomb[a->rule->rnum]++;
#endif
#ifdef	TIM
			gettimeofday(&tv1, 0);
#endif
			int result = unify_dg_tmp(a->ha_dg, a->ha_par, a->ha_arg);
#ifdef	TIM
			gettimeofday(&tv2, 0);
			base_unify_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
			nbase_unify++;
#endif
			if(result != 0)hyperfailure(a);
			rdg = a->ha_par;
			force_noha = 1;
			a->ha_use++;
		}
	}
	else rdg = a->dg;

	if(!b->dg)
	{
		// hyperpassive parsing: we don't save passive edges' dg's until they're actually used
		if(trace>1)printf("reconstructing hyperpassive edge #%d\n", b->id);
		if(b->ha_use > 200 || 1)
		{
			if(recall_hyper(b))return 0;
			pdg = b->dg;
		}
		else
		{
#ifdef	RULE_STATS
			nrecomb[b->rule->rnum]++;
#endif
#ifdef	TIM
			gettimeofday(&tv1, 0);
#endif
			int result = unify_dg_tmp(b->ha_dg, b->ha_par, b->ha_arg);
#ifdef	TIM
			gettimeofday(&tv2, 0);
			base_unify_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
			nbase_unify++;
#endif
			if(result != 0)hyperfailure(b);
			pdg = b->ha_par;
			force_noha = 1;
			b->ha_use++;
		}
	}
	else pdg = b->dg;
	//printf("recombine %s\n", a->rule->name);

	if(trace>1)printf("trying: #%d %s in #%d %s[%d]\n", b->id, pdg->xtype->name, a->id, rdg->xtype->name, arg);
#ifdef	TIM
	gettimeofday(&tv1, 0);
#endif
#ifdef	CLOCKCOUNT
	clock_t	T = clock();
#endif
//static int ut = -1;
//if(ut==-1)ut = new_timer("core unification");
//start_timer(ut);
	//if(!a->have)printf("EPS %s\n", a->rule->name);
	static int main_unify_timer = -1;
	if(main_unify_timer == -1)
		main_unify_timer = new_timer("main unify");
	IFCLOCK( start_timer(main_unify_timer); )
	res = unify_dg_tmp(pdg, rdg, arg);
	IFCLOCK( stop_timer(main_unify_timer, 1); )
//stop_timer(ut, 1);
#ifdef	CLOCKCOUNT
	unify_clock += clock()-T;
	unify_count++;
#endif
#ifdef	TIM
	gettimeofday(&tv2, 0);
	base_unify_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
	nbase_unify++;
#endif

	if(!res)unify_attempts_success++;

	if(!res && a->rule->orth)
	{
		// check whether orthographemic component accepts
		//printf("invoking unify_orthography(#%d & #%d)\n", a->id, b->id);
		if(unify_orthography(a->dg, b->dg, b->lex, a->rule))
		{
			res = -1;
			unify_attempts_bad_orth++;
		}
		/*// XXX this is sooo slow.
		char *sub = show_orth_leaves(b), *foo;
		if(trace > 1)printf(" .. yield of b is `%s'\n", sub);
		foo = inflect(a->rule->orth, sub);
		if(trace > 1)printf(" .. would inflect to `%s'\n", foo);
		if(!foo)
		{
			res = -1;
			unify_attempts_bad_orth++;
		}*/
	}

	if(!res)
	{
		static int	build_edge_timer = -1;
		if(build_edge_timer == -1)
			build_edge_timer = new_timer("build edge");
		IFCLOCK( start_timer(build_edge_timer); )
		int build_edge_result = build_edge(a, b, arg, rdg, Eout, force_noha);
		IFCLOCK( stop_timer(build_edge_timer, 1); )
		if(build_edge_result == -2)
		{
			// found a root analysis in first-only mode
			if(trace>1)printf("build_edge failed\n");
			return -1;
		}
		if(build_edge_result == -1)
		{
			if(trace>1)printf("build_edge found a cycle\n");
			return 0;
		}
		if((slab_usage() / (1024*1024)) >= max_chart_megabytes && !arbiter_request_memory())
		{
			fprintf(stderr, "NOTE: terminating search, too much RAM\n");
			itsdb_error("ran out of RAM while building forest");
			return -1;	// give up :(
		}
		return 1;
	}
	else
	{
#ifdef	UNIFY_PATHS
		extern struct path	unify_backtrace_path();
		if(trace>1)unify_backtrace();
		if(gen_qc)gqc_count_failure(unify_backtrace_path());
#endif
		forget_tmp();
	}

	return 0;
}

int	unify_and_build(struct edge	*a, struct edge	*b)
{
	struct edge	*e = NULL;
	//printf("u_and_b #%d #%d?\n", a->id, b->id);
	int	res = unify_and_build1(a, b, &e, !ENABLE_HYPERACTIVE);
	if(res == -1)return -1;
	if(e)add_agenda(e);
	return res;
}

int	combine(struct edge	*a, struct edge	*b)
{
	if(filter(a, b))
		return unify_and_build(a, b);
	else return 0;
}

char	*show_orth_leaves(struct edge	*e)
{
	int		i;
	char	*sub, *ret;

	if(!e->have)
	{
		if(e->lex)
		{
			int len = 0, i;
			for(i=0;i<e->lex->stemlen;i++)
				len += strlen(e->lex->stem[i]->name) + 1 - 2;
			ret = malloc(len+4); *ret = 0;
			for(i=0;i<e->lex->stemlen;i++)
			{
				if(i)strcat(ret, " ");
				strcat(ret, e->lex->stem[i]->name+1);
				ret[strlen(ret)-1] = 0;
			}
			return ret;
		}
		return strdup("[null]");
	}
	if(!e->daughters)return strdup("*INVENTED*");
	if(e->have==1)
	{
		sub = show_orth_leaves(e->daughters[0]);
		if(e->rule->orth)
		{
			//printf("applying orth rule `%s' to `%s'\n", e->rule->name, sub);
			ret = inflect(e->rule->orth, sub);
			if(!ret)ret = strdup("*INFL-FAIL*");
			free(sub);
			return strdup(ret);	// higher-up show_orth_leaves() might want to free what we return... blah.
		}
		else return sub;
	}
	else
	{
		for(ret=calloc(1,1),i=0;i<e->have;i++)
		{
			sub = show_orth_leaves(e->daughters[i]);
			ret = realloc(ret, strlen(ret) + strlen(sub) + 2);
			if(i)strcat(ret, " ");
			strcat(ret, sub);
			free(sub);
		}
		return ret;
	}
}

int	nfinal;

void	final_chart_stats()
{
	extern unsigned long long ndecomposed;
	packing_report();
	if(debug_level)
	{
		fprintf(stderr, "NOTE: unify filters: %lld total, %lld rf (%.1f%%), %lld qc (%.1f%% / %.1f%%), %lld success (%.1f%% / %.1f%%), %lld bad orth (%.1f%% / %.1f%%)\n", unify_attempts_total,
					unify_attempts_pass_rf, 100*(double)unify_attempts_pass_rf / unify_attempts_total,
					unify_attempts_pass_qc, 100*(double)unify_attempts_pass_qc / unify_attempts_total, 100*(double)unify_attempts_pass_qc / unify_attempts_pass_rf,
					unify_attempts_success, 100*(double)unify_attempts_success / unify_attempts_total, 100*(double)unify_attempts_success / unify_attempts_pass_qc,
					unify_attempts_bad_orth, 100*(double)unify_attempts_bad_orth / unify_attempts_total, 100*(double)unify_attempts_bad_orth / unify_attempts_success);
		fprintf(stderr, "NOTE: %lld / %lld (%.1f%%) passive edges were connected to roots\n", ndecomposed, total_passives, 100*(double)ndecomposed / total_passives);
	}
#ifdef TIM
	fprintf(stderr, "NOTE: unify was %.4fs for %lld ops = %gs\n", base_unify_time, nbase_unify, base_unify_time / nbase_unify);
	fprintf(stderr, "NOTE: finalize was %.4fs for %lld ops = %gs\n", base_finalize_time, nbase_finalize, base_finalize_time / nbase_finalize);
	base_unify_time = 0;
	base_finalize_time = 0;
#endif
	if(gen_qc)gqc_result();
}

// useful function for calling from the debugger...
int edge_is_in_chart(struct edge	*e)
{
	struct chart_cell	*c = cells + e->from*chart_size + e->to;
	int i, j;
	for(i=0;i<c->p_nedges;i++)
	{
		if(e == c->p_edges[i])printf("yes, directly\n");
		for(j=0;j<c->p_edges[i]->npack;j++)
			if(c->p_edges[i]->pack[j] == e)printf("indirectly, packed on #%d\n", c->p_edges[i]->id);
	}
	fflush(stdout);
}
