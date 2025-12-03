#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<signal.h>
#include	<time.h>
#include	<math.h>

#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"morpho.h"
#include	"mrs.h"
#include	"unpack.h"
#include	"token.h"
#include	"lattice-mapping.h"
#include	"lexical-parse.h"
#include	"timer.h"
#include	"profiler.h"
#include	"timeout.h"

double	ubertagging_threshold = 0.0001;
int		give_up_threshold = 70;

void	itsdb_dump_tokens(char	*name, char	*countname, struct lattice	*tokens);
int itsdb_report_parse(struct lattice	*tokens, struct lattice	*lexical_chart, int	status, int	tforest);

struct lattice	*last_token_chart;

extern int	total_edges, real_edges, passive_edges, used_edges, pused_edges, trace, used_total, pused_total;
extern int	question, exhaustive, lui_mode, inhibit_pack, inhibit_results, do_itsdb, do_itsdb_stdout, best_only;
extern float timer();

#ifdef	LEVEL_TIMER
float	level_times[100];
#endif
int		level = 0;
int	do_forest = 0;
extern int debug_level;
int yy_mode = 0;
int	do_improve_characterization = 0;

int	g_profiling = 0;

struct profiler	*start_sign_profiler(struct edge	*e)
{
	static struct profiler	**active_rule_profilers = NULL;
	static struct profiler	**passive_rule_profilers = NULL;
	static struct profiler	*passive_lex_profiler = NULL;
	chart_parsing_profiler->sortable = 10;
	if(!active_rule_profilers)
	{
		active_rule_profilers = calloc(sizeof(struct profiler*), nrules);
		passive_rule_profilers = calloc(sizeof(struct profiler*), nrules);
	}
	if(e->have == e->need)
	{
		if(e->have == 0)
		{
			start_and_alloc_profiler(&passive_lex_profiler, "lexeme", chart_parsing_profiler, NULL);
			return passive_lex_profiler;
		}
		struct rule	*r = e->rule;
		char	name[1024];
		sprintf(name, "passive: %s", r->name);
		start_and_alloc_profiler(&passive_rule_profilers[r->rnum], name, chart_parsing_profiler, NULL);
		return passive_rule_profilers[r->rnum];
	}
	else
	{
		struct rule	*r = e->rule;
		char	name[1024];
		sprintf(name, "active: %s", r->name);
		start_and_alloc_profiler(&active_rule_profilers[r->rnum], name, chart_parsing_profiler, NULL);
		return active_rule_profilers[r->rnum];
	}
}

static int	parse_process_edge(struct edge	*e)
{
	int			i, j, remain, pack = 0, from = e->from, to = e->to, have = e->have, nlist=0;
	struct chart_cell	*c;
	static struct edge	**list = 0;
	static int			alist = 0;

	// XXX experimental chart-pruning-like idea
	if(e->have == e->need && e->rule && !predict_1_rule_use(e->rule->name, e->from, e->to))
	{
		//printf("predicted we don't want #%d %s [%d - %d]\n",
			//e->id, e->rule->name, e->from, e->to);
		return 0;
	}

	// block() prevents in-chart edges built on frozen edges from playing further.
	// edges that were on the agenda at that time need to be block'd here.
	// also block cases where the daughter is a generalized edge all of whose pack-ees have been vaniquished (as block() does)
	// question: should this test be moved to pack_edge()?  not unless we call pack_edge() on both active and passives, maybe?
	if(e->daughters)
		for(i=0;i<e->have;i++)
		{
			if(e->daughters[i]->frozen==1)
			{
				//printf("NOT giving edge #%d a chance to try to pack; daughter[%d] = edge #%d was frozen\n", e->id, i, e->daughters[i]->id);
				return 0;
			}
			if(!e->daughters[i]->daughters && !e->daughters[i]->lex && !e->daughters[i]->npack)
				return 0;
		}
	int	jj;
	// reduce list of prepacked edges by the same technique
	for(j=jj=0;j<e->npack;j++)
	{
		struct edge	*p = e->pack[j];
		assert(p->daughters || p->lex);	// can't have a prepacked generalization edge; should have been flattened if so.
		for(i=0;i<p->have;i++)
		{
			if(p->daughters[i]->frozen==1)
			{
				//printf("NOT giving edge #%d a chance to try to pack; daughter[%d] = edge #%d was frozen\n", e->id, i, e->daughters[i]->id);
				continue;
			}
			if(!p->daughters[i]->daughters && !p->daughters[i]->lex && !p->daughters[i]->npack)
				continue;
		}
		e->pack[jj++] = p;
	}
	e->npack = jj;

#ifdef	LEVEL_TIMER
	if(!e->lex && (e->to-e->from != level))
	{
		if(e->to > e->from)
			level_times[e->to-e->from - 1] = timer();
		level = e->to - e->from;
	}
#endif

	if(!inhibit_pack && e->have == e->need)	// why not pack actives too?
	{
		static int packtimer = -1;
		if(packtimer==-1)packtimer = new_timer("packing");
		IFCLOCK( start_timer(packtimer); );
		if(g_profiling)
			start_and_alloc_profiler(&packing_profiler, "packing", chart_parsing_profiler, NULL);
		pack = pack_edge(e);
		if(g_profiling)
			stop_profiler(packing_profiler, 1);
		IFCLOCK( stop_timer(packtimer, 1); );
		if(pack==1)
			return 0;	// big savings! woohoo!
	}
	if(pack==0)add_edge_to_chart(e);

	struct profiler	*prof = NULL;
	if(g_profiling)
		prof = start_sign_profiler(e);

	if(!alist){list=calloc(sizeof(struct edge*), 4); alist=4;}
#define	LADD(e)	do { if(nlist+1 > alist) { \
					alist *= 2; \
					list = realloc(list, sizeof(struct edge*)*alist); \
					} list[nlist++] = (e); } while(0)

	// try to combine with edges on either side
	if(e->have == e->need)
	{
//		char	fil[nrules*2];
//		if(constraint_rule_filter(e->lex, e->id, e->dg, fil) != 0)
//			return 0;

		c = cells + from;
		// passive edge
		for(i=0;i<=from;i++)
		{
			struct edge	**E = c[i*chart_size].al_edges, **F = E+c[i*chart_size].al_nedges;
			for(;E<F;E++) if(to + ((*E)->need - (*E)->have - 1) < chart_size)
//				if(!fil[2*(*E)->rule->rnum + 0] || !fil[2*(*E)->rule->rnum + 1])
					LADD(*E);
		}
		c = cells + to*chart_size;
		for(i=to;i<chart_size;i++)
		{
			struct edge	**E = c[i].ar_edges, **F = E+c[i].ar_nedges;
			for(;E<F;E++) if(from - ((*E)->need - (*E)->have - 1) >= 0)
//				if(!fil[2*(*E)->rule->rnum + 0] || !fil[2*(*E)->rule->rnum + 1])
					LADD(*E);
		}
	}
	else
	{
		// active edge
		remain = e->need - e->have;
		if(e->rtl)
		{
			for(i=0,c=cells+from;i<=from;i++)
			{
				struct edge	**E = c[i*chart_size].p_edges, **F = E+c[i*chart_size].p_nedges;
				for(;E<F;E++) if((*E)->from - (remain-1) >= 0)LADD(*E);
			}
		}
		else
		{
			for(i=to,c=cells+to*chart_size;i<chart_size;i++)
			{
				struct edge **E = c[i].p_edges, **F = E+c[i].p_nedges;
				for(;E<F;E++) if((*E)->to + (remain-1) < chart_size)LADD(*E);
			}
		}
	}
	//printf(" edge #%d found %d potential neighbors\n", e->id, nlist);

	if(!nlist)
	{
		if(prof)stop_profiler(prof, 1);
		return 0;
	}

	if(e->have == e->need)
	{
		__builtin_prefetch(e->rule);
		for(i=j=0;i<nlist;i++)
		{
			if(i+2<nlist)__builtin_prefetch(list[i+2]);
			if(i+1<nlist)__builtin_prefetch(list[i+1]->rule);
			if(filter(list[i], e))
				list[j++] = list[i];
		}
	}
	else
	{
		__builtin_prefetch(e->rule);
		for(i=j=0;i<nlist;i++)
		{
			if(i+2<nlist)__builtin_prefetch(list[i+2]);
			if(i+1<nlist)__builtin_prefetch(list[i+1]->rule);
			if(filter(e, list[i]))
				list[j++] = list[i];
		}
	}
	nlist = j;

	if(!nlist)
	{
		if(prof)stop_profiler(prof, 1);
		return 0;
	}

/*
int	cmp(const void	*a, const void	*b)
{
	struct dg	*da = (*(const struct edge**)a)->dg;
	struct dg	*db = (*(const struct edge**)b)->dg;
	if(da && db)return db->gen - da->gen;
	else if(da)return -1;
	else if(db)return 1;
	else return 0;
}
qsort(list, nlist, sizeof(void*), cmp);
*/

	if(e->have == e->need)
	{
		for(i=0;i<nlist;i++)
			if(unify_and_build(list[i], e) == -1)return -1;
	}
	else
	{
		for(i=0;i<nlist;i++)
			if(unify_and_build(e, list[i]) == -1)return -1;
	}
	if(prof)stop_profiler(prof, 1);
	return 0;
}

int	fits(struct rule	*r, int	d, struct edge	*e)
{
	if(e->rule)return check_rf(r, e->rule, d);
	if(d==r->ndaughters-1)return check_trl(r, e->lex->lextype);
	return 1;
}

int	quickcheck_rule(int	rnum, int	d, struct qc	*q)
{
	static struct qc	**rqc = 0;
	if(!rqc)
	{
		int	i;
		rqc = malloc(sizeof(struct qc*)*nrules*2);
		for(i=0;i<nrules;i++)
		{
			rqc[2*i+0] = extract_qc_arg(rules[i]->packdg, 0);
			if(rules[i]->ndaughters>1)
				rqc[2*i+1] = extract_qc_arg(rules[i]->packdg, 1);
		}
	}
	return quickcheck(rqc[2*rnum+d], q);
}

void	halftime_analysis()
{
	struct chart_cell	*right = cells+(chart_size-1)+(chart_size-2)*chart_size;
	char				parent[nrules], uleftsib[nrules], leftsib[nrules];
	int					i, j;

	bzero(parent, sizeof(parent));
	bzero(uleftsib, sizeof(parent));
	bzero(leftsib, sizeof(parent));
	//printf("rightmost passive edges: %d\n", right->p_nedges);
	for(i=0;i<right->p_nedges;i++)
	{
		struct edge	*e = right->p_edges[i];
		for(j=0;j<nrules;j++) if(!rules[j]->rtl && rules[j]->ndaughters>1)
			if(fits(rules[j], rules[j]->ndaughters-1, e) &&
				!quickcheck_rule(j, rules[j]->ndaughters-1, e->qc))
				parent[j] = 1;
	}
	//printf("rightmost active RL edges: %d\n", right->ar_nedges);
	for(i=0;i<right->ar_nedges;i++)
	{
		struct edge	*e = right->ar_edges[i];
		if(!e->have)continue;
		parent[e->rule->rnum] = 1;
	}

	for(i=0;i<nrules;i++) if(parent[i])
		printf("	right daughter of %s\n", rules[i]->name);

	// mark all unaries which fit the left slot of the parent, recursively

	int again;
	do { again = 0;
	for(i=0;i<nrules;i++) if(parent[j])
		for(j=0;j<nrules;j++) if(rules[j]->ndaughters==1
			&& check_rf(rules[i], rules[j], 0) && !parent[j])parent[j] = 1, again=1; } while(again);

	// find all binaries that fit into the parents or the unaries
	for(i=0;i<nrules;i++) if(parent[i])
		for(j=0;j<nrules;j++)
			if(check_rf(rules[i], rules[j], 0))leftsib[j] = 1;

	for(i=0;i<nrules;i++) if(leftsib[i])
		printf("	left sibling could be %s\n", rules[i]->name);
}

//int		wcap[1024];
char	current_sentence[10240] = "(not initialized)";
int didsent;
int	show_probability = 0;

int	prepare_parse_chart(struct lattice	*token_chart, struct lattice	*lexical_chart)
{
	sort_lattice(lexical_chart);

	int	nwords = lexical_chart->lattice_vertex_id_gen - 1;

	// setup the chart
	clear_chart(nwords+1);

	// put lexical edges into agenda
	int i;
	// note: edges need to be process_edge()'d into the chart in the same order they were discovered in lexical parsing,
	// which should be the same order they appear in the lexical_chart->edges list.
	// if we dont do it in the right order, we can violate some assumptions of the retroactive packing system
	// and end up with spurious readings.
	for(i=0;i<lexical_chart->nedges;i++)
	{
		struct lattice_edge	*le = lexical_chart->edges[i];
		assert(le->edge != NULL);
		le->edge->from = le->from->id;
		le->edge->to = le->to->id;
		add_agenda(le->edge);
	}

	// optionally add edges from a robust shallow parse tree
	if(!yy_mode)dublin_robustness(lexical_chart, current_sentence);

	// put syntax rules into agenda
	//if(rtried)free(rtried);
	//rtried = calloc(sizeof(int),nrules);
	agenda_rules(nwords);

	return nwords;
}

void	(*parse_callback)(struct hypothesis	*hyp, struct mrs	*mrs) = NULL;

// show analyses
int parse_show_result(struct hypothesis	*hyp, struct mrs	*mrs, double	prob)
{
	struct dg	*root = hyp->dg, *sem;
	extern char	*mrs_end;
	extern int print_trees;
	if(trace>0)printf("edge #%d has a sentential unpacking\n", hyp->edge->id);
	if(trace>1){print_dg(hyp->dg); printf("\n");}
	if(!inhibit_results)
	{
		char	*sentence = current_sentence;
		if(sentence && !question && !didsent){printf("SENT: %s\n", sentence);didsent=1;}
		if(show_probability)printf("probability = %f\n", prob);
		if(print_trees)
		{
			mrs_end = " ; ";
			print_mrs(mrs);
			extern int report_labels;
			char	*dstr = report_labels?hypothesis_to_labelled_tree_string(hyp):hypothesis_to_dstring(hyp);
			fflush(stdout);
			puts(dstr);
			fflush(stdout);
			mrs_end = "\n";
			/*extern int saved_termerr;
			write(saved_termerr, dstr, strlen(dstr));
			write(saved_termerr, mrs_end, 1);*/
			//print_hypothesis(hyp, printf, 0);
			//printf((mrs_end = "\n"));
			free(dstr);
		}
		else print_mrs(mrs);
	}
	if(parse_callback)
		parse_callback(hyp, mrs);
	free_mrs(mrs);
	//printf("\n");
	//printf("dstring = `%s'\n", slab_escape(hypothesis_to_dstring(hyp)));
	return 1;
}

static int chart_setup_timer = -1;

int	parse(int	nwords, char	**words, int	*cfrom, int	*cto, char	*sentence)
{
	clock_t	start = clock();

	if(chart_setup_timer == -1)chart_setup_timer = new_timer("chart setup");
	start_timer(chart_setup_timer);

	if(g_profiling)start_and_alloc_profiler(&token_mapping_profiler, "token mapping", parse_profiler, preprocess_profiler);

	// setup a token lattice and do token mapping
	struct lattice	*token_chart = build_token_chart(nwords, words, cfrom, cto);
	if(!token_chart) { stop_timer(chart_setup_timer, 1); return -1; }

	return parse_with_token_chart(token_chart, start);
}

int parse_with_token_chart(struct lattice	*token_chart, clock_t	start)
{
	int		i, count, cforest;
	int		num_parses = 0, num_entries;
	float	t_setup, t_forest, t_unpack;
	struct dg	*root;
	struct dg	*sem;
	struct edge	*edge;

	if(do_itsdb)itsdb_dump_tokens(":p-input", ":ninputs", token_chart);
	apply_token_mapping(token_chart);
	sort_lattice(token_chart);
	if(!yy_mode && do_improve_characterization)
		improve_token_lattice_characterization(token_chart);

	if(token_chart->nvertices>give_up_threshold)
	{
		fprintf(stderr, "NOTE: giving up, too many words (%d+)\n", give_up_threshold);
		itsdb_error("too many words");
		if(do_itsdb)itsdb_report_parse(token_chart, NULL, -2, 0);
		stop_timer(chart_setup_timer, 1);
		return -2;
	}

	if(trace)print_token_chart(token_chart);

	if(trace)printf("finished token mapping\n");

	if(g_profiling)start_and_alloc_profiler(&lexical_lookup_profiler, "lexical lookup", parse_profiler, token_mapping_profiler);

	// do lexical lookup
	struct lattice	*lexical_chart = lexical_lookup_into_chart(token_chart);
	if(!lexical_chart)
	{
		fprintf(stderr, "NOTE: failed to build lexical chart\n");
		stop_timer(chart_setup_timer, 1);
		return -1;
	}
	if(trace)printf("finished lexical lookup\n");

	if(g_profiling)start_and_alloc_profiler(&lexical_parsing_profiler, "lexical parsing", parse_profiler, lexical_lookup_profiler);

	extern int chart_size;
	chart_size = 0;	// set to a predictable value rather than leaving it whatever the last sentence had; used in deciding whether an edge is spanning or not, as early as lexical parsing, for deciding whether the rule_root_utc[] is applicable.

	extern int reduce_chart_before_lexical_parsing;

	if(!reduce_chart_before_lexical_parsing)
	{
		// do lexical parsing
		int rv = lexical_parse_lattice(lexical_chart);
		if(rv == -1)
		{
			itsdb_error("ran out of RAM in lexical parsing");
			return -1;	// ran out of memory in lexical parsing!
		}
	}

	if(reduce_lexical_lattice(lexical_chart, token_chart))
	{
		fprintf(stderr, "NOTE: post reduction gap\n");
		stop_timer(chart_setup_timer, 1);
		if(do_itsdb)itsdb_report_parse(token_chart, lexical_chart, -2, 0);
		return -2;
	}

	if(reduce_chart_before_lexical_parsing)
		lexical_parse_lattice(lexical_chart);

	if(trace)print_lexical_chart(lexical_chart);
	if(trace)printf("finished lexical parsing\n");

	if(g_profiling)start_and_alloc_profiler(&lexical_filtering_profiler, "lexical filtering", parse_profiler, lexical_parsing_profiler);

	// do lexical filtering
	apply_lexical_filtering(lexical_chart);
	if(trace)printf("finished lexical filtering\n");

#include	"ubertag.h"
extern struct ubertagger	*the_ubertagger;
extern int	enable_ubertagging;
	if(g_profiling)start_and_alloc_profiler(&ubertagging_profiler, "übertagging", parse_profiler, lexical_filtering_profiler);
	if(the_ubertagger && enable_ubertagging)
		ubertag_lattice(the_ubertagger, lexical_chart, log(ubertagging_threshold));

	if(g_profiling)start_and_alloc_profiler(&chart_parsing_profiler, "chart parsing", parse_profiler, ubertagging_profiler);

	// XXX far-fetched experiment...
	//first_pass_parse(lexical_chart);
	//return 1;

	// lexemes have no packing restrictor applied to them thus far.
	// make sure all copy()'s from here on out (until unpacking time) are restricting.
	if(!inhibit_pack)enable_packing(1);
	// setup the main parse chart
	int nwords = prepare_parse_chart(token_chart, lexical_chart);
	if(nwords < 0)
	{
		fprintf(stderr, "NOTE: negative lexical chart length\n");
		itsdb_error("negative lexical chart length");
		if(do_itsdb)itsdb_report_parse(token_chart, lexical_chart, -2, 0);
		stop_timer(chart_setup_timer, 1);
		enable_packing(0);
		return -2;
	}
	assert(nwords >= 0);
	if(!nwords)
	{
		fprintf(stderr, "NOTE: nothing to parse\n");
		itsdb_error("nothing to parse");
		if(do_itsdb)itsdb_report_parse(token_chart, lexical_chart, -2, 0);
		stop_timer(chart_setup_timer, 1);
		enable_packing(0);
		return -2;
	}

	// XXX experimental chart-pruning-like idea
	predict_rule_uses(nwords, lexical_chart);

	cancel_task = 0;
	did_timeout = 0;
	signal(SIGALRM, alarm_handler);

	if(timeout_seconds > 0)
		alarm(timeout_seconds);

	stop_timer(chart_setup_timer, 1);
	static int chart_parsing_timer = -1;
	if(chart_parsing_timer == -1)chart_parsing_timer = new_timer("chart parsing");
	start_timer(chart_parsing_timer);

	t_setup = timer();

	// do the actual parsing
	int	half = nwords/2;
	double t_half;
	while( !cancel_task && (edge = next_agenda(0)) )
	{
		if(edge->to-edge->from >= half)
		{
			half = nwords+2;
			t_half = timer();
			//halftime_analysis();
		}
		if(parse_process_edge(edge))break;
	}

	compact_generalization_edges();

	enable_packing(0);

	stop_timer(chart_parsing_timer, 1);

	if(g_profiling)start_and_alloc_profiler(&unpacking_profiler, "unpacking", parse_profiler, chart_parsing_profiler);

	t_forest = t_half + timer();
	cforest = clock() - start;

	if(do_forest)
	{
		char	*sentence = current_sentence;
		fflush(stdout);
		if(sentence)fprintf(stderr, "SENT: %s\n", sentence);
		int found_root = output_forest(&cells[chart_size-1], token_chart);
		fflush(stdout);
		fprintf(stderr, "NOTE: %d readings [forest], ", found_root);
		print_slab_stats();
		fprintf(stderr, "\n");
		num_parses = 1;
	}
	else if(!do_itsdb && !lui_mode)
	{
		didsent = 0;
		if(chart_size>0)
			num_parses = iterate_cell_root_hypotheses(&cells[chart_size-1], parse_show_result, best_only);
		else num_parses = 0;

		fprintf(stderr, "NOTE: %d readings, added %d / %d edges to chart (%d fully instantiated, %d actives used, %d passives used)\t",
			num_parses, total_edges, real_edges, passive_edges, used_edges, pused_edges);
		print_slab_stats();

		//rule_profiler();	// XXX comment me out normally
	}
	else if(do_itsdb)
	{
		num_parses = itsdb_report_parse(token_chart, lexical_chart, 0, (int)((long long)cforest*1000 / CLOCKS_PER_SEC));
	}
	else if(lui_mode)
	{
		num_parses = output_lui_trees(cells+chart_size-1, current_sentence, best_only, 0);
		if(!num_parses){}//output_lui_chart(words);
		last_token_chart = token_chart;
	}
	alarm(0);

//	extern int	output_edge_vectors;
//	if(output_edge_vectors)
//		do_output_edge_vectors();

	t_unpack = timer();

	used_total += used_edges;
	pused_total += pused_edges;

	if(0)
	{
		static FILE	*f = 0;
		//extern long long ndecomposed;
		//static long long ond = 0;
		if(!f)f = fopen("/tmp/times", "w");
		fprintf(f, "%d	%d	%f	%f	%f	%s\n", nwords, num_parses, t_setup, t_forest, t_unpack, current_sentence);
		//ond = ndecomposed;
		fflush(f);
	}

	return num_parses;
}

void	preprocess_line(char	*string, int	*Nwords, char	***Words, int	**CFrom, int	**CTo);

int	parse_line1(char	*line)
{
	char	*copy = NULL;
	int	nparse = 0;
	int	nwords = 0, i, j;
	int		*cfrom = NULL, *cto = NULL;
	char	**words = NULL, *p, *q;
	extern int preprocess_only;

	timer();
	extern int tsdb_notes;
	if(tsdb_notes)tsdb_parse_note_start();
	if(g_profiling)
	{
		if(parse_profiler)stop_profilers_recursively(parse_profiler);
		start_and_alloc_profiler(&parse_profiler, "parsing", NULL, NULL);
	}

	last_token_chart = NULL;

	// a starting place for main-chart edge IDs
	reset_edges();

	if(yy_mode)
	{
		strcpy(current_sentence, "(yy mode)");
		nparse = parse_yy(line);
		goto finished;
	}

	strcpy(current_sentence, "(preparing)");
	while(line[0] && line[strlen(line)-1] == '\n')line[strlen(line)-1] = 0;
int	check_mbs(char	*mbs);
	if(!*line || check_mbs(line)==-1)
	{
		if(!inhibit_results && !do_itsdb_stdout){printf("SKIP: %s\n", line);fflush(stdout);}
		if(do_itsdb) itsdb_report_parse(NULL, NULL, -1, 0);
		return -1;
	}
	if(!strncmp(line, "<DOC", 4))
	{
		printf("%s\n", line);
		return -1;
	}

	copy = strdup(line);

	if(g_profiling)
		start_and_alloc_profiler(&preprocess_profiler, "REPP", parse_profiler, NULL);
	preprocess_line(copy, &nwords, &words, &cfrom, &cto);
	if(preprocess_only)
	{
		if(!inhibit_results)
		{
			for(i=0;i<nwords;i++)
			{
				printf("%s%s", i?" ":"", words[i]);
				if(debug_level)printf("<%d:%d>", cfrom[i], cto[i]);
			}
			printf("\n");
		}
		goto finished;
	}

	if(nwords>200)
	{
		fprintf(stderr, "NOTE: 0 readings, too many words (200+)\n");
		itsdb_error("too many words (200+ before token mapping)");
		if(!inhibit_results && !do_itsdb_stdout){printf("SKIP: %s\n", line);fflush(stdout);}
		goto finished;
	}

	strncpy(current_sentence, line, 10239);current_sentence[10239] = 0;
	level = 0;
	timer();
	nparse = parse(nwords, words, cfrom, cto, current_sentence);
	if(nparse<=0 && !inhibit_results && !do_itsdb_stdout){printf("SKIP: %s\n", line);fflush(stdout);}

#ifdef	LEVEL_TIMER
	level_times[nwords] = timer();
	for(i=1;i<=nwords;i++)printf(" level %d: %f\n", i, level_times[i]);
#endif

	if(nparse<-1)fprintf(stderr, "NOTE: ignoring `%s'\n", current_sentence);
	if(do_itsdb && nparse==-1)itsdb_report_parse(NULL, NULL, -1, 0);

finished:
	if(tsdb_notes)tsdb_parse_note_end();
	if(g_profiling)stop_profilers_recursively(parse_profiler);
	clear_mrs();
	for(i=0;i<nwords;i++)free(words[i]);
	if(words)free(words);
	if(cfrom)free(cfrom);
	if(cto)free(cto);
	if(copy)free(copy);
	return nparse;
}

int parse_line(char	*line)
{
	int res = parse_line1(line);
	if(!inhibit_results)printf("\n\n");
	fflush(stdout);
	return res;
}

show_last_parse_chart()
{
	// ... the slab has been clear_slab()'d, but
	// we likely still own the memory and it likely hasn't been trampled yet.
	// hehe... if we start having strange issues here,
	// we should just not clear the slab until next parse when in LUI mode.
	if(!last_token_chart)
		fprintf(stderr, "no chart to display.\n");
	else output_lui_chart(last_token_chart);
}

rule_profiler()
{
	int i,j;
	static FILE	*f = NULL;
	if(!f)f = fopen("/tmp/rule_profile.txt", "w");
	for(i=0;i<chart_size*chart_size;i++)
	{
		struct chart_cell	*c = cells + i;
		for(j=0;j<c->p_nedges;j++)
		{
			struct edge	*e = c->p_edges[j];
			if(!e->rule)continue;
			fprintf(f, "%s %d %d %d\n", e->rule->name, e->unpack?1:0, (e->to-e->from), chart_size - (e->to-e->from));
		}
	}
	fflush(f);
}
