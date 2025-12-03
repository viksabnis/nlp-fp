#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<limits.h>
#include	<wchar.h>
#include	<ctype.h>

#include	"conf.h"
#include	"rule.h"
#include	"chart.h"
#include	"morpho.h"
#include	"tdl.h"
#include	"lexicon.h"
#include	"freeze.h"
#include	"lexical-parse.h"
#include	"lattice-mapping.h"
#include	"token.h"
#include	"profiler.h"

extern int inhibit_pack;

void	add_new_lexical_edge(struct lattice	*lc, struct edge	*e)
{
	struct lattice_edge	*lat_e = slab_alloc(sizeof(*lat_e));
	bzero(lat_e, sizeof(*lat_e));
	assert(e->from <= lc->nvertices);
	assert(e->to <= lc->nvertices);
	lat_e->from = lc->vertices[e->from];
	lat_e->to = lc->vertices[e->to];
	lat_e->token = NULL;
	lat_e->edge = e;
	add_lattice_edge(lc, lat_e);
}

struct lattice	*lexical_lookup_into_chart(struct lattice	*token_chart)
{
	struct lattice	*lc = slab_alloc(sizeof(*lc));
	int i;

	sort_lattice(token_chart);

	// make identical vertices in the lexical chart, with initially no edges
	bzero(lc, sizeof(*lc));
	lc->nvertices = token_chart->nvertices;
	lc->vertices = slab_alloc(sizeof(struct lattice_vertex*)*lc->nvertices);
	lc->lattice_vertex_id_gen = token_chart->lattice_vertex_id_gen;
	for(i=0;i<lc->nvertices;i++)
	{
		lc->vertices[i] = slab_alloc(sizeof(struct lattice_vertex));
		bzero(lc->vertices[i], sizeof(struct lattice_vertex));
		lc->vertices[i]->id = token_chart->vertices[i]->id;
	}
	assert(token_chart->start && token_chart->end);
	lc->start = lc->vertices[token_chart->start->id];
	lc->end = lc->vertices[token_chart->end->id];

	void	edge_handler(struct edge	*le, struct token	**tokens)
	{
		extern int debug_level;
		if(debug_level)printf(" lexical lookup found lexeme '%s'\n", le->lex->word);
		add_new_lexical_edge(lc, le);
	}

	int res = lexical_lookup(token_chart, edge_handler);
	if(res!=0)
	{
		//fprintf(stderr, "NOTE: lexical coverage gap\n");
		itsdb_error("pre-reduction lexical gap");
		return NULL;
	}
	return lc;
}

struct profiler	*start_lrule_profiler(struct rule	*r)
{
	static struct profiler	**profs=NULL;
	if(!profs)profs = calloc(sizeof(struct profiler*),nrules);
	start_and_alloc_profiler(profs+r->rnum, r->name, lexical_parsing_profiler, NULL);
	lexical_parsing_profiler->sortable = 5;
	return profs[r->rnum];
}

int	lexical_parse(struct lattice	*lc, struct lattice_edge	*le, struct edge	**epsila, char	*used)
{
	struct edge	*e = le->edge;
	int	i;

	//printf("lexparsing edge #%d '%s'\n", le->edge->id, e->lex->word);
	//for(i=0;i<le->edge->north_routes;i++)
	//	printf("oroute %d: next rule %s\n", i, (le->edge->orth_routes[i].len>0)?(rules[le->edge->orth_routes[i].rules[0]]->name):"none");
	for(i=0;i<nrules;i++)
	{
		if(!rules[i]->lexical)continue;

		// check_lexical_rule_constraints is part of filter()... why were we doing this twice?
		//if(check_lexical_rule_constraints(rules[i], le->edge))continue;
		//printf("should I try lexrule '%s'?\n", rules[i]->name);
		epsila[i]->from = epsila[i]->to = le->edge->from;
		struct profiler	*prof;
		int	fired = 0;
		if(g_profiling)prof = start_lrule_profiler(rules[i]);
		if(filter(epsila[i], le->edge))
		{
			//printf("trying lexrule '%s' on edge #%d ('%s')\n", rules[i]->name, le->edge->id, show_orth_leaves(le->edge));
			struct edge	*e = NULL;
			int	res = unify_and_build1(epsila[i], le->edge, &e, 1);
			extern int trace;
			if(res == -1)
			{
				//fprintf(stderr, "unify_and_build1 got mad\n");
				return -1;
			}
			if(res == 1 && e != NULL)
			{
				//printf(" -- built new edge #%d ('%s')\n", e->id, show_orth_leaves(e));
				add_new_lexical_edge(lc, e);
				fired = 1;
			}
			else if(trace>1)
			{
				printf("rule %s failed on lexical-parsing edge #%d ; res = %d\n", rules[i]->name, le->edge->id, res);
				unify_backtrace();
				/*printf("mother AVM:\n");
				print_dg(epsila[i]->dg);printf("\n");
				printf("daughter AVM:\n");
				print_dg(le->edge->dg);printf("\n");*/
			}
		}
		if(g_profiling)stop_profiler(prof, fired);
	}
	return 0;
}

int	lexical_parse_lattice(struct lattice	*lc)
{
	int i, j;
	struct edge	*epsila[nrules];
	char		used[nrules];
	struct lattice_vertex	*epsila_starts[nrules];

	// apply lexical rules as much as possible
	for(i=0;i<nrules;i++)
		if(rules[i]->lexical)
		{
			used[i] = 1;
			epsila_starts[i] = NULL;
		}
	int	_save_inhibit_pack = inhibit_pack;
	inhibit_pack = 1;
	for(i=0;i<lc->nedges;i++)
	{
		struct lattice_edge	*e = lc->edges[i];
		if(e->edge->frozen)continue;
		for(j=0;j<nrules;j++)
			if(rules[j]->lexical && used[j] && epsila_starts[j] != e->from)
			{
				// prevent structure sharing between edges that start in different places
				used[j] = 0;
				epsila_starts[j] = NULL;
				epsila[j] = epsilon_edge(rules[j], 0, 0, NULL);
			}
		if(lexical_parse(lc, lc->edges[i], epsila, used) != 0)
		{
			inhibit_pack = _save_inhibit_pack;
			return -1;
		}
		for(j=0;j<nrules;j++)
			if(rules[j]->lexical && used[j])
				epsila_starts[j] = e->from;
	}
	inhibit_pack = _save_inhibit_pack;

	// delete edges which have not satisfied their orth_routes
	for(i=0;i<lc->nedges;i++)
	{
		struct edge	*e = lc->edges[i]->edge;
		if(!edge_is_ready_for_syntax(e))
		{
			// this edge cannot play in syntax, since it has not completely inflected
			remove_lattice_edge(lc, lc->edges[i]);
			i--;
		}
	}
	return 0;
}

void	print_lexical_chart(struct lattice	*tc)
{
	int	i;
	for(i=0;i<tc->nedges;i++)
	{
		struct lattice_edge	*e = tc->edges[i];
		struct edge	*t = e->edge;
		printf("lexical edge #%d le %p vtx [%d-%d] lexeme '%s'\n",
			t->id, e, e->from->id, e->to->id, t->lex->word);
	}
}

int	reduce_lexical_lattice(struct lattice	*lat, struct lattice	*toklat)
{
	extern int debug_level;
	char		cover[1024];

	static struct profiler	*redprof = NULL;

	int	length = lat->lattice_vertex_id_gen - 1;
	//printf("reducer: length = %d\n", length);
	if(length<=0)return 0;
	assert(length < sizeof(cover));

	if(g_profiling)start_and_alloc_profiler(&redprof, "chart reduction", lexical_parsing_profiler, NULL);

	//sanity_check_agenda(length);
	bzero(cover, length);
	int	I, J, i;
	for(I=0;I<lat->nedges;I++)
	{
		struct edge	*e1 = lat->edges[I]->edge;
		assert(e1->lex);

		for(i=0;i<nchart_dependencies;i++)
		{
			struct dg	*from = dg_path(e1->dg, chart_dependencies_from[i]);
			//printf("edge #%d %s from = %s\n", e1->id, e1->lex->word, from?from->xtype->name:"NULL");
			if(from)
			{
				int	satisfied = 0;
				for(J=0;J<lat->nedges;J++)
				{
					struct edge	*e2 = lat->edges[J]->edge;
					assert(e2->lex);
					struct dg	*to = dg_path(e2->dg, chart_dependencies_to[i]);
					//if(to && descendent_of(to->xtype->tnum, from->xtype))satisfied = 1;
					// glb seems more appropriate than descendent_of, and indeed explained a rather obscure difference vs pet...
					if(to && glb(to->xtype, from->xtype))satisfied = 1;
				}
				if(!satisfied)break;
				//printf("dep on `%s' satisfied\n", e1->lex->word);
			}
		}
		if(i<nchart_dependencies)
		{
			// reduce
			// don't mark as frozen; strange but true:
			// an edge built on top of this one by lexical rules
			// can survive chart reduction, and if we mark this one as frozen
			// then the parent might not make it into the chart
			//e1->frozen = 1;
			//printf("reduce edge #%d %s dep %d\n", e1->id, e1->lex->word, i);
			remove_lattice_edge(lat, lat->edges[I]);
			I--;
		}
		else	// keep
		{
			for(i=e1->from;i<e1->to;i++)
			{
				//printf("%s provides %d\n", e1->lex->word, i);
				//printf("`%s' from %d to %d\n", e1->lex->word, e1->from, e1->to);
				cover[i] = 1;
			}
		}
	}

	if(g_profiling)stop_profiler(redprof, lat->nedges);

	// check that lexemes cover the whole span;
	// if not we have no chance of building a spanning analysis.
	for(i=0;i<length;i++)
		if(!cover[i])
		{
			//if(debug_level)fprintf(stderr, "NOTE: lexemes do not span position %d `%s'!\n", i, words[i]);
			if(1)//if(debug_level)
			{
				char	*word = NULL;
				int k;
				for(k=0;k<toklat->nedges;k++)
				{
					struct lattice_edge	*te = toklat->edges[k];
					if(te->from->id == i)
					{
						if(!word || strlen(word)>strlen(te->token->string))
							word = te->token->string;
					}
				}
				fprintf(stderr, "NOTE: lexemes do not span position %d `%s'!\n", i, word?:"?");
				itsdb_error("post-reduction lexical gap");
			}
			return -1;
		}

	return 0;
}
