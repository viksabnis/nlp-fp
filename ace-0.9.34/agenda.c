#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<stdio.h>

#include	"conf.h"
#include	"chart.h"
#include	"morpho.h"
#include	"lexicon.h"

extern int	debug_level;
extern int trace;

struct task
{
	struct task	*next, *prev;
	struct edge	*edge;
};

#define	NPRIO	256

#define	EPSILON_PRIORITY(rule)	(NPRIO-1)
#define	EDGE_PRIORITY(edge)		(NPRIO-1 - (edge->to-edge->from))
#define	GEN_EDGE_PRIORITY(edge)		(NPRIO-1 - (edge->neps))
#define	LEX_PRIO				(NPRIO-2)

static struct queue
{
	struct task	*start, *end;
}	agenda[NPRIO];

int	highest = -1;

struct task	*lstart[500];

void	clear_agenda()
{
	int	i;

	for(i=0;i<NPRIO;i++)
	{
		agenda[i].start = 0;	// stuff is slab-alloc'd, don't worry about freeing
		agenda[i].end = 0;
	}
	bzero(lstart, sizeof(struct task*)*500);
	highest = -1;
}

void	add_agenda(struct edge	*e)
{
	struct task	*t = slab_alloc(sizeof(struct task));

	assert(e->to >= e->from);

	if(trace && e->lex && e->have==e->need)
	{
		struct lexeme	*lex = e->lex;
		printf("added lexeme `%s' = #%d  [%d-%d]\n", lex->word, e->id, e->from, e->to);
		if(trace>1){print_dg(e->dg); printf("\n\n");}
	}

	e->ntries = 0;
	e->unpack = 0;
	// we were zeroing these out until 2013-sept-4.
	// that broke the new generalization packing trick, since we want to record some packing on generalized edges before they even make it into the agenda.
	// hopefully not doing this doesn't break anything...  edge producers should really make sure their fields are set appropriately already!
	//e->npack = 0;
	//e->pack = 0;

	if(g_mode == GENERATING)
	{
		e->prio = GEN_EDGE_PRIORITY(e);
		//printf("gen edge with %d eps; prio = %d\n", e->neps, e->prio);
	}
	else if(e->from==e->to)e->prio = EPSILON_PRIORITY(e->rule);
	else if(e->lex)e->prio = LEX_PRIO;	// note: lexical edges must be returned from the agenda in FIFO order
	else e->prio = EDGE_PRIORITY(e);

	if(e->prio < 0 || e->prio >= NPRIO)
	{
		fprintf(stderr, "tried to agendize an edge with priority %d!\n", e->prio);
		exit(-1);
	}

	t->edge = e;
	t->next = 0;
	t->prev = agenda[e->prio].end;
	if(agenda[e->prio].end)agenda[e->prio].end->next = t;
	else agenda[e->prio].start = t;
	agenda[e->prio].end = t;

	if(e->lex && !lstart[e->from])lstart[e->from] = t;

	if(e->prio > highest)highest = e->prio;

	if(e->have == e->need)
	{
		extern unsigned long long total_passives;
		total_passives++;
	}
}

// kill everything on the agenda that is built (directly) on 'e'.
kill_agenda(struct edge	*p)
{
	int	i;
	//printf("poisoning #%d\n", p->id);
	for(i=0;i<=highest;i++)
	{
		struct task	*t = agenda[i].start, *prev = NULL, **pp = &agenda[i].start;
		while(t)
		{
			struct edge	*e = t->edge;
			int j;
			prev = t;
			for(j=0;j<e->have;j++)
				if(e->daughters[j] == p)
				{
					//printf("killing #%d from the agenda\n", e->id);
					*pp = t->next;
					if(t->next)t->next->prev = t->prev;
					prev = t->prev;
				}
			pp = &t->next;
			t = t->next;
		}
		agenda[i].end = prev;
	}
}

struct edge	*next_agenda(int	from_start)
{
	struct task	*best;
	int		i;

	for(i=highest;i>=0;i--) if(agenda[i].start)
	{
		if(from_start || i==LEX_PRIO)	// always return LEX_PRIO items in FIFO order; otherwise retroactive packing can break (since we didn't give them a chance to pack in lexical_parse() before building on top of them)
		{
			// pop least recent edge from this queue
			best = agenda[i].start;
			agenda[i].start = best->next;
			if(best==agenda[i].end)
			{
				agenda[i].end = 0;
				highest = best->edge->prio - 1;
			}
			else highest = best->edge->prio;
		}
		else
		{
			// pop most recent edge from this queue
			best = agenda[i].end;
			agenda[i].end = best->prev;
			if(best==agenda[i].start)
			{
				agenda[i].start = 0;
				highest = best->edge->prio - 1;
			}
			else highest = best->edge->prio;
		}
		if(best->next)best->next->prev=best->prev;
		if(best->prev)best->prev->next=best->next;
		return best->edge;
	}
	return 0;
}

void	allow_edge_orth_route(struct edge	*e, int nrules, int *rules)
{
	e->north_routes++;
	e->orth_routes = slab_realloc(e->orth_routes,
		sizeof(struct orth_route)*(e->north_routes-1),
		sizeof(struct orth_route)*e->north_routes);
	e->orth_routes[e->north_routes-1].len = nrules;
	e->orth_routes[e->north_routes-1].rules = rules;
}

void sanity_check_agenda(int length)
{
	struct task *t1;
	struct queue	*lag = &agenda[LEX_PRIO];

	for(t1=lag->start;t1;t1=t1->next)
	{
		printf("#%d: %p `%s' from %d to %d\n", t1->edge->id,  t1, t1->edge->lex->word, t1->edge->from, t1->edge->to);
		assert(! (t1->edge->from<0 || t1->edge->to<0 || t1->edge->from>length || t1->edge->to>length));
	}
	printf("passed sanity\n");
}

/*

int	reduce_chart(int	length)//, char **words)
{
	extern int debug_level;
	struct task	*t1, *t2;
	struct queue	*lag = &agenda[LEX_PRIO];
	char		cover[1024];
	int		i;

	if(length<=0)return 0;

	//sanity_check_agenda(length);
	bzero(cover, length);
	for(t1=lag->start;t1;t1=t1->next)
	{
		assert(t1->edge->lex); t2 = t1;
		for(i=0;i<nchart_dependencies;i++)
		{
			struct dg	*from = dg_path(t1->edge->dg, chart_dependencies_from[i]);
			if(from)
			{
				//printf("%s selects %s\n", t1->edge->lex->word, from->xtype->name);
				for(t2=lag->start;t2;t2=t2->next)
				{
					assert(t2->edge->lex);
					struct dg	*to = dg_path(t2->edge->dg, chart_dependencies_to[i]);
					if(to && descendent_of(to->xtype->tnum, from->xtype)) {
						// XXX shouldn't that be glb() rather than descendent_of()?
						//printf(" satisfied by %s\n", t2->edge->lex->word);
						break; }
				}
				if(!t2)
				{
					//printf(" .. reduce\n");
					break;
				}
			}
		}
		if(!t2)
		{
			//printf("edge %d, lexeme %s dropped by reducer\n", t1->edge->id, t1->edge->lex->word);
			if(t1->next)t1->next->prev = t1->prev;
			if(t1->prev)t1->prev->next = t1->next;
			if(t1==lag->start)lag->start = t1->next;
			if(t1==lag->end)lag->end = t1->prev;
		}
		else
		{
			//printf("provided by %s with pred %s\n", t2->edge->lex->word, t2->edge->lex->pred->name);
			kept:
			for(i=t1->edge->from;i<t1->edge->to;i++)
			{
				//printf("%s provides %d\n", t1->edge->lex->word, i);
				//printf("`%s' from %d to %d\n", t1->edge->lex->word, t1->edge->from, t1->edge->to);
				cover[i] = 1;
			}
		}
	}

	// check that lexemes cover the whole span;
	// if not we have no chance of building a spanning analysis.
	for(i=0;i<length;i++)
		if(!cover[i])
		{
			//if(debug_level)fprintf(stderr, "NOTE: lexemes do not span position %d `%s'!\n", i, words[i]);
			if(debug_level)fprintf(stderr, "NOTE: lexemes do not span position %d!\n", i);
			itsdb_error("post-reduction lexical gap");
			return -1;
		}

	return 0;
}

*/

// can 'lt' fit in first position of rule?
static inline int	lexfirst(struct type	*lt, int	rule)
{
	extern char	**type_rftc;
	return type_rftc[rule][lt->tnum];
}

// can 'lt' fit in last position of rule?
static inline int	lexlast(struct type	*lt, int	rule)
{
	extern char	**type_rltc;
	return type_rltc[rule][lt->tnum];
}

// return 0 if there is at least one lexeme starting at 'x' that 'rule' can dominate on its lhs
int	lexrulefilt_f(int	x, int	rule)
{
	extern char	**type_rftc;
	struct task	*t;

	if(!type_rftc)return 0;
	for(t=lstart[x];t;t=t->next)
	{
		if(!(t->edge->from==x && t->edge->lex))break;
		if(lexfirst(t->edge->dg->xtype, rule))return 0;
	}
	return 1;
}

// return 0 if there is at least one lexeme ending at 'x' that 'rule' can dominate on its rhs
int	lexrulefilt_l(int	x, int	rule)
{
	extern char	**type_rltc;
	struct task	*t;
	int			s;

	if(!type_rltc)return 0;
	// for each starting position
	for(s=0;s<x;s++)
	{
		for(t=lstart[s];t;t=t->next)
		{
			if(!(t->edge->to==x && t->edge->lex))break;
			if(lexlast(t->edge->dg->xtype, rule))return 0;
		}
	}
	return 1;
}
