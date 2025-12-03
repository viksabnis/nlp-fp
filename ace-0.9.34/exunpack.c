#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<stdarg.h>

#include "dag.h"
#include "chart.h"
#include "lexicon.h"
#include "maxent.h"
#include "unpack.h"
#include "mrs.h"
#include	"token.h"
#include	"transfer.h"

struct tree_list
{
	int	n;
	struct hypothesis	**list;
};

struct tree_list	singleton_eue(struct edge	*e)
{
	struct tree_list	tl;
	tl.n = 1;
	tl.list = slab_alloc(sizeof(struct hypothesis*));
	tl.list[0] = slab_alloc(sizeof(struct hypothesis));
	bzero(tl.list[0], sizeof(struct hypothesis));
	tl.list[0]->edge = e;
	tl.list[0]->arity = 0;
	tl.list[0]->rhslist = NULL;
	if(e->rule)tl.list[0]->dg = e->rule->dg;
	else 
	{
		if(g_mode == GENERATING)
		{
			// generator lexeme.  don't put the specialized RELS list in.
			tl.list[0]->dg = lexical_dg(e->lex, 0);
		}
		else tl.list[0]->dg = e->dg;
	}
	if(!e->have)build_hypothesis_surface(tl.list[0]);
	return tl;
}

struct tree_list	instantiate_eue(struct edge	*e, struct tree_list	*dtl, int	d)
{
	if(d == e->have)return singleton_eue(e);
	struct tree_list	sub = instantiate_eue(e, dtl, d+1);
	struct tree_list	dtr = dtl[d];
	int	i, j;
	struct tree_list	res;
	res.list = slab_alloc(sizeof(struct hypothesis*) * dtr.n * sub.n);
	res.n = 0;
	for(i=0;i<dtr.n;i++)
	{
		for(j=0;j<sub.n;j++)
		{
			struct hypothesis	*sh = sub.list[j];
			//printf("sh->dg >%d =:\n", d);print_dg(sh->dg);printf("\n");
			if(unify_dg_tmp(dtr.list[i]->dg, sh->dg, d))
			{
				forget_tmp();
				continue;
			}
			else
			{
				struct dg	*dg = finalize_tmp(sh->dg, (d==0)?1:0);
				if(!dg)continue;	// cycle failure
				struct hypothesis	*h = slab_alloc(sizeof(*h));
				bzero(h, sizeof(*h));
				h->dg = dg;
				h->edge = e;
				h->arity = sh->arity+1;
				h->rhslist = slab_alloc(sizeof(struct hypothesis*)*h->arity);
				h->rhslist[0] = dtr.list[i];
				memcpy(h->rhslist+1, sh->rhslist, sizeof(struct hypothesis*)*sh->arity);
				res.list[res.n++] = h;
			}
		}
	}
	if(d==0)
		for(i=0;i<res.n;i++)
			build_hypothesis_surface(res.list[i]);
	return res;
}

extend_tree_list(struct tree_list	*L, struct tree_list	ex)
{
	L->list = slab_realloc(L->list, sizeof(void*)*L->n, sizeof(void*)*(L->n+ex.n));
	memcpy(L->list+L->n, ex.list, sizeof(void*)*ex.n);
	L->n += ex.n;
}

struct tree_list	exhaustive_unpack_edge(struct edge	*e)
{
	if(e->unpack)return *(struct tree_list*)e->unpack;
	if(e->frozen && !e->frosted)
	{
		struct tree_list	tl = {.n = 0, .list = NULL};
		e->unpack = slab_alloc(sizeof(tl));
		*(struct tree_list*)(e->unpack) = tl;
		//printf("EUE edge #%d was frozen\n", e->id);
		return tl;
	}
	struct tree_list	dtl[e->have];
	int	i, j;
	for(i=0;i<e->have;i++)
	{
		dtl[i] = exhaustive_unpack_edge(e->daughters[i]);
		for(j=0;j<e->daughters[i]->npack;j++)
			extend_tree_list(&dtl[i], exhaustive_unpack_edge(e->daughters[i]->pack[j]));
	}
	struct tree_list	tl = instantiate_eue(e, dtl, 0);
	e->unpack = slab_alloc(sizeof(tl));
	*(struct tree_list*)(e->unpack) = tl;
	//printf("EUE edge #%d has %d instantiated trees\n", e->id, tl.n);
	return tl;
}

extern int debug_level;

int	exhaustive_unpack(struct chart_cell	*cell, int (*process)(struct hypothesis *hyp, struct mrs *mrs))
{
	int	i, total = 0;
	int ninsthyps = 0;
	for(i=0;i<cell->p_nedges;i++)
	{
		struct edge	*edge = cell->p_edges[i];
		if(debug_level > 2)printf("checking whether %d can be root\n", edge->id);
		if( (g_mode!=GENERATING || ep_span_is_root(edge->ep_span_bv, edge->neps)) && is_root(edge->dg) && !edge->frozen )
		{
			if(debug_level > 1)printf("edge #%d can be root...\n", edge->id);
			int	j;
			for(j=-1;j<edge->npack;j++)
			{
				// for each potentially root packed edge...
				struct edge *e = (j==-1)?edge:edge->pack[j];
				if(e->frozen && !e->frosted)continue;
				if(!is_root(e->dg))continue;
				struct tree_list	tl = exhaustive_unpack_edge(e);
				int k;
				for(k=0;k<tl.n;k++)
				{
					struct hypothesis	*h = tl.list[k];
					struct dg	*dg = h->dg;
					ninsthyps++;
					if(is_root(dg))
					{
						struct mrs	*m = extract_mrs(dg);
						if(check_idioms(dg, m))
						{
							total += 1;
							if(g_mode == GENERATING)
								fixup_generator_string(h);
							process(h, m);
							//fprintf(stderr, "I don't know how to call process() on these hypotheses yet.\n");
						}
					}
				}
			}
		}
	}
	//fprintf(stderr, "NOTE: %d trees reconstructed\n", ninsthyps);
	return total;
}
