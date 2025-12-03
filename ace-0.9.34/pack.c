// to get back to normal: (from sept-2-2013)
// turn off MODIFD generalization
// turn off different-arity packing
// turn on rule filter
// subsumption test spends extra time now testing for generalizability

// would like to get the VPs to pack for 'Kim devours the zebra beside Abrams.'


#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>

#include	"chart.h"
#include	"lexicon.h"

#define PACKBUG(fmt,...) do {} while(0)
//#define PACKBUG printf
//#define	show_orth_leaves(x...)	"?"

#define	ENABLE_GENERALIZATION

extern int disable_generalization;
extern int debug_level;
extern unsigned int	generation;

extern int *nptries;

int equivalence_packing_only = 0;

// to determine whether the active edge component of a task is built out of frozen goods
int	contains_frozen(struct edge	*e)
{
	int	i;
	if(e->frozen)return 1;
	for(i=0;i<e->have;i++)
		if(e->daughters[i]->frozen)return 1;
	return 0;
}

static int	same_cell_daughter(struct edge *par, struct edge *dtr)
{
	int i;

	if(par==dtr)return 1;
	if(g_mode==GENERATING && !bitvec_equal(par->ep_span_bv, dtr->ep_span_bv, n_epsbv))return 0;
	if(g_mode==PARSING && (par->from != dtr->from || par->to != dtr->to))return 0;
	if(par->daughters)
	{
		for(i=0;i<par->have;i++)
			if(same_cell_daughter(par->daughters[i], dtr))return 1;
	}
	// new condition sept-2-2013... don't we need this?
	for(i=0;i<par->npack;i++)
		if(same_cell_daughter(par->pack[i], dtr))return 1;
	return 0;
}

struct dg	*restrict_copy_dg(struct dg	*dg, int for_generation)
{
	struct dg *copy;

	enable_packing(for_generation?2:1);
	copy = copy_dg(dg);
	enable_packing(0);

	return copy;
}

int identical_orth_routes(struct edge *a, struct edge *b)
{
	struct orth_route *ra, *rb;
	int					i, n = a->north_routes;

	if(a->north_routes != b->north_routes)return 0;
	if(a->north_routes == -1)return 1;
	int orth_route_cmp(const struct orth_route *ra, const struct orth_route *rb)
	{
		int i;
		if(ra->len != rb->len)return ra->len-rb->len;
		return memcmp(ra->rules, rb->rules, sizeof(int)*ra->len);
	}
	// XXX should keep these sorted ahead of time
	qsort(a->orth_routes, n, sizeof(struct orth_route), (int(*)(const void*, const void*))orth_route_cmp);
	qsort(b->orth_routes, n, sizeof(struct orth_route), (int(*)(const void*, const void*))orth_route_cmp);
	for(i=0;i<n;i++)
		if(orth_route_cmp(a->orth_routes+i, b->orth_routes+i))
			return 0;
	return 1;
}

static void record_packing(struct edge *host, struct edge *e)
{
	int	newn = host->npack + e->npack + 1;
	if(!e->daughters && !e->lex)newn--;	// don't pack e if it's a generalization edge -- but still get things packed on it.
	host->pack = slab_realloc(host->pack, host->npack*sizeof(struct edge*), newn*sizeof(struct edge*));
	if(! (!e->daughters && !e->lex))
		host->pack[host->npack++] = e;
	if(e->npack)
	{
		//printf("record_packing: got an extra %d edges packed on pack-ee\n", e->npack);
		memcpy(host->pack + host->npack, e->pack, sizeof(struct edge*)*e->npack);
		host->npack += e->npack;
		e->npack = 0;
		e->pack = NULL;
	}
}

static inline show_packing_list(struct edge	*e)
{
	int i;
	PACKBUG("#%d packing list: ", e->id);
	for(i=0;i<e->npack;i++)PACKBUG(" #%d", e->pack[i]->id);
	PACKBUG("\n");
}

static long long packcount = 0, packtry = 0, packqc = 0, packss = 0, packg = 0;
#ifdef	COPY_COUNTS
extern long long copycount, copytraverse, copysharecount, copyreentcount;
#endif

extern int gen_qc;

/*
int	upward_kill(struct edge	*edge, struct edge	*save)
{
	struct chart_cell	*c = cells + edge->from*chart_size + edge->to;
	int					i, j, k, killed = 1, pass;

	// what (I think) this is supposed to do:
	// FROST `edge', which means mark it as frozen but leave it in the chart
	// FREEZE all edges (packed or not) that are parents of `edge'
	//	which means remove it from the chart.
	//   since we are parsing each string length exhaustively before moving to longer constituents,
	//		only need to search in the same cell
	//   *ALSO*, when we freeze a parent, we must see if there are any X packed *in* that edge,
	//      and if there are, we must return those X to the agenda 
	// BUT, 'save' was the new host, so DON'T freeze it;
	//	this is non-NULL when we retroactively pack an edge into its parent
	edge->frozen = 1;
	PACKBUG("frost #%d\n", edge->id);
	// algorithm: anything with a frozen daughter gets frozen, repeat till convergence
	more: pass = 0;
	for(i=0;i<c->p_nedges;i++)
	{
		struct edge *E = c->p_edges[i];
		for(k=-1;k<E->npack;k++)
		{
			struct edge *e = (k==-1)?E:E->pack[k];
			if(e == save)continue;
			// for each edge, packed or not
			for(j=0;j<e->have;j++)
				if(e->daughters[j]->frozen == 1)
					break;
			if(j==e->have)continue;	// no frozen daughters
			// we have a frozen daughter
			// FREEZE
			PACKBUG("freeze #%d\n", e->id);
			e->frozen = 1;	// mark so future scans see this edge as frozen
			killed++;
			// remove `e' from the chart
			if(k==-1)
			{
				c->p_nedges--;
				memmove(c->p_edges+i, c->p_edges+i+1, sizeof(struct edge*) * (c->p_nedges - i));
				// new code august-2-2011;
				// when we kill an edge e because its descendent has been packed,
				// we are guaranteed that that edge will be regenerated (in more general form) off of the edge that the descendent packed into.
				// however, other edges packed on e will not be regenerated, so we have to be careful not to lose them.
				int l;
				for(l=0;l<e->npack;l++)
				{
					struct edge	*p = e->pack[l];
					if(!edge_descendent(edge, p))
					{
						// make sure everything built on `p' from the first time it entered the chart dies
						// since p is packed, there is nothing *in* the chart built on p,
						// but there may be stuff on the agenda built on p.
						// since we are putting p back on the agenda,
						// we can't leave a marker for all future edges built on p to be killed.
						// we have to do it now.
						kill_agenda(p);
						//printf("returning packed edge #%d to agenda on upward_kill\n", e->pack[l]->id);
						p->frozen = 0;
						p->frosted = 0;
						add_agenda(p);
					}
					else {} // 'p' would have been killed by a different pass of this function
				}
				goto more;
			}
			else
			{
				E->npack--;
				memmove(E->pack+k, E->pack+k+1, sizeof(struct edge*) * (E->npack - k));
				k--;
				continue;
			}
		}
	}
	if(pass)goto more;
	//printf("upward_kill'd %d edges built on #%d\n", killed, edge->id);
	return killed;
}*/

int	generalize_pack_edge(struct edge	*edge)
{
	struct chart_cell	*c = cells + edge->from*chart_size + edge->to;
	printf("thinking about how to pack #%d [%d passives in cell]\n", edge->id, c->p_nedges);
	if(c->p_nedges == 0)return 0;

	struct edge	*existing = c->p_edges[0];

	int	ssd, fw=1, bk=1;
	ssd = equivalent_dg(existing->dg, edge->dg, fw, bk, 0);
	if(ssd == 1 || ssd == 2)
	{
		// existing susumes new edge
		record_packing(existing, edge);
		printf("#%d packs INTO existing #%d\n", edge->id, existing->id);
		return 1;
	}
	if(ssd == -1)
	{
		// new edge subsumes existing edge
		assert(!existing->frozen);
		record_packing(edge, existing);
		c->p_nedges = 0;
		printf("#%d SUBSUMES existing #%d (so replaces it in the chart)\n", edge->id, existing->id);
		return 0;
	}

	// no subsumption relation; invent a new more general edge!
	struct edge	*invent = slab_alloc(sizeof(struct edge));
	bzero(invent, sizeof(*invent));

	enable_packing(1);
	enable_trim(1);
	invent->dg = generalize(existing->dg, edge->dg);
	enable_packing(0);
	enable_trim(0);

	invent->from = edge->from;
	invent->to = edge->to;
	invent->id = next_eid();
	invent->have = edge->have;
	invent->need = edge->need;
	invent->qc = extract_qc(invent->dg);

	printf("invented a new generalized edge #%d [ subsumes #%d and #%d ]\n", invent->id, existing->id, edge->id);
	print_dg(invent->dg);
	printf("\n");

	record_packing(invent, edge);
	record_packing(invent, existing);
	c->p_nedges = 0;
	add_agenda(invent);
	return 1;
}

int block(struct edge	*e, int	freeze, int	remove)
{
	int	destructive = 0;
	//PACKBUG(">> block(#%d, %d, %d)\n", e->id, freeze, remove);
	if((!e->frozen || freeze) && !remove)
	{
		if(freeze && !(e->frozen && !e->frosted))
			PACKBUG("FREEZING edge #%d; expect to pick it up later.\n", e->id);

		if(freeze) { e->frozen = 1; e->frosted = 0; }
		else { e->frozen = 1; e->frosted = 1; }
	}
	else if(remove)e->frozen = 1;	// mark as frozen so that edges built on this that are still on the agenda get discarded
	// for each of `e's parents:
	struct chart_cell	*c = cells + e->from*chart_size + e->to;
	int i, j, l;
	retry:
	for(i=0;i<c->p_nedges;i++)
	{
		struct edge	*P = c->p_edges[i];
		for(l=-1;l<P->npack;l++)
		{
			struct edge	*p = (l==-1)?P:P->pack[l];
			for(j=0;j<p->have;j++)
				if(p->daughters && p->daughters[j] == e)
				{
					if(l == -1)
					{
						if(!remove)
						{
							if(block(p, 1, 0))
							{
								destructive = 1;
								goto retry;
							}
						}
						else
						{
							PACKBUG("EXPUNGING edge #%d\n", p->id);
							c->p_nedges--;
							memmove(c->p_edges+i,c->p_edges+i+1,sizeof(struct edge*)*(c->p_nedges-i));
							destructive = 1;
							block(p, 1, 1);
							goto retry;
						}
					}
					else
					{
						// trying to FREEZE an edge that is already on a packing list.
						// the only reason we keep FROZEN edges around in the main chart
						// is so they can save us work by subsuming other edges that come along
						// until they are gobbled up by the new subsuming edge we know is coming.
						// packed edges aren't eligible to subsume other edges,
						// so the best thing to do is just delete this edge now.
						P->npack--;
						PACKBUG("EXPUNGING edge #%d from #%d\n", p->id, P->id);
						memmove(P->pack+l, P->pack+l+1, sizeof(struct edge*)*(P->npack-l));
						destructive = 1;
						show_packing_list(P);
						l--;
						if(P->npack == 0 && !P->daughters && !P->lex)
						{
							// just killed off the last real packed daughter of a generalization edge.
							// we can't leave the generalization edge in the chart,
							// since it no longer represents valid combinatorics, and could waste effort.
							// plan: expunge the generalization host edge and everything built on it.
							c->p_nedges--;
							memmove(c->p_edges+i,c->p_edges+i+1,sizeof(struct edge*)*(c->p_nedges-i));
							destructive=1;
							block(P,0,1);
							goto retry;	// chart cell probably got reorganized... restart the loop.
						}
					}
					break;
				}
		}
	}
	//PACKBUG("<< block(#%d, %d, %d)\n", e->id, freeze, remove);
	return destructive;
}

void	clear_carcs_and_copy(struct dg	*d)
{
	d = dereference_dg(d);
	if(!d->carcs && !d->copy)return;
	int i;
	struct dg	**darcs = DARCS(d);
	d->carcs = NULL;
	d->copy = NULL;
	for(i=0;i<d->narcs;i++)
		clear_carcs_and_copy(darcs[i]);
}

int	pack_edge(struct edge	*edge)
{
	/*if(edge->to > edge->from + 1)	// pack under generalization for non lexical spans
		// the generalization system doesn't deal with lexical rule chain requirements yet
		// also, cycles can emerge from unary rules. what to do there?
		return generalize_pack_edge(edge);*/

	struct chart_cell	*c = cells + edge->from*chart_size + edge->to;
	struct edge			*h, **candidates;
	int			i, ssd, ncandidates;
	int			already_packed = 0;

	//if(g_mode==PARSING && edge->neps==-1)return 0;	// for now, never pack Dublin edges.

	struct edge	*generalizable_host = NULL;

	int	would_pack_as_ssd = 0;

#ifdef	COPY_COUNTS
	packcount++;
#endif

	PACKBUG("trying to pack #%d `%s' somewhere\n", edge->id, show_orth_leaves(edge));

	int	packing_active = (edge->have != edge->need)?1:0;

	static struct edge	**generalization_candidates = NULL;
	static int			ageneralization_candidates = 0;
	int ngeneralization_candidates = 0;
	void save_generalization_candidate(struct edge	*c)
	{
		if(ngeneralization_candidates + 1 > ageneralization_candidates)
		{
			ageneralization_candidates = 5 + 1.5*ageneralization_candidates;
			generalization_candidates = realloc(generalization_candidates, sizeof(struct edge*)*ageneralization_candidates);
		}
		generalization_candidates[ngeneralization_candidates++] = c;
	}

	try_more:
	candidates = (edge->have==edge->need)?c->p_edges:(edge->rule->rtl?c->ar_edges:c->al_edges);
	ncandidates = (edge->have==edge->need)?c->p_nedges:(edge->rule->rtl?c->ar_nedges:c->al_nedges);
	for(i=0;i<ncandidates && (h=candidates[i]);i++)
	{
		// sept-02-2013 -- we were refusing to pack edges of different arity.  was there a good reason?
		//if( (h->need - h->have) == (edge->need - edge->have)    //h->have == edge->have && h->need == edge->need
		if( h->have == edge->have && h->need == edge->need
		&& (g_mode != GENERATING || bitvec_equal(h->ep_span_bv, edge->ep_span_bv, n_epsbv))
			)
		{
			// XXX shouldn't we require identical accessibility bitmaps?
			int	fw = 1, bk = 1, gz = 1;
			if(edge == h)continue;	// if we retroactively packed an existing passive into 'edge', then 'edge' is now in the chart, so be careful
			// if nothing is subsumed by both rule schemata,
			// then refinements of them cannot be in subsumption relations
			// ... but generalizations can stand in subsumption, and non-subsuming edges can generalize.
			//if(edge->rule && h->rule)
			//	if(!check_srf(edge->rule, h->rule))continue;

			// active edges need to be looking the same direction to pack
			if(packing_active && h->rule->rtl != edge->rule->rtl)continue;

			packtry++;
#ifndef	GEN_SUBSUMPTION_QC
			if(!gen_qc && !packing_active && equiv_quickcheck(h->qc, edge->qc, &fw, &bk, &gz))continue;
#endif
			packqc++;

			PACKBUG("would like to pack #%d `%s' and #%d `%s'!\n", edge->id, show_orth_leaves(edge), h->id, show_orth_leaves(h));
			if(!identical_orth_routes(h, edge))continue;

			if(!edge->dg)
				if(recall_hyper(edge))
				{
					PACKBUG("whoops! edge was hyperpassive and vanished\n");
					return 0;
				}
			if(!h->dg)
				if(recall_hyper(h))
				{
					PACKBUG("whoops! host was hyperpassive and vanished\n");
					continue;
				}

			if(!fw && !bk)
			{
				if(gz && !h->frozen && !(g_mode==PARSING && h->neps==-1))save_generalization_candidate(h);
				continue;
			}

#ifdef	RULE_STATS
			if(edge->ntries==0)
			{
				if(edge->rule)nptries[edge->rule->rnum]++;
				else nptries[nrules]++;
			}
			edge->ntries++;
			if(h->ntries==0)
			{
				if(h->rule)nptries[h->rule->rnum]++;
				else nptries[nrules]++;
			}
			h->ntries++;
#endif

			//ssd = equivalent_dg(h->dg, edge->dg, fw, bk, 0);
			ssd = equivalent_dg(h->dg, edge->dg, 1, 1, 0);
			assert(!(ssd == -1 && !bk));
			if(ssd == 3 || ssd == -3)
			{
				//printf("potential to pack #%d and #%d with generalization even though they don't stand in strict subsumption\n", h->id, edge->id);
				ssd = 0;
				if(!h->frozen)
				{
					generalizable_host = h;
					packg++;
				}
			}

			if(equivalence_packing_only && ssd != 2)ssd = 0;
			if(ssd)packss++;
			if(ssd && h->lex && edge->lex)PACKBUG("packing lex `%s' and lex `%s'\n", edge->lex->word, h->lex->word);
			PACKBUG("ssd = %d ; h->frozen = %d\n", ssd, h->frozen);
			//if(!ssd)subsume_backtrace();
			//if(ssd == 1 || (ssd == 2 && !h->frozen))
			if((ssd == 1 || ssd == 2) && !h->frozen)
			{
				// forward packing
				// h subsumes edge
				if(g_mode==PARSING && edge->neps==-1)
					continue;	// don't let dublin edges be packed into other edges
				if(same_cell_daughter(edge, h))
				{
					// h is a descendent of edge
					// packing would cause a loop in unpacking
					// could happen if a rule produces a result
					// that is compatible with but more specific than
					// a descendent with the same span.
					// sounds like poor grammar engineering, but conceivable.
					// with ERG-1004 on 'CSLI' at least, this never happens.

					// BUT it does happen with ERG-1010 on the following sentence:
					// A bunkhouse is a hostel or barracks-like building that historically was used to house working cowboys on ranches in North America.
					// hd_optcomp_c makes an infinite loop on [hostel or barracks- like]
					// yuck.
					if(ssd == 2)
					{
						// mother is completely equivalent to daughter.
						// that is a loop in the grammar.
						fprintf(stderr, "WARNING: grammar rule `%s' is loopy\n", edge->rule->name);
						fprintf(stderr, "WARNING: edge #%d [%s] == edge #%d [%s]\n", edge->id, edge->rule->name, h->id, h->rule->name);
						// pretend we packed it, but actually just discard it.
						return 1;
					}
					PACKBUG("blocked same-cell-daughter packing\n");
					continue;
				}
				// mark the subsumed edge as frosted so that we refuse to build anything on it that may be lurking in the agenda.
				// this can't happen normally, since `edge' just came off the agenda itself and hasn't been given a chance to combine.
				// it *can* happen when `edge' is a result from lexical parsing that we are just now putting in the chart
				// note: it must be frosted rather than frozen, since it is still *valid*
				edge->frozen = 1; edge->frosted = 1;
				PACKBUG("packed #%d `%s' in #%d `%s'!\n", edge->id, show_orth_leaves(edge), h->id, show_orth_leaves(h));
				//printf("host: "); print_dg(h->dg); printf("\n");
				//printf("pack: "); print_dg(edge->dg); printf("\n");
				//printf("EQUIV = %d\n", equivalent_dg(h->dg, edge->dg));
				record_packing(h, edge);
				show_packing_list(h);
				return 1;
			}
			else if((ssd == -1 || ssd == 2) && 1 && !packing_active)
			{
				int was_frozen = h->frozen;
				// retroactive packing
				// edge subsumes h
				if(same_cell_daughter(edge, h))
				{
					// h is a descendent of edge
					PACKBUG("blocked same-cell-daughter retroactive packing\n");
					continue;
				}
				if(g_mode==PARSING && h->neps==-1)
				{
					// h is a Dublin robust parse tree guide; there is already a full tree in the agenda built on it which we don't really want to cancel or generalize more.
					continue;
				}
				if(!already_packed)
				{
					// replace 'h' by 'edge' in the chart before upward_kill() changes the chart around
					c->p_edges[i] = edge;
					PACKBUG("reverse packed #%d `%s' in #%d `%s'!\n", h->id, show_orth_leaves(h), edge->id, show_orth_leaves(edge));
					PACKBUG(" ... and edge already had %d packers\n", edge->npack);
					//printf("host: "); print_dg(edge->dg); printf("\n");
					//printf("pack: "); print_dg(h->dg); printf("\n");
					// promote what's packed on 'h' to be packed on 'edge'
					if(!edge->npack)
					{
						edge->npack = h->npack;
						edge->pack = h->pack;
					}
					else
					{
						// happens for generalization packing.
						int	newnpack = edge->npack + h->npack;
						struct edge	**newpack = slab_alloc(sizeof(struct edge*) * newnpack);
						memcpy(newpack, edge->pack, sizeof(struct edge*) * edge->npack);
						memcpy(newpack + edge->npack, h->pack, sizeof(struct edge*) * h->npack);
						edge->npack = newnpack;
						edge->pack = newpack;
					}
				}
				else
				{
					// delete 'h' from the chart
					c->p_nedges--;
					ncandidates--;
					memmove(c->p_edges+i, c->p_edges+i+1, sizeof(struct edge*)*(c->p_nedges-i));
					i--;
					PACKBUG("claimed #%d also\n", h->id);
					if(h->npack)
					{
						// promote what's packed on 'h' to be packed on 'edge'
						edge->pack = memcpy(slab_alloc(sizeof(struct edge*)*(edge->npack+h->npack)), edge->pack, sizeof(struct edge*)*edge->npack);
						memcpy(edge->pack+edge->npack, h->pack, sizeof(struct edge*)*h->npack);
						edge->npack += h->npack;
					}
				}
				h->npack = 0;
				h->pack = 0;
				// frozen edges don't need to be put onto packing lists... they were there as placeholders but are irrelevant to unpacking.
				// also, generalization edges don't need to be put onto packing lists... they are also irrelevant to unpacking.
				if(!(h->frozen && !h->frosted) && !(h->daughters==NULL && h->lex==NULL))
				{
					//printf(" ... packing it too\n");
					//h->frosted = 1;
					record_packing(edge, h);
				}
				already_packed = 1;
				if(h->built_on)
				{
					//printf("upkilling #%d to pack it in #%d\n", h->id, edge->id);
					int destructive = block(h, 0, 0);
					if(destructive)
					{
						// now recompute what 'i' in p_edges we are on, since block() can change that... yuck.
						// might have to rewind to 'edge', if 'h' isn't there anymore...
						assert(candidates == c->p_edges);
						for(i=0;i<c->p_nedges;i++)
							if(h == c->p_edges[i] || edge == c->p_edges[i])break;
						assert(i != c->p_nedges);
						ncandidates = c->p_nedges;
					}
				}
				h->built_on = 0;
				// keep going!
				show_packing_list(edge);
			}
		}
	}
	if(already_packed)return 2;

	// failed to pack under strict subsumption.
#ifdef	ENABLE_GENERALIZATION
	if(edge->have == edge->need && g_mode == PARSING && !edge->north_routes && !disable_generalization && edge->neps!=-1)
	{
		// we kept a list of edges whose quickcheck suggested they may generalize
		for(i=0;!generalizable_host && i<ngeneralization_candidates;i++)
		{
			struct edge	*h = generalization_candidates[i];
			int ssd = equivalent_dg(h->dg, edge->dg, 1, 1, 0);
			if(ssd == 3 || ssd == -3)
				generalizable_host = h;
		}
		if(generalizable_host)
		{
			// but did find a host that could pack with 'edge' under slight generalizations
			int	ssd = equivalent_dg(edge->dg, generalizable_host->dg, 1, 1, 1);
			struct edge	*from;
			if(ssd == 3)from = edge;
			else if(ssd == -3)from = generalizable_host;
			else
			{
				fprintf(stderr, "relationship between edge and recorded candidate generalization host = %d\n", ssd);
				assert(!"no generalized subsumption when I thought there was");
			}
			//printf("generalization packing: got ssd = %d\n", ssd);
			clear_carcs_and_copy(from->dg);
			extern int discard_inappropriate_types_during_copy;
			discard_inappropriate_types_during_copy = 1;
			struct dg	*gdg = finalize_tmp(from->dg, 0);
			assert(gdg != NULL);
			discard_inappropriate_types_during_copy = 0;

			//printf("#%d's dag:\n", edge->id);print_dg(edge->dg);printf("\n");
			//printf("#%d's dag:\n", generalizable_host->id);print_dg(generalizable_host->dg);printf("\n");
			//printf("new dag:\n");print_dg(gdg);printf("\n");

			struct edge	*ge = slab_alloc(sizeof(*ge));
			memcpy(ge, from, sizeof(*ge));
			ge->frozen = ge->frosted = 0;
			ge->id = next_eid();
			ge->used = 0;
			ge->dg = gdg;
			ge->qc = extract_qc(gdg);
			// pack everything packed on edge onto ge
			ge->npack = edge->npack;
			ge->pack = slab_alloc(sizeof(struct edge*) * (ge->npack+1));
			memcpy(ge->pack, edge->pack, sizeof(struct edge*)*edge->npack);
			// pack edge itself onto ge, unless edge is a generalization
			if(edge->daughters || edge->lex)
				ge->pack[ge->npack++] = edge;
			edge->npack = 0;
			edge->pack = NULL;
			ge->lex = NULL;
			ge->daughters = NULL;
			// when we try to pack 'ge', we will retroactively pick up generalizable_host -- and maybe others.
			PACKBUG("hallucinated #%d which packs #%d and should pick up #%d\n", ge->id, edge->id, generalizable_host->id);
			//printf("verifying that gdg subsumes #%d ->dg\n", edge->id);
			//assert(1 == equivalent_dg(gdg, edge->dg, 1, 1, 0));
			//printf("verifying that gdg subsumes #%d ->dg\n", generalizable_host->id);
			//assert(1 == equivalent_dg(gdg, generalizable_host->dg, 1, 1, 0));
			//fflush(stdout);
			// NEW provision added Feb-29-2018 to address bug found when parsing:
			// Until Version 2.1 (⌊/Peach/⌋), Fruit was an ⌊>open source>⌋ engine.
			// it turns out we should be block()'ing the host!
			// reason: we don't want more stuff to be built on it
			//    before the generalized edge comes and picks it up.
			// however, we also don't want block()'ing it to STOP the generalized edge from picking it up...
			if(generalizable_host->built_on)
				block(generalizable_host, 0, 0);
			add_agenda(ge);
			return 1;	// report that 'edge' is packed.
		}
	}
#endif

	return 0;
}

void packing_report()
{
#ifdef	COPY_COUNTS
	fprintf(stderr, "NOTE: %lld packings (%.1f%% success), %lld copy() calls, %lld copy() reentrancies, %lld copy() allocations, %lld copy() shares = %.1f%%\n", packcount, 100*(float)packcount / packtry,
		copytraverse, copyreentcount, copycount, copysharecount, 100*(float)copysharecount / (copycount+copysharecount));
#endif
	if(debug_level)
	{
		fprintf(stderr, "NOTE: %lld subsumption tests; qc filters %.1f%% leaving %lld, of which ss passes %.1f%% = %lld ; %.1f%% = %lld generalizable\n",
			packtry, 100 - 100*(float)packqc/packtry, packqc, 100*(float)packss/packqc, packss, 100*(float)packg/packqc, packg);
	}
}

// once forest creation is complete,
// take generalization edges G that pack edges [x,y,z] and replace them with 
// a real edge X that packs [y, z].
// it doesn't matter (?) whether X actually subsumes y and z -- we're just representing choice points now.
struct edge	*compact_generalization_edge(struct edge	*g)
{
	int i, j;
	// remove any other generalization edges G' that are packed on G; anything that was at one point packed on G' should have been promoted to packed directly on G when G' was picked up.
	//printf("compacting g-edge #%d, which has %d packers\n", g->id, g->npack);
	for(i=j=0;i<g->npack;i++)
		if(g->pack[i]->daughters || g->pack[i]->lex)
		{
			g->pack[j++] = g->pack[i];
			//printf(" ... kept packed #%d\n", g->pack[i]->id);
		}
		else
		{
			if(g->pack[i]->npack)
			{
				fprintf(stderr, "g-edge #%d had a pack-ee g-edge #%d which had %d pack-ees\n", g->id, g->pack[i]->id, g->pack[i]->npack);
				assert(!"not reached");
			}
		}
	g->npack = j;

	// there better be at least one (two, really?) real edge here...
	if(g->npack == 0)
	{
		fprintf(stderr, "g-edge #%d had no real pack-ees\n", g->id);
		assert(!"not reached");
	}
	struct edge	*x = g->pack[0];
	x->pack = g->pack+1;
	x->npack = g->npack-1;
	x->frozen = x->frosted = 0;	// edges picked up by generalization edges are frequently retroactively packed; when we pop it back out to the main chart, remove the frosting

	// also make x look like g in terms of AVM shape, so that testing against x's AVM is a real proxy for the ones that we claima are subsumed by it
	x->dg = g->dg;
	x->qc = g->qc;

	// ... but do NOT modify g->pack or g->npack; edges built in g need to know how to unpack.
	return x;
}

void	compact_generalization_edges()
{
	int i;
	// first, take the generalization edges out of the chart, promoting their first real pack-ee
	for(i=0;i<chart_size*chart_size;i++)
	{
		struct chart_cell	*c = &cells[i];
		int j, l;
		for(j=0;j<c->p_nedges;j++)
		{
			struct edge	*e = c->p_edges[j];
			if(e->daughters == NULL && !e->lex)
			{
				// generalization edge
				c->p_edges[j] = compact_generalization_edge(e);
			}
			for(l=0;l<e->npack;l++)
			{
				struct edge	*p = e->pack[l];
				if(p->daughters == NULL && !p->lex)
				{
					// generalization edge
					fprintf(stderr, "ERROR: edge #%d packed g-edge #%d\n", e->id, p->id);
					assert(!"ERROR: found a generalization edge on a packing list... oops.");
				}
			}
		}
	}

	// next, fix references to generalization edges to point instead to their first real pack-ee.
	for(i=0;i<chart_size*chart_size;i++)
	{
		struct chart_cell	*c = &cells[i];
		int j, k, l;
		for(j=0;j<c->p_nedges;j++)
		{
			struct edge	*E = c->p_edges[j];
			for(l=-1;l<E->npack;l++)
			{
				struct edge	*e = (l==-1)?E:E->pack[l];
				assert(! (e->daughters == NULL && !e->lex));
				if(e->frozen && !e->frosted)
				{
					// if we run out of RAM during forest creation,
					// we might fail to pick up a frozen edge.
					// don't worry about vapid generalization daughters on those;
					// they'll be ignored anyway.
					continue;
				}
				for(k=0;k<e->have;k++)
				{
					struct edge	*d = e->daughters[k];
					if(d->daughters == NULL && !d->lex)
					{
						if(d->npack == 0)
						{
							fprintf(stderr, "ERROR: edge #%d had generalization daughter #%d which packs nothing\n", e->id, d->id);
							exit(-1);
						}
						e->daughters[k] = d->pack[0];
					}
				}
			}
		}
	}
}
