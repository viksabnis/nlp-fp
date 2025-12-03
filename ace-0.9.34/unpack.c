#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<stdarg.h>
#include	<wchar.h>
#include	<wctype.h>
#include	<setjmp.h>
#include	<math.h>

#include "dag.h"
#include "chart.h"
#include "lexicon.h"
#include "maxent.h"
#include "unpack.h"
#include "mrs.h"
#include	"token.h"
#include	"transfer.h"
#include	"unicode.h"
#include	"freeze.h"
#include	"conf.h"
#include	"dag-provenance.h"
#include	"morpho.h"
#include	"profiler.h"

//#define	DEBUG	printf
#define	DEBUG(fmt, ...)	do {} while(0)
#define	DEBUG2(fmt, ...)	do {} while(0)

extern int enable_token_avms;

int derivations_include_roots = 0;
int format_udx = 0;

extern int max_unpack_megabytes;
//#define	MAX_UNPACK_CHUNKS	70000
//#define	MAX_UNPACK_CHUNKS	7000
//#define	MAX_UNPACK_CHUNKS	1500

extern int debug_level, inhibit_pack;

unsigned long long	ndecomposed, totaldecompositions;

static jmp_buf	out_of_memory_jump;

int	max_grandparenting = 3;
int use_packed_edge_ids = 0;

int	total_hyps;

//struct profiler	*gec_profiler;
//struct profiler	*score_profiler;

struct context_unpack_info	*get_edge_cui(struct edge	*e, struct scoring_ancestry	ancestry);
struct scoring_ancestry	compute_sub_ancestry(struct scoring_ancestry	panc, struct edge	*edge);
struct hypothesis	*get_cui_hypothesis(struct context_unpack_info	*cui, int	rank);
void	set_cui_hypothesis(struct context_unpack_info	*cui, int	rank, struct hypothesis	*h);
//int	cui_has_hypothesis(struct context_unpack_info	*cui, struct hypothesis	*hyp);

static inline char* edge_sign(struct edge *e)
{
	if(!e)return NULL;
	if(!e->have)return e->lex->lextype->name;
	else return e->rule->name;
}

void score_hypothesis(struct hypothesis *h)
{
	int i;
	h->score = 0;
	if(h->arity)
	{
		// 'h' is a rule node
		// XXX TODO make this support higher arity rules
		char	*lhs_sign = edge_sign(h->edge);
		char	*rhs0_sign = edge_sign(h->rhslist[0]->edge);
		char	*rhs1_sign = (h->arity>1)?edge_sign(h->rhslist[1]->edge):NULL;
		int		key_arg = h->edge->rule->rtl;
		float	score;

		int has_lexical_dtrs = 0;
		for(i=0;i<h->arity;i++)if(h->rhslist[i]->arity == 0)has_lexical_dtrs = 1;
		//start_and_alloc_profiler(&score_profiler, "score-hypothesis", unpacking_profiler, NULL);
		if(has_lexical_dtrs)
		{
			score = maxent_score(lhs_sign, rhs0_sign, rhs1_sign, key_arg, &h->ancestry);
		}
		else
		{
			int	lhs_rnum = h->edge->rule->rnum;
			int	rhs0_rnum = h->rhslist[0]->edge->rule->rnum;
			int	rhs1_rnum = (h->arity > 1)?h->rhslist[1]->edge->rule->rnum:-1;
			//float verify = maxent_score(lhs_sign, rhs0_sign, rhs1_sign, key_arg, &h->ancestry);
			score = maxent_score_ro(lhs_rnum, rhs0_rnum, rhs1_rnum, &h->ancestry);
			//printf("score  = %f\n", score);
			//printf("verify = %f\n", verify);
			//assert(score == verify);
		}
		//stop_profiler(score_profiler, 1);
		h->score += score;

		float	lexical_daughter_scores = 0;

		for(i=0;i<h->arity;i++)
		{
			h->score += h->rhslist[i]->score;
			if(h->rhslist[i]->arity == 0)
				lexical_daughter_scores += h->rhslist[i]->score;
		}

		if(!h->dec->is_scored)
		{
			h->dec->is_scored = 1;
			h->dec->local_score = score + lexical_daughter_scores;
			h->dec->all_unpackings_z = exp((double)h->dec->local_score);
			//fprintf(stderr, "local Z at #%d dec %p = %f\n", h->edge->id, h->dec, h->dec->all_unpackings_z);
			struct scoring_ancestry	sub_ancestry = compute_sub_ancestry(h->ancestry, h->edge);
			for(i=0;i<h->arity;i++)
			{
				double	sub_z = 0;
				struct hypothesis	*sub_h = h->rhslist[i];
				struct edge	*sub_e = sub_h->edge;
				if(sub_h->arity == 0)continue;	// we already collected a score for lexical daughters
				struct context_unpack_info	*subcui = get_edge_cui(sub_e, sub_ancestry);
				int j;
				for(j=0;j<subcui->ndecs;j++)
				{
					// if we short-circuit know that there are no unifiable hypotheses
					// of a decomposition, we might have never called new_hypothesis() for that decomposition, and thus in turn have never scored the decomposition.
					// leaving the Z terms out for that decomposition doesn't seem wrong to me just now?
					if(subcui->decs[j].is_scored == 0)
						continue;

					//fprintf(stderr, "read dec %p Z %f\n", subcui->decs+j, subcui->decs[j].all_unpackings_z);
					sub_z += subcui->decs[j].all_unpackings_z;
				}
				//fprintf(stderr, " sub_z for dtr %d = %f\n", i, sub_z);
				h->dec->all_unpackings_z *= sub_z;
			}
			//fprintf(stderr, "final Z for dec %p = %f\n", h->dec, h->dec->all_unpackings_z);
		}
	}
	else if(g_mode != GENERATING) // FIXME: realization ranking doesn't have access to surface forms because we have no tokens...
	{
		// 'h' is a leaf/lexeme node
		// construct the cannonical surface form
		//if(!enable_token_avms)return;
		extern char	current_sentence[];
		char	surface[1024], *sp = surface;
		int	i;
		struct edge	*e = h->edge;
		struct lexeme	*lex = e->lex;
		assert(lex);
		sp += sprintf(sp, "\"");
		for(i=0;i<lex->stemlen;i++)
		{
			struct token	*tok = (struct token*)e->daughters[i];
			tok->used = 1;	// any token that gets reached in scoring is part of a result
			if(strlen(tok->string) + (sp-surface) > 1000)return;
			if(tok->cfrom==-1 || tok->cto==-1)return;
			// if we wanted to preserve capitalization, we would do:
			//sp += sprintf(sp, "%s%.*s", i?" ":"", tok->cto-tok->cfrom, current_sentence + tok->cfrom);
			// since we (in general, except names?) don't, we do:
			sp += sprintf(sp, "%s%s", i?" ":"", tok->string);
		}
		sp += sprintf(sp, "\"");
		//printf("should score surface `%s'\n", surface);
		char	*lhs_sign = edge_sign(e);
		h->score = maxent_score(lhs_sign, surface, NULL, 0, &h->ancestry);
		//printf("got score: %f\n", h->score);
	}
}

/*  high arity safe after this mark */

struct decomposition *decompose_edge(struct edge	*edge, int *Ndecompositions)
{
	int	n = 1, i, j, orign;
	struct decomposition *dec, *d;

	if(!edge->lex && !edge->daughters)
	{
		// generalization edge; has no unpackings itself
		*Ndecompositions = 0;
		return NULL;
	}

	ndecomposed++;
	if(edge->frozen && !edge->frosted)
	{
		// shouldn't get here because we delete frozen edges from the chart
		// and don't build on top of them
		fflush(stdout);
		fprintf(stderr, "ERROR: tried to decompose frozen edge #%d\n", edge->id);
		exit(-1);
	}

	for(i=0;i<edge->have;i++)
	{
		int	ngood = 1;
		struct edge	*d = edge->daughters[i];
		if(d->frozen && !d->frosted)
		{
			fflush(stdout);
			fprintf(stderr, "ERROR: tried to decompose edge #%d with frozen daughter #%d\n", edge->id, d->id);
			exit(-1);
		}
		// count non-frozen alternatives for this daughter
		for(j=0;j<d->npack;j++)
			if(!(d->pack[j]->frozen && !d->pack[j]->frosted))
				ngood++;
		n *= ngood + 1;
	}
	// this has been known to exceed the slab segment size:
	int	len = sizeof(struct decomposition) * n;
	extern long long currslabsize;
	if(len >= currslabsize)
	{
		d = dec = mega_slab(len, max_unpack_megabytes);
		if(!d)
		{
			fprintf(stderr, "NOTE: couldn't allocate %d decompositions, giving up\n",n);
			longjmp(out_of_memory_jump, 3);
		}
	}
	else d = dec = slab_alloc(len);

	for(i=0;i<n;i++)
	{
		dec[i].edge = edge;
		dec[i].seen_indices = NULL;
		dec[i].nsi = 0;
		dec[i].asi = 0;
		dec[i].is_scored = 0;
		dec[i].failed = dec[i].checked = 0;
	}

	n = 0;

	int	arity = edge->have;
	int	indices[arity];
	bzero(indices, sizeof(indices));
	while(1)
	{
		int	x;
		// make a decomposition with these indices
		struct edge	*rhs[arity];
		for(x=0;x<arity;x++)
		{
			int			ix = indices[x];
			struct edge	*rx = (ix==0)?edge->daughters[x]:edge->daughters[x]->pack[ix-1];
			if(rx->frozen && !rx->frosted)break;
			if(rx->rule && !check_rf(edge->rule, rx->rule, x))break;
			rhs[x] = rx;
		}
		if(x==arity)
		{
			// no checks failed; record it.
			d->rhs = slab_alloc(sizeof(struct edge*)*arity);
			memcpy(d->rhs, rhs, sizeof(struct edge*)*arity);
			d++;
			n++;
		}
		// increment the indices
		for(x=0;x<arity;x++)
		{
			indices[x]++;
			if(indices[x] > edge->daughters[x]->npack)
				indices[x] = 0;
			else break;
		}
		if(x==arity)break;
	}

	*Ndecompositions = n;
	totaldecompositions += n;
	return dec;
}

// is 'subsumer' >= 'subsumed' in all dimensions?
static inline int subsume_indices(int	*subsumed, int	*subsumer, int	arity)
{
	int	i;
	for(i=0;i<arity;i++)
		if(subsumed[i] > subsumer[i])return 0;
	return 1;
}

// have we used a hypothesis with these indices yet?
static inline int dec_seen_indices(struct decomposition	*dec, int	*indexlist)
{
	int	i, arity = dec->edge->have;
	// we've seen indexlist if it is subsumed by one we have recorded
	for(i=0;i<dec->nsi;i++)
		if(subsume_indices(indexlist, dec->seen_indices+arity*i, arity))return 1;
	return 0;
}

// record that we have used a hypothesis with these indices.
// pack our recorded list of indices under subsumption.
// we've seen everything subsumed by anything on our list.
void dec_add_indices(struct decomposition	*dec, int *indices)
{
	int	i, j;
	int	arity = dec->edge->have;
	// remove all indices subsumed by 'indices'
	for(i=j=0;i<dec->nsi;i++)
		if(!subsume_indices(dec->seen_indices+arity*i, indices, arity))
		{
			// not subsumed; keep it.
			if(j != i)
				memcpy(dec->seen_indices+arity*j, dec->seen_indices+arity*i, sizeof(int)*arity);
			j++;
		}
	dec->nsi = j;
	if(dec->nsi >= dec->asi)
	{
		dec->asi = (dec->nsi+1)*2;
		dec->seen_indices = slab_realloc(dec->seen_indices, sizeof(int)*arity*dec->nsi, sizeof(int)*arity*dec->asi);
	}
	memcpy(dec->seen_indices + dec->nsi*arity, indices, sizeof(int)*arity);
	dec->nsi++;
}

// should a hypothesis with these indices be built?
// if we've seen hypotheses with one less on each dimension, yes.
// otherwise, a hypothesis with one less on a dimension is guaranteed to be better, so don't allow this to be explored yet.
// return 0 to allow exploration, 1 to disallow
static inline int dec_check_indices(struct decomposition	*dec, int *indexlist)
{
	int ret = 0;

	int	i;
	for(i=0;i<dec->edge->have;i++)
	{
		indexlist[i]--;
		if(indexlist[i]>=0 && !dec_seen_indices(dec, indexlist))
			ret = 1;
		indexlist[i]++;
	}
	//ret = !(DEC_SEEN(indices[0]-1, indices[1]) && DEC_SEEN(indices[0], indices[1]-1));
	//printf("dec_check on %p [%d %d] = %d;   ni2 = %d\n", dec, indices[0], indices[1], ret, dec->ni2);
	return ret;
}

print_heap(struct hypagenda_item *h, int indent)
{
	int i;
	if(!h){printf("(null)\n");return 0;}
	for(i=0;i<indent;i++)printf("  ");
	printf("hyp %p [edge #%d] score %f\n", h->h, h->h->edge->id, h->h->score);
	if(h->left)print_heap(h->left, indent+1);
	if(h->right)print_heap(h->right, indent+1);
}

// insert 'h' into 'edge's agenda, a heap structure
void add_uagenda(struct hypagenda_item **A, struct hypagenda_item *newitem)
{
	struct hypagenda_item *w = *A, **W = A;

	while(w && w->h->score >= newitem->h->score)
	{
		if(!w->left || (w->right && rand()%2))
		{
			W = &w->left;
			w = w->left;
		}
		else
		{
			W = &w->right;
			w = w->right;
		}
	}

	*W = newitem;
	if(w)add_uagenda(W, w);
}

void	add_hypothesis_to_agenda(struct hypagenda_item	**agenda, struct hypothesis	*h)
{
	struct hypagenda_item	*ha = slab_alloc(sizeof(*ha));
	ha->h = h;
	ha->left = NULL;
	ha->right = NULL;

	add_uagenda(agenda, ha);
}

void	build_hypothesis_surface(struct hypothesis	*h)
{
	if(h->edge->lex)
	{
		if(h->arity == 0)
		{
			// lexeme
			struct edge	*e = h->edge;
			int	i, slen = 0;
			if(g_mode == GENERATING)
			{
				// when generating, tokens are not available, so we have to use stem[]
				for(i=0;i<e->lex->stemlen;i++)slen += strlen(e->lex->stem[i]->name) + 3;//1 - 2;
				if(slen%4)slen = (slen&~3)+4;
				h->string = slab_alloc(slen); h->string[0]=0;
				for(i=0;i<e->lex->stemlen;i++)
				{
					char	single[256];
					if(i)strcat(h->string, " ");
					strcpy(single, e->lex->stem[i]->name+1);
					if(*single)single[strlen(single)-1] = 0;
					strcat(h->string, single);
				}
			}
			else
			{
				// when parsing, tokens tell us the surface form
				struct token	**toks = (struct token**)e->daughters;
				for(i=0;i<e->lex->stemlen;i++)
					slen += strlen(toks[i]->string) + 3;//1 - 2;
				if(slen%4)slen = (slen&~3)+4;
				h->string = slab_alloc(slen); h->string[0]=0;
				for(i=0;i<e->lex->stemlen;i++)
				{
					if(i)strcat(h->string, " ");
					strcat(h->string, toks[i]->string);
				}
			}
		}
		else
		{
			// lexical rule
			assert(h->arity==1);	// lexical rules are unary
			if(h->edge->rule->orth && g_mode == GENERATING)
			{
				h->string = inflect(h->edge->rule->orth, h->rhslist[0]->string);
				if(!h->string)h->string = "(failed to inflect)";	// packing might make us try something silly here
			}
			else h->string = h->rhslist[0]->string;
		}
	}
	else
	{
		// combine the strings of daughters
		int slen = 0, i, arity = h->arity;
		for(i=0;i<arity;i++)slen += strlen(h->rhslist[i]->string) + 1;
		if(slen%4)slen = (slen&~3)+4;
		h->string = slab_alloc(slen); h->string[0] = 0;
		for(i=0;i<arity;i++)
		{
			if(i)strcat(h->string, " ");
			strcat(h->string, h->rhslist[i]->string);
		}
	}
}

struct hypothesis *new_hypothesis(struct decomposition	*dec, struct hypagenda_item **agenda, struct hypothesis **rhslist, int *indexlist, struct scoring_ancestry	ancestry)
{
	struct hypothesis	*h = slab_alloc(sizeof(struct hypothesis));
	int					i;

	DEBUG("hypothesize %p at dec %p [%d ...] for edge #%d\n", h, dec, indexlist[0], dec->edge->id);
	DEBUG2("current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));
//	DEBUG(" ... ancestry: ");
//	for(i=0;i<ancestry.nparent_types;i++){ DEBUG(" %s", ancestry.parent_types[i]); }
//	DEBUG("\n");

	h->dec = dec;
	h->edge = dec->edge;
	h->arity = dec->edge->have;
	h->rhslist = slab_alloc(sizeof(struct hypothesis*)*h->arity);
	memcpy(h->rhslist, rhslist, sizeof(struct hypothesis*)*h->arity);
	h->dg = NULL; h->string = NULL;
	h->checkup = 0;
	h->toklen = 0;
	h->eid = use_packed_edge_ids?h->edge->id:next_eid();
	for(i=0;i<h->arity;i++)
		h->toklen += h->rhslist[i]->toklen;

	build_hypothesis_surface(h);

	h->indexlist = slab_alloc(sizeof(int) * h->arity);
	memcpy(h->indexlist, indexlist, sizeof(int) * h->arity);
	h->ancestry = ancestry;

	score_hypothesis(h);

	add_hypothesis_to_agenda(agenda, h);
	total_hyps++;
	DEBUG2("(returning) current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));
	return h;
}

struct hypothesis *leaf_hypothesis(struct edge *e, struct scoring_ancestry	ancestry)
{
	struct hypothesis *hyp = slab_alloc(sizeof(struct hypothesis));
	int	i, slen = 0;
	assert(!e->have);

	hyp->dec = NULL;
	hyp->edge = e;
	hyp->toklen = e->lex->stemlen;
	hyp->arity = 0;
	hyp->rhslist = NULL;
	hyp->indexlist = NULL;
	hyp->eid = hyp->edge->id;

	assert(e->lex);
	build_hypothesis_surface(hyp);
	hyp->dg = NULL;
	hyp->checkup = -1;
	hyp->ancestry = ancestry;

	score_hypothesis(hyp);
	return hyp;
}

static int indent = 0;

static int g_checkup;
static inline void checkup(struct hypothesis *h)
{
	if(h->dg)return; // if we already know failure/success status, don't recurse
	if(h->checkup>=0 && h->checkup != g_checkup)
	{
		if(h->dec && h->dec->failed)
		{
			//printf("local failure saved work\n");
			h->dg = (void*)1;
			return;
		}
		int i;
		for(i=0;i<h->arity;i++)
		{
			checkup(h->rhslist[i]);
			if(h->rhslist[i]->dg == (void*)1)// || h->dec->failed)
			{
				h->dg = (void*)1;
				return;
			}
		}
		h->checkup = g_checkup;
	}
}

int	compare_ancestry(struct scoring_ancestry	a, struct scoring_ancestry	b)
{
	if(a.nparent_types != b.nparent_types)return a.nparent_types - b.nparent_types;
	if(a.rooted != b.rooted)return a.rooted - b.rooted;
	int i, r;
	for(i=0;i<a.nparent_types;i++)
		if(a.gprnum[i] != b.gprnum[i])return a.gprnum[i] - b.gprnum[i];
		//if( (r=strcmp(a.parent_types[i], b.parent_types[i])) != 0)return r;
	return 0;
}

void	hash_ancestry(struct scoring_ancestry	*anc)
{
	int i;
	char	*p;
	anc->hash = 0;
	anc->hash = anc->rooted * 7 + anc->nparent_types * 101;
	for(i=0;i<anc->nparent_types;i++)
	{
		anc->hash = ((anc->hash << 9) * 13) ^ (anc->hash >> 23);
		anc->hash ^= anc->gprnum[i];
		/*for(p=anc->parent_types[i];*p;p++)
		{
			anc->hash ^= *p;
			anc->hash  = (anc->hash << 3) | (anc->hash >> 29);
		}*/
	}
}

struct scoring_ancestry	compute_sub_ancestry(struct scoring_ancestry	panc, struct edge	*edge)
{
	struct scoring_ancestry	anc;
	anc.nparent_types = panc.nparent_types + 1;
	anc.rooted = panc.rooted;
	if(anc.nparent_types > max_grandparenting)
	{
		anc.nparent_types = max_grandparenting;
		anc.rooted = 0;
	}
	//anc.parent_types = slab_alloc(sizeof(char*) * anc.nparent_types);
	int i;
	for(i=1;i<anc.nparent_types;i++)
	{
		//anc.parent_types[i] = panc.parent_types[i-1];
		anc.gprnum[i] = panc.gprnum[i-1];
	}
	assert(edge->rule != NULL);
	if(anc.nparent_types)
	{
		//anc.parent_types[0] = edge_sign(edge);
		assert(edge->rule);
		anc.gprnum[0]  = edge->rule->rnum;
	}
	hash_ancestry(&anc);
	return anc;
}

void	put_more_on_agenda(struct hypagenda_item	**A, struct decomposition	*dec, int	*from_indices, struct scoring_ancestry	ancestry)
{
	int i, j;
	int	arity = dec->edge->have;
	struct scoring_ancestry	sub_ancestry;
	sub_ancestry = compute_sub_ancestry(ancestry, dec->edge);

	// popped an item off the agenda, now tell the corresponding
	// decomposition that the relevant index tuple has been popped
	// so it will let us extend around it
	dec_add_indices(dec, from_indices);
	for(i=0;i<arity;i++)
	{
		int	idx[arity];
		memcpy(idx, from_indices, sizeof(int)*arity);
		idx[i]++;
		if(!dec_check_indices(dec, idx))
		{
			struct hypothesis *rhs[arity];
			bzero(rhs, sizeof(struct hypothesis*)*arity);
			// try to add a new agenda hypothesis for {dec,idx}
			for(j=1;j<indent;j++)DEBUG("  ");
			DEBUG("trying further hypothesize [%d %d] on dec %p of #%d\n", idx[0], idx[1], dec, dec->edge->id);
			DEBUG2("current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));

			int	status = 0;
			for(j=0;j<arity;j++)
			{
				rhs[j] = hypothesize_edge(dec->rhs[j], idx[j], sub_ancestry, NULL);
				if(!rhs[j]) { status = -1; break; }
				/*if(rhs[j]->dg==(void*)0x1)	// TODO find a way to make this actually work.
				{
					// XXX this solution doesn't really work.
					// we miss readings on CSLI item 629 if the "if" is there
					// we crash on the very next item if it isn't there.
					// simple solution: pretend this hypothesis succeeded,
					// and pretend we've already popped it; get yet more indices!
					if(i==j)
						put_more_on_agenda(A, dec, idx, ancestry);
					//put_more_on_agenda(A, dec, idx, ancestry);
					status = -2;
					break;
				}*/
			}
			if(status == 0)new_hypothesis(dec, A, rhs, idx, ancestry);
			else
			{
				for(j=0;j<indent;j++)DEBUG("  ");
				if(status == -1)
					DEBUG(" further hypothesize [%d %d] returned nothing on dec %p\n", idx[0], idx[1], dec);
				else
					DEBUG(" further hypothesize [%d %d] returned a failed instantiation record on dec %p\n", idx[0], idx[1], dec);
			}
		}
		else
		{
			for(j=1;j<indent;j++)DEBUG("  ");
			DEBUG("%p of #%d doesn't want [%d %d]\n", dec, dec->edge->id, idx[0], idx[1]);
		}
	}
}

extern int cancel_task, did_timeout;

struct hypothesis *process_hypagenda(struct hypagenda_item **A)
{
	struct hypothesis	*hyp;
	struct hypagenda_item	**W, *l, *r;
	int					arity, i, j;

	if((slab_usage() / (1024*1024)) >= max_unpack_megabytes && !arbiter_request_memory())
		longjmp(out_of_memory_jump, 2);
	if(cancel_task)
		longjmp(out_of_memory_jump, 10);

	//printf("agenda:\n");
	//print_heap(*A, 1);

again:
	if(!*A)return NULL;

	// pop max from the agenda heap
	hyp = (*A)->h;

	for(l=(*A)->left,r=(*A)->right,W=A;l && r;)
	{
		struct hypagenda_item *tmp;
		if(l->h->score > r->h->score)
		{
			// promote left
			*W = l;
			tmp = l->right;
			l->right = r;
			W = &l->left;
			l = l->left;
			r = tmp;
		}
		else
		{
			// promote right
			*W = r;
			tmp = r->left;
			r->left = l;
			W = &r->right;
			r = r->right;
			l = tmp;
		}
	}
	if(l)*W = l;
	else *W = r;

	// do the expansion around the popped hyp
	DEBUG2("before put_more_on_agenda(): current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));
	put_more_on_agenda(A, hyp->dec, hyp->indexlist, hyp->ancestry);
	DEBUG2("after put_more_on_agenda(): current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));

	checkup(hyp);
	if(hyp->dg == (void*)1)
	{
		DEBUG("checkup failed for edge #%d hypothesis: ", hyp->eid);
		//print_hypothesis(hyp, printf, 0); printf("\n");
		goto again;
	}

	// 'hyp' is the next ranking item in the relevant edge's cache for this ancestry; record it.
	struct context_unpack_info	*cui = get_edge_cui(hyp->edge, hyp->ancestry);
	//if(!cui_has_hypothesis(cui, hyp))
	set_cui_hypothesis(cui, cui->nhypotheses, hyp);
	//else assert(!"wow... that hypothesis was already on the cui! how?");
	// ^^ I've never seen that assertion go off in my life.
	// the cui_has_hypothesis() call takes up a lot of time when there are long lists

	DEBUG2("returning from process_hypagenda(): current memory usage = %.1fmb\n", (double)slab_usage() / (1024*1024));

	return hyp;
}

struct context_unpack_info	*get_edge_cui(struct edge	*e, struct scoring_ancestry	ancestry)
{
	//start_and_alloc_profiler(&gec_profiler, "get-edge-cui", unpacking_profiler, NULL);
	if(!e->unpack)
	{
		e->unpack = slab_alloc(sizeof(struct unpack_info));
		bzero(e->unpack, sizeof(struct unpack_info));
	}

	// binary search
	int hi=e->unpack->ncuis,lo=0,mid = 0;
	while(hi>lo)
	{
		mid = (hi+lo)/2;
		unsigned int mh = e->unpack->cuis[mid]->ancestry.hash;
		if(ancestry.hash == mh)
			break;
		if(ancestry.hash > mh)lo=mid+1;
		else hi=mid;
	}
	if(hi>lo)
	{
		int i;
		// found the right part of the list
		for(i=mid;i<e->unpack->ncuis && ancestry.hash == e->unpack->cuis[mid]->ancestry.hash;i++)
			if(!compare_ancestry(ancestry, e->unpack->cuis[i]->ancestry))
				return e->unpack->cuis[i];
		for(i=mid-1;i>=0 && ancestry.hash == e->unpack->cuis[mid]->ancestry.hash;i--)
			if(!compare_ancestry(ancestry, e->unpack->cuis[i]->ancestry))
				return e->unpack->cuis[i];
	}
	else mid = lo;
	// no matching hash value, but 'mid' is where to insert it

/*
	// linear search
	int i;
	for(i=0;i<e->unpack->ncuis;i++)
		if(ancestry.hash == e->unpack->cuis[i]->ancestry.hash)
		{
			if(!compare_ancestry(ancestry, e->unpack->cuis[i]->ancestry))
			{
				//stop_profiler(gec_profiler, 1);
				if(i>0)
				{
					// hack to massage the list into a more use-frequency sorted order over time if a lot of requests are made
					int	swap = i/2;
					struct context_unpack_info *tmp = e->unpack->cuis[i];
					e->unpack->cuis[i] = e->unpack->cuis[swap];
					e->unpack->cuis[swap] = tmp;
					return tmp;
				}
				return e->unpack->cuis[i];
			}
			//else printf("HASH collision @ %8.8x\n", ancestry.hash);
		}
*/

	e->unpack->cuis = slab_realloc(e->unpack->cuis, sizeof(struct context_unpack_info*)*e->unpack->ncuis, sizeof(struct context_unpack_info*)*(e->unpack->ncuis+1));
	struct context_unpack_info	*cui = slab_alloc(sizeof(*cui));
	bzero(cui, sizeof(*cui));
	cui->ancestry = ancestry;
	//e->unpack->cuis[e->unpack->ncuis++] = cui;

	// insert at 'mid'
	memmove(e->unpack->cuis+mid+1, e->unpack->cuis+mid, sizeof(struct context_unpack_info*) * (e->unpack->ncuis - mid));
	e->unpack->cuis[mid] = cui;
	e->unpack->ncuis++;

	//stop_profiler(gec_profiler, 1);
	/*if(e->unpack->ncuis == 200)
	{
		printf("edge #%d %d - %d has 200+ CUIs\n", e->id, e->from, e->to);
		for(i=0;i<e->unpack->ncuis;i++)
		{
			struct scoring_ancestry a = e->unpack->cuis[i]->ancestry;
			int j;
			if(a.rooted)printf("^ ");
			for(j=0;j<a.nparent_types;j++)printf("%s ",a.parent_types[j]);
			printf("\n");
		}
	}*/
	return cui;
}

//#define	HYPS_PER_BLOCK	1024

void	set_cui_hypothesis(struct context_unpack_info	*cui, int	rank, struct hypothesis	*h)
{
	if(cui->nhypotheses <= rank)
	{
		assert(cui->nhypotheses == rank);
		cui->nhypotheses = rank+1;
		if(cui->nhypotheses > cui->ahypotheses)
		{
			int	oah = cui->ahypotheses;
			cui->ahypotheses = 2*(rank+1) - 1;
			int	newlen = sizeof(struct hypothesis*)*cui->ahypotheses;
			extern long long currslabsize;
			if(newlen >= currslabsize)
			{
				struct hypothesis	**newlist = mega_slab(newlen, max_unpack_megabytes);
				if(!newlist)
				{
					fprintf(stderr, "NOTE: couldn't allocate %d hypothesis pointers, giving up\n", cui->ahypotheses);
					longjmp(out_of_memory_jump, 3);
				}
				memcpy(newlist, cui->hypotheses, sizeof(struct hypothesis*)*(oah));
				cui->hypotheses = newlist;
			}
			else cui->hypotheses = slab_realloc(cui->hypotheses, sizeof(struct hypothesis*)*(oah), newlen);
		}
	}
	cui->hypotheses[rank] = h;
}

struct hypothesis	*get_cui_hypothesis(struct context_unpack_info	*cui, int	rank)
{
	if(cui->nhypotheses <= rank)return NULL;
	return cui->hypotheses[rank];
}

/*int	cui_has_hypothesis(struct context_unpack_info	*cui, struct hypothesis	*hyp)
{
	int i;
	for(i=0;i<cui->nhypotheses;i++)
		if(hyp == cui->hypotheses[i])return 1;
	return 0;
}*/

struct hypothesis *hypothesize_edge(struct edge *e, int rank, struct scoring_ancestry	ancestry, struct hypagenda_item	**customAgenda)
{
	int					i, j;

	struct context_unpack_info	*cui = get_edge_cui(e, ancestry);

	for(i=0;i<indent;i++)DEBUG("  ");
	DEBUG("asked to hyp %d on edge #%d [%d-%d] (had seen %d)\n", rank, e->id, e->from, e->to, cui->nhypotheses);
	DEBUG(" ... cui %p ancestry: ", cui);
	for(i=0;i<ancestry.nparent_types;i++){ DEBUG(" %d", ancestry.gprnum[i]); }
	DEBUG("\n");

	struct hypothesis	*hyp = get_cui_hypothesis(cui, rank);
	if(hyp)
	{
		if(customAgenda)
		{
			// if customAgenda is set, we are supposed to put all the hypotheses that have been created at time of return onto it before returning
			DEBUG(" ... returning %d already-known hypotheses in customAgenda\n", cui->nhypotheses);
			int i;
			for(i=0;i<cui->nhypotheses;i++)
				add_hypothesis_to_agenda(customAgenda, cui->hypotheses[i]);
		}
		return hyp;
	}

	if(cui->nhypotheses != rank)
	{
		fprintf(stderr, "unpack(): asked for rank %d, but next is actually rank %d\n",
					rank, cui->nhypotheses);
	/*DEBUG("context of error was:\n");
	DEBUG("  ... asking hyp %d on edge #%d [%d-%d] (had seen %d)\n", rank, e->id, e->from, e->to, cui->nhypotheses);
	DEBUG(" ... ancestry: ");
	for(i=0;i<ancestry.nparent_types;i++){ DEBUG(" %s", ancestry.parent_types[i]); }
	DEBUG("\n");*/
		assert(0);
	}

	//DEBUG("asked to hyp %d on edge #%d\n", rank, e->id);

	if(!e->have)
	{
		if(rank != 0)return NULL;
		hyp = leaf_hypothesis(e, ancestry);
		set_cui_hypothesis(cui, 0, hyp);
		return hyp;
	}

	if(!cui->nhypotheses)
	{
		// nothing in the cache means we haven't decomposed this edge and put the initial hypotheses on the agenda yet
		int i, j, ndecs;
		int	arity = e->have;
		int	idx[arity];
		bzero(idx, sizeof(int)*arity);

		struct decomposition *decs;
		// initialize agenda with (0,...,0) index vector for each decomposition
		decs = decompose_edge(e, &ndecs);
		if(!decs)return NULL;
		cui->decs = decs;
		cui->ndecs = ndecs;
		indent++;

		struct scoring_ancestry	sub_ancestry;
		sub_ancestry = compute_sub_ancestry(ancestry, e);

		for(i=0;i<ndecs;i++)
		{
			struct decomposition *dec = decs+i;
			struct hypothesis *rhs[arity];
			bzero(rhs, sizeof(struct hypothesis*)*arity);
			for(j=0;j<arity;j++)
			{
				rhs[j] = hypothesize_edge(dec->rhs[j], 0, sub_ancestry, NULL);
				if(!rhs[j])break;
			}
			if(j<arity)continue;	// failed to hypothesize even the 0'th unpacking of this decomposition
			struct hypothesis	*h = new_hypothesis(dec, &cui->agenda, rhs, idx, ancestry);
			if(customAgenda)add_hypothesis_to_agenda(customAgenda, h);
		}
		indent--;
	}

	if(customAgenda)return NULL;

	indent++;
	hyp = process_hypagenda(&cui->agenda);
	indent--;
	if(!hyp)return NULL;

	//set_cui_hypothesis(cui, rank, hyp);
	return hyp;
}

struct hypothesis	*cheap_hypothesis(struct edge	*e, int	with_dg)
{
	struct hypothesis	*h = slab_alloc(sizeof(*h));
	bzero(h, sizeof(*h));
	h->edge = e;
	h->eid = e->id;
	h->arity = e->have;
	h->rhslist = slab_alloc(sizeof(void*)*h->arity);
	int i;
	for(i=0;i<h->arity;i++)
	{
		h->rhslist[i] = cheap_hypothesis(e->daughters[i], with_dg);
		h->toklen += h->rhslist[i]->toklen;
	}
	if(with_dg)h->dg = e->dg;
	if(e->lex)h->toklen = e->lex->stemlen;
	build_hypothesis_surface(h);
	return h;
}

unsigned long long total_reconstructed_nodes;

struct lexeme	*get_hypothesis_lexeme(struct hypothesis	*h)
{
	// have to walk down to the bottom because packing can cause the ->edge->lex on an upper node to be different from on a lower node
	while(h->edge->rule)h = h->rhslist[0];
	assert(h->edge->lex);
	return h->edge->lex;
}

int unify_type_to_path(struct dg	*dg, char	*typename, struct path	path)
{
	struct dg	*d = dg_path(dg, path);
	if(!d || d==dg)
	{
		fprintf(stderr, "ERROR: no such path\n");
		return -1;
	}
	struct type	*t = lookup_type(typename);
	if(!t)
	{
		fprintf(stderr, "ERROR: no such type '%s'\n", typename);
		return -1;
	}
	struct type	*g = glb(d->xtype, t);
	if(!g)
	{
		fprintf(stderr, "ERROR: no glb for '%s' and '%s'\n", d->xtype->name, typename);
		return -1;
	}
	d->type = d->xtype = g;
	return 0;
}
 
int instantiate_hypothesis(struct hypothesis *h)
{
	int arity = h->arity, i;

	// don't try to re-instantiate when we've already been here!
	if(h->dg)
	{
		if(h->dg == (void*)1)
		{
		return -1;
			assert(!"Not reached");
			return -1;
		}
		else return 0;
	}

	DEBUG("inst edge #%d rule %s     = dec %p\n", h->edge->id, h->edge->rule?h->edge->rule->name:NULL, h->dec);
	for(i=0;i<arity;i++)
		if(0 != instantiate_hypothesis(h->rhslist[i]))
		{
			h->dg = (void*)1;
			DEBUG("edge #%d fail on daughter %d = #%d\n", h->edge->id, i, h->rhslist[i]->edge->id);
			return -1;
		}
	if(!h->string)
		build_hypothesis_surface(h);

	extern int	dont_unspecialize;
	// it's tempting to think we need to unspecialize when we're doing generalization in-situ on parse edges.
	// that's because modifying the result of a rule (e.g. to make the top type 'sign') can modify the lexical dag by subgraph sharing.
	// but if we unspecialize, be *sure* to put the token information back in -- and it's not available right now (is it?).
	// so for now, don't generalize anything except the top type of a sign -- that can't hurt anything.
	int	unspecialize = /*(g_mode == PARSING) || */((g_mode == GENERATING) && (!dont_unspecialize));
	if(unspecialize || !inhibit_pack)
	{
		if(!arity)
		{
			// lexeme edge.  we don't restrict these.
			if(unspecialize)
			{
				// generator lexeme.  don't put the specialized RELS list in.
				h->dg = lexical_dg(h->edge->lex, 0);
			}
			else h->dg = h->edge->dg;
		}
		else
		{
			total_reconstructed_nodes++;
			struct dg *rdg = h->edge->rule->dg;
			int	robustness_licensed = 0, robustness_used = 0;
			if(0)
			{
				try_with_robustness:
				robustness_used = 1;
				enable_robust_unification();
				//printf("using robust unification to reconstruct #%d: %s\n",
				//	h->edge->id, h->edge->rule?h->edge->rule->name:h->edge->lex->word);
			}
			if(g_mode == PARSING && h->edge->neps==-1)
			{
				robustness_licensed = 1;
			}
			for(i=0;i<arity;i++)
				if(unify_dg_tmp(h->rhslist[i]->dg, rdg, i))
				{
					//printf("when combining edges #%d and #%d under rule %s\n",
					//	h->edge->id, h->rhslist[i]->edge->id, h->edge->rule->name);
					//unify_backtrace();
					//print_hypothesis(h, printf, 0); printf("\n\n");
					forget_tmp();
					h->dg = (void*)1;
					/*if(!(h->dec->checked & (1<<i)))
					{
						// experiment to see whether the un-reconstructed edges fit...
						int k;
						struct edge	*d = h->dec->rhs[i];
						int res = unify_dg_tmp(d->dg, rdg, i);
						forget_tmp();
						if(res != 0)
						{
							//printf(" experiment found a local failure: #%d[%d] != #%d\n", h->edge->id, i, d->id);
							h->dec->failed |= 1<<i;
						}
						else h->dec->failed &= ~(1<<i);
						h->dec->checked |= 1<<i;
					}*/
					/*if(!h->dec->checked)
					{
						// experiment to see whether the un-reconstructed edges fit...
						//  better than previous experiment: put all daughters in, not just 1.
						int k;
						for(k=0;k<arity;k++)
							if(unify_dg_tmp(h->dec->rhs[k]->dg, rdg, k))
								break;
						forget_tmp();
						h->dec->checked = 1;
						if(k<arity)
						{
							//printf("experiment: local failure for decomposition %p\n", h->dec);
							h->dec->failed = 1;
						}
						//else printf("experiment: local success for decomposition %p\n", h->dec);
					}*/
					break;
				}
			if(i<arity)
			{
				if(robustness_used)disable_robust_unification();
				else if(robustness_licensed)goto try_with_robustness;
				return -1;
			}
			if(h->edge->rule->orth)
				if(unify_orthography(rdg, h->rhslist[0]->dg, get_hypothesis_lexeme(h), h->edge->rule))
				{
					forget_tmp();
					h->dg = (void*)1;
					if(robustness_used)disable_robust_unification();
					else if(robustness_licensed)goto try_with_robustness;
					return -1;
				}
			if(g_mode == GENERATING)
			{
				int cant_share = 0;
				for(i=0;i<arity;i++)
					if(h->rhslist[i]->edge->neps == 0)
						cant_share = 1;
				if(cant_share)
					h->dg = finalize_tmp_noss(rdg, 1);
				else h->dg = finalize_tmp(rdg, 1);
			}
			else h->dg = finalize_tmp(rdg, 1);
			if(robustness_used)
			{
				disable_robust_unification();
				if(robustness_marker_type)
					unify_type_to_path(h->dg, robustness_marker_type, robustness_marker_path);
			}
			if(!h->dg)	// cycle failure can occur
			{
				h->dg = (void*)1;
				//printf("when combining edges #%d and #%d under rule %s, cycle\n", h->edge->id, h->rhslist[i]->edge->id, h->edge->rule->name);
				return -1;
			}
		}
	}
	else
	{
		// no need to unspecialize or reconstruct; we already have a full dag.
		h->dg = h->edge->dg;
	}

	return 0;
}

struct dstr_cache
{
	char	*str;
	struct hypothesis	*h;
	int					o;
	int		gen;
};

#define	DSTR_CACHE_SIZE	102397
static struct dstr_cache	dstr_cache[DSTR_CACHE_SIZE];
int		dstr_cache_gen = 1;

void clear_dstr_cache()
{
	dstr_cache_gen++;
}

#define	DSTR_HASH(h,o)	(int)((((unsigned long long)h)^o) % (DSTR_CACHE_SIZE))

char	*dstr_lookup(struct hypothesis	*h, int	o)
{
	int	hc = DSTR_HASH(h,o);
	if(dstr_cache[hc].h == h && dstr_cache[hc].o == o && dstr_cache[hc].gen == dstr_cache_gen)
		return dstr_cache[hc].str;
	return NULL;
}

void	dstr_save(struct hypothesis	*h, int	o, char	*str)
{
	int	hc = DSTR_HASH(h,o);
	dstr_cache[hc].h = h;
	dstr_cache[hc].o = o;
	dstr_cache[hc].str = str;
	dstr_cache[hc].gen = dstr_cache_gen;
}

struct token	*gen_extract_one_token(struct hypothesis	*h, int	k, char	*inflected_form)
{
	assert(h->edge->lex && !h->edge->rule);
	struct token	*t = slab_alloc(sizeof(*t));
	bzero(t, sizeof(*t));
	t->eid = -1;	// these get re-extracted all the time; who can say when two tokens are logically identical?
	t->used = 1;
	if(!enable_token_avms)goto missing_token;
	struct dg	*toklist = dg_path(h->dg, lex_tokens_list_path);
	if(toklist == NULL)goto missing_token;
	int	kk = k;
	while(kk>0)
	{
		toklist = dg_hop(toklist, 2);	// REST
		if(toklist == NULL)goto missing_token;
		kk--;
	}
	struct dg	*tokdg = dg_hop(toklist, 1);
	if(!tokdg)goto missing_token;

	struct dg	*form_dg = dg_path(tokdg, token_form_path);
	if(form_dg && form_dg->xtype->name[0]=='"')
		t->string = type_to_string(form_dg->xtype);
	else t->string = inflected_form;//type_to_string(h->edge->lex->stem[k]);
	t->dg = tokdg;
	return t;
missing_token:
	// we get here if the grammar left some information unspecified in the tokens list.
	// ... happens for MWEs especially.
	t->string = inflected_form;
	if(enable_token_avms)
		t->dg = type_dg(token_type);
	else t->dg = type_dg(top_type);
	return t;
}

inflect_mwe_chain(int	ntoks, char	**forms, struct hypothesis	*h)
{
	if(h->edge->rule)
	{
		assert(h->arity == 1);	// lexical rules are unary.
		inflect_mwe_chain(ntoks, forms, h->rhslist[0]);
		if(h->edge->rule->orth)
		{
			struct orule	*o = h->edge->rule->orth;
			int	k = 0;
			if(o->type == or_suffix)
				k = ntoks-1;
			forms[k] = inflect(o, forms[k]);
		}
	}
}

struct lexeme	*get_leaf_lex(struct hypothesis	*hyp)
{
	// why we need to do this:
	// with packing (enabled even on lexical edges for generation),
	//  the hyp->edge->lex field might not match the lexeme at the bottom of the tree.
	// we care when generating the surface forms.
	assert(hyp->edge->lex);
	while(hyp->edge->rule)hyp = hyp->rhslist[0];
	return hyp->edge->lex;
}

void print_hypothesis_from(struct hypothesis *hyp, int (*print)(const char *fmt,...), int	labelled, int	_from)
{
	void	print_tree0(struct hypothesis *hyp, int from, char	**genwordforms)
	{
		int i;
		struct edge *e = hyp->edge;

		if(e->lex && g_mode == GENERATING)
		{
			if(!genwordforms)
			{
				struct lexeme	*l = get_leaf_lex(hyp);
				int				nforms = l->stemlen;
				char	*forms[nforms];
				for(i=0;i<nforms;i++)
					forms[i] = type_to_string(l->stem[i]);
				inflect_mwe_chain(nforms, forms, hyp);
				print_tree0(hyp, from, forms);
				return;
			}
		}

		// print out the edge, with span information
		char	*sign = "no-sign";
		char	*udx_type = "", *udx_at = "";
		if(e->rule)
		{
			sign = e->rule->name;
			if(format_udx>1)
			{
				udx_at = "@";
				udx_type = e->rule->dg->xtype->name;
			}
		}
		else if(e->lex)
		{
			sign = e->lex->word;
			if(format_udx>0)
			{
				udx_at = "@";
				udx_type = e->lex->lextype->name;
			}
		}
		if(!labelled)
			print(" (%d %s%s%s %f %d %d", hyp->eid, sign, udx_at, udx_type,
							hyp->score, from, from+hyp->toklen);
		else print(" (\"%s\"", label_dag(hyp->dg, "?"));
		if(e->have)
		{
			for(i=0;i<e->have;i++)
			{
				print_tree0(hyp->rhslist[i], from, genwordforms);
				from += hyp->rhslist[i]->toklen;
			}
		}
		else if(e->lex)
		{
			int	ntokens = e->lex->stemlen;
			struct token	*tokens[ntokens];
			for(i=0;i<ntokens;i++)
			{
				if(g_mode == PARSING)
					tokens[i] = (struct token*)e->daughters[i];
				else tokens[i] = gen_extract_one_token(hyp, i, genwordforms[i]);
			}
			print(" (\"");
			for(i=0;i<ntokens;i++)
			{
				struct token	*tok = tokens[i];
				char	*form = tok->string;
				if(i>0)print(" ");
				print("%s", slab_escape(form));
			}
			print("\"");

			if(enable_token_avms)
			{
				if(!labelled)
				{
					for(i=0;i<ntokens;i++)
					{
						struct token	*tok = tokens[i];
						int	id = tok->eid;
						char	*tokstr = dstr_lookup((void*)tok, from);
						if(!tokstr)
						{
							char	token_str[10240];
							extern int dag_print_style;
							dag_print_style = 1;
							snprint_dg(token_str, 10239, tok->dg);
							// *token_str = 0;
							dag_print_style = 0;
							tokstr = slab_escape(token_str);
							dstr_save((void*)tok, from, tokstr);
						}
						print(" %d \"%s\"", id, tokstr);
					}
				}
			}
			print(")");
		}
		print(")");
	}
	static int timer = -1;
	if(timer==-1)timer = new_timer("derivation printing");
	start_timer(timer);
	//struct slab_state	st;
	//get_slabstate(&st);	// the slab_escape() nonsense for escaping token structures shouldn't stay with us forever!
	// actually, it should since we're caching them now
	if(derivations_include_roots)
	{
		assert(hyp->dg != NULL);
		char	*root = is_root(hyp->dg);
		extern int enable_dublin;
		if(enable_dublin && !root)
			root = "CSAW_ROBUST";
		assert(root != NULL);
		print(" (%s", root);
	}
	print_tree0(hyp, _from, NULL);
	if(derivations_include_roots)print(")");
	//set_slabstate(&st);
	stop_timer(timer, 1);
}

void print_hypothesis(struct hypothesis *hyp, int (*print)(const char *fmt,...), int	labelled)
{
	print_hypothesis_from(hyp, print, labelled, 0);
}

char	*hypothesis_to_dstring_from(struct hypothesis	*h, int	_from)
{
	char	*derivation = malloc(10240);
	int		dalen = 10240, dlen = 0;
	*derivation = 0;
	int	dprintf(const char	*fmt, ...)
	{
		va_list	v;
		va_start(v, fmt);
		int	l = vsnprintf(derivation+dlen, dalen-dlen, fmt, v);
		va_end(v);
		if(l >= dalen-dlen)
		{
			va_list v2;
			va_start(v2, fmt);
			dalen += l + 10240 ;
			derivation = realloc(derivation, dalen);
			l = vsnprintf(derivation+dlen, dalen-dlen, fmt, v2);
			va_end(v2);
		}
		dlen += l;
		return l;
	}
	print_hypothesis_from(h, dprintf, 0, _from);
	return derivation;
}

char	*hypothesis_to_dstring(struct hypothesis	*h)
{
	return hypothesis_to_dstring_from(h, 0);
}

char	*hypothesis_to_labelled_tree_string(struct hypothesis	*h)
{
	char	*lt = malloc(10240);
	int		dalen = 10240, dlen = 0;
	*lt = 0;
	int	dprintf(const char	*fmt, ...)
	{
		va_list	v;
		va_start(v, fmt);
		int	l = vsnprintf(lt+dlen, dalen-dlen, fmt, v);
		va_end(v);
		if(l >= dalen-dlen)
		{
			va_list v2;
			va_start(v2, fmt);
			dalen += l + 10240 ;
			lt = realloc(lt, dalen);
			l = vsnprintf(lt+dlen, dalen-dlen, fmt, v2);
			va_end(v2);
		}
		dlen += l;
		return l;
	}
	print_hypothesis(h, dprintf, 1);
	return lt;
}

/*void	install_orth(struct dg	*dg, int	nforms, char	**forms)
{
	struct dg	*stem_list = dg_path(dg, lex_stem_path);
	int	k = 0;
	for(k=0;k<nforms;k++)
	{
		assert(stem_list);
		struct dg	*stem_first = dg_hop(stem_list, 1);	// FIRST
		assert(stem_first);

		char	buffer[1024];
		sprintf(buffer, "\"%s\"", forms[k]);
		struct type	*ot = add_string(freeze_string(buffer));
		stem_first->type = stem_first->xtype = ot;
		stem_list = dg_hop(stem_list, 2);	// REST
	}
	assert(stem_list);
	stem_list->xtype = lookup_type(g_null_type);
}*/

int	gen_extract_lexemes(struct dg	*topdown, struct hypothesis	*h, int	k, struct edge	**L)
{
	int	i;
	if(h->edge->lex)
	{
		// new edge structure because topdown info isn't applicable to other users
		struct edge	*e = slab_alloc(sizeof(*e));
		*e = *h->edge;
		e->dg = topdown;
		// no longer need to do the orthography stuff below (I think),
		// since we now put orthography info in with unify_orthography().
		// old:
			// we need to build the orthographies of each token for MWEs;
			// starting with the base forms in the lexicon,
			/*struct lexeme	*lex = get_leaf_lex(h);
			int	n = lex->stemlen;
			char	*forms[n];
			for(i=0;i<n;i++)forms[i] = type_to_string(lex->stem[i]);
			// apply all the inflections in the lexical rule chain,
			// applying suffix rules to the right-hand edge of the MWE
			// and prefix rules to the left-hand-edge.
			inflect_mwe_chain(n, forms, h);
			install_orth(e->dg, n, forms);*/
		L[k] = e;
		//lui_dg_list(lex->word, e->dg, make_provenance(FROM_TREE,h));
		return k+1;
	}
	// get full FS for h
	assert(0 == unify_dg_tmp(h->edge->rule->dg, topdown, -1));
	for(i=0;i<h->arity;i++)assert(0 == unify_dg_tmp(h->rhslist[i]->dg, topdown, i));
	// copy out topdown info for each daughter
	if(h->edge->rule->orth)assert(0 == unify_orthography(topdown, h->rhslist[0]->dg, get_hypothesis_lexeme(h), h->edge->rule));
	topdown = finalize_tmp(topdown, 0);
	assert(topdown != NULL);
	for(i=0;i<h->arity;i++)
		k = gen_extract_lexemes(daughter_position(topdown, i), h->rhslist[i], k, L);
	return k;
}

/* ERG's Lisp code to do this roughly translates as:
bool gen-extract-surface(edge, initialp, cliticp)
{
	if(edge->daughters)
	{
		for each daughter d
			cliticp = gen-extract-surface(d, initialp, cliticp)
		return cliticp
	}
	else
	{
		entry = lexical-entry for e
		orth = orthography of 'entry', with a space after it?
		do some ugly hack for "Englishmen"
		tdfs = lex-entry-full-fs(entry);
		type = tdfs->type
		string = downcase(first leaf of edge)?
		prefix = how many initial characters of string are in {(, ", '}
		suffix = min(length of string, prefix + length of orth)
		if(orth != the substring of 'string' between prefix and suffix)
			suffix = 0
		rawp = suffix != 0 and there is at least 1 uppercase letter in orth
		capitalizep = 1 if type is a subtype of one of:
			{basic_n_proper_lexent, n_-_c-month_le, n_-_c-dow_le, n_-_pr-i_le}
		if(!cliticp)
			cliticp = string length > 0 and string[0]=='\''
		if(rawp)
			string = string[0..prefix] + orth + string[suffix..end]
		else if(capitalizep)
			replace underscores with spaces
			set the first alphanumeric character after each space to be uppercase
		if(string[0]=='_' && length(string) > 1 && string[1] is uppercase)
			string = string[1..end]
		if(initialp && string[0] is alphanumeric)
			string[0] = towupper(string[0]);
		if(!initialp && !cliticp)
			output a space
		output string, skipping spaces following hyphens
		return (last character we output == '-')
	}
}
*/

void	fixup_generator_string(struct hypothesis	*h)
{
	extern int trace;
	if(enable_post_generation_mapping)
	{
		struct edge	**lexeme_list = slab_alloc(sizeof(struct edge*) * h->toklen);
		//start_lui_dg_list();
		int n = gen_extract_lexemes(h->dg, h, 0, lexeme_list);
		//stop_lui_dg_list("generator lexical output");
		int k;
		for(k=0;k<n;k++)
		{
			if(trace>0)printf("lexeme %d: %s\n", k, lexeme_list[k]->lex->word);
			//print_dg(lexeme_list[k]->dg);
			//printf("\n");
		}
		struct lattice	*l = edge_list_to_lattice(n, (void**)lexeme_list);
		apply_post_generation_mapping_rules(l);
		sort_lattice(l);
		struct lattice_vertex	*v = l->vertices[0];
		int	slen = 0, nedges = 0;
		int	maxedges = l->nedges * 2 + 1024;
		char	*tokens[maxedges];
		while(v && v->nfollowers)
		{
			assert(v->nfollowers == 1);
			struct lattice_edge	*e = v->followers[0];
			struct dg	*dg = e->edge->dg;
			struct dg	*orth = dg_path(dg, lex_stem_path);
			assert(orth);
			while(orth)
			{
				struct dg	*of = dg_hop(orth, 1);	// FIRST
				if(!of)break;
				if(trace>0)printf("output edge %s\n", of->xtype->name);
				v = e->to;
				char	*token = of->xtype->name;
				tokens[nedges++] = token;
				slen += strlen(token) - 2 + 1;	// discount ""s on the type name; add a space.
				orth = dg_hop(orth, 2);	// REST
				assert(nedges < maxedges);
			}
		}
		slen += 1;
		if(slen % 4)slen = slen + 4 - (slen%4);
		h->string = slab_alloc(slen);
		char	*ptr = h->string;
		for(k=0;k<nedges;k++)
		{
			if(k)*ptr++ = ' ';
			ptr += sprintf(ptr, "%.*s", (int)strlen(tokens[k])-2, tokens[k]+1);
		}
		*ptr = 0;
	}
	else
	{
		wchar_t	*w = towide(h->string);
		wchar_t	*p = w, *q = w;
		int		initialp = 1;

		while(*p)
		{
			if(initialp && iswalnum(*p))
			{
				// capitalize the first alphanumeric
				*q++ = towupper(*p++);
				initialp = 0;
			}
			else if(*p == ' ' && p>w && p[-1]=='-')
			{
				// gobble up space after hyphens
				p++;
			}
			else if(*p == ' ' && p[1] == '\'' && p[2] && p[2]!=' ')
			{
				// gobble up space before clitics
				p++;
			}
			else if(*p == '_')
			{
				// convert to a space
				*q++ = ' ';
				p++;
			}
			else *q++ = *p++;
		}
		*q = 0;
		h->string = freeze_tombs(w);
		free(w);
	}
}

int want_mrs = 1;

int iterate_cell_root_hypotheses(struct chart_cell *cell, int (*process)(struct hypothesis *hyp, struct mrs *mrs, double	probability), int nbest)
{
	int	i, j;
	volatile int count = 0, nhyp = 0, ninsthyps = 0;	// volatile so that they are usable after longjmp()'ing out of an OOM condition
	struct hypagenda_item	*agenda = NULL;
	struct hypothesis		*hyp;
	struct edge			*edge;

	int	complained_about_unidiomatic_input = 0;
	static int	hyp_timer = -1, inst_timer = -1, mrs_timer = -1;

extern int do_itsdb;
	// exhaustive_unpack() is maybe a bit faster, but it doesn't do ranking,
	// and it doesn't know how to `dont_unspecialize'...
	//if(!nbest && !do_itsdb)return exhaustive_unpack(cell, process);

	static struct scoring_ancestry	root_ancestry = {.nparent_types=0/*,.parent_types=NULL*/, .rooted = 1};
	hash_ancestry(&root_ancestry);

	clear_dstr_cache();

	if(setjmp(out_of_memory_jump) != 0)
	{
		if(cancel_task && did_timeout)
		{
			// NOTE and itsdb_error already have been called
			fprintf(stderr, "NOTE: out of time while unpacking\n");
			itsdb_error("ran out of time while unpacking");
		}
		else
		{
			// cancel_task can be set when arbiter sends a cancellation request
			// we might also get here when we decide on our own that we're out of memory
			fprintf(stderr, "NOTE: hit RAM limit while unpacking\n");
			itsdb_error("ran out of RAM while unpacking");
		}
		goto resume_after_oom;
	}

	for(i=0;i<cell->p_nedges;i++)
	{
		edge = cell->p_edges[i];
		if(edge->frozen)
		{
			fprintf(stderr, "ERROR: found a frozen edge #%d (not packed) in the root cell!\n", edge->id);
			itsdb_error("frozen edge in root cell");
			//exit(-1);
			continue;
			// XXX these can occur in generation when index accessibility filtering causes a more general analysis to be discarded...
			// XXX looking forward to finding a way NOT to have that happen.
			// packing and and index accessibility filtering at the moment seem to be incompatible... see email to oe/glenn jul-27-2012
			// for now, pretend they are compatible... brush the problem under the rug...
			// it's rare.
			// this means we do miss realizations occassionally, in theory.
			// case: GG 'babel' suite item 177
		}
		if( (g_mode!=GENERATING || ep_span_is_root(edge->ep_span_bv, edge->neps)) && is_root(edge->dg) )// && !edge->frozen )
		{
			DEBUG("edge #%d can be root...\n", edge->id);
			for(j=-1;j<edge->npack;j++)
			{
				// for each potentially root packed edge...
				struct edge *e = (j==-1)?edge:edge->pack[j];
				if(e->frozen && !e->frosted)continue;
				if(!is_root(e->dg))continue;
				hypothesize_edge(e, 0, root_ancestry, &agenda);
			}
		}
	}

	// should have decomposed every edge in every context
	// and scored every local context by now
	// ... go get the normalization factor
	double	Z = 0;
	//double	Z_robust = 0;
	for(i=0;i<cell->p_nedges;i++)
	{
		edge = cell->p_edges[i];
		if(edge->frozen)continue;
		if( (g_mode!=GENERATING || ep_span_is_root(edge->ep_span_bv, edge->neps)) && is_root(edge->dg) )
		{
			for(j=-1;j<edge->npack;j++)
			{
				// for each potentially root packed edge...
				struct edge *e = (j==-1)?edge:edge->pack[j];
				if(e->frozen && !e->frosted)continue;
				if(!e->daughters)continue;	// generalization edge
				char	*root = is_root(e->dg);
				if(!root)continue;
				struct context_unpack_info	*cui = get_edge_cui(e, root_ancestry);
				int k;
				for(k=0;k<cui->ndecs;k++)
				{
					// if we discovered that there are no unifiable
					// instantiations of this decomposition, is_scored may never have been set.
					// rare -- but it can happen.  not counting the Z terms for those ghost readings doesn't seem wrong -- in fact it seems like an improvement.
					if(cui->decs[k].is_scored == 0)
						continue;
					Z += cui->decs[k].all_unpackings_z;
					//fprintf(stderr, "root edge #%d dec %p %d / %d score %f\n",
					//	e->id, cui->decs+k, k+1, cui->ndecs, cui->decs[k].all_unpackings_z);
					//if(strstr(root, "robust"))Z_robust += cui->decs[k].all_unpackings_z;
				}
			}
		}
	}
	//fprintf(stderr, "MaxEnt normalization factor = %f\n", Z);
	//char	comment[128];
	//sprintf(comment, "%f", Z_robust / Z);
	//itsdb_comment(comment);
	//fprintf(stderr, "memory usage = %.1fmb\n", (double)slab_usage()/(1024*1024));

	if(hyp_timer==-1)hyp_timer = new_timer("hypothesize");
	if(inst_timer==-1)inst_timer = new_timer("instantiate");
	if(mrs_timer==-1)mrs_timer = new_timer("mrs");
	while( !(nbest && count>=nbest) )
	{
		start_timer(hyp_timer);
		hyp = process_hypagenda(&agenda);
		stop_timer(hyp_timer, 1);
		if(!hyp)break;
		nhyp++;
		DEBUG("try a hyp %p score %f ind %d on decomp %p [", hyp, hyp->score, hyp->indexlist[0], hyp->dec);
		int k;
		for(k=0;k<hyp->arity;k++)
			DEBUG("%s#%d", k?" ":"", hyp->dec->rhs[k]->id);
		DEBUG("] of edge #%d\n", hyp->edge->id);
		start_timer(inst_timer);
		int	ires = instantiate_hypothesis(hyp);
		stop_timer(inst_timer, 1);
		DEBUG("instantiation result = %d\n", ires);
		if(0 == ires)
		{
			ninsthyps++;
			if(is_root(hyp->dg))
			{
				struct mrs	*m = NULL;
				if(want_mrs)
				{
					extern int ncleanup_rules, inhibit_vpm;
					if(ncleanup_rules > 0)inhibit_vpm++;
					start_timer(mrs_timer);
					m = extract_mrs(hyp->dg);
					stop_timer(mrs_timer, 1);
					if(ncleanup_rules > 0)
					{
						inhibit_vpm--;
						m = cleanup_mrs(m);	// both for parsing and generation
						//m = internal_to_external_mrs(m);
					}
				}
				int idiomatic = check_idioms(hyp->dg, m);
				if(!idiomatic && (g_mode == GENERATING))
				{
					if(!complained_about_unidiomatic_input)
					{
						complained_about_unidiomatic_input = 1;
						fprintf(stderr, "NOTE: generated unidiomatic output; is the generator input idiomatic?\n");
					}
				}
				extern int trace;
				if(trace>2)
				{
					printf("UNIDIOMATIC:\n");
					print_mrs(m);printf("\n");
				}
				if(idiomatic || (g_mode == GENERATING))
				{
					//printf("hyp = %p\n", hyp);
					//printf("\n"); print_hypothesis(hyp, printf, 0); printf("\n");
					if(g_mode == GENERATING)
						fixup_generator_string(hyp);
					double	probability = exp((double)hyp->score) / Z;
					count += process(hyp, m, probability);
				}
			}
			else DEBUG("... wasn't root after unpacking\n");
		}
		else g_checkup++;	// mark that we need to look for subfailures before hypothesizing
		if((slab_usage() / (1024*1024)) >= max_unpack_megabytes && !arbiter_request_memory())
			longjmp(out_of_memory_jump, 1);
	}
resume_after_oom:;
	if(!count)
	{
		struct edge	*dublin_last_ditch_root_edge();
		struct edge	*last_ditch = dublin_last_ditch_root_edge();
		struct hypothesis	*last_ditch_h = last_ditch?cheap_hypothesis(last_ditch,0):NULL;
		if(last_ditch_h)
		{
			if(0 == instantiate_hypothesis(last_ditch_h))
			{
				struct mrs	*m = NULL;
				if(want_mrs)
				{
					extern int ncleanup_rules, inhibit_vpm;
					if(ncleanup_rules > 0)inhibit_vpm++;
					start_timer(mrs_timer);
					m = extract_mrs(last_ditch_h->dg);
					stop_timer(mrs_timer, 1);
					if(ncleanup_rules > 0)
					{
						inhibit_vpm--;
						m = cleanup_mrs(m);	// both for parsing and generation
						//m = internal_to_external_mrs(m);
					}
				}
	#define	LAST_DITCH_PROBABILITY	1E-10
				fprintf(stderr, "NOTE: using dublin tree as last ditch offering\n");
				process(last_ditch_h, m, LAST_DITCH_PROBABILITY);
				count++;
			}
			else fprintf(stderr, "NOTE: couldn't instantiate dublin hypothesis\n");
		}
	}
	if(debug_level)
	{
		printf("%d hyps / %d reconstructed / %d readings\n", nhyp, ninsthyps, count);
		printf("%lld decompositions produced for %lld passive edges\n", totaldecompositions, ndecomposed);
	}
	/*for(i=0;i<chart_size;i++)
	{
		for(j=i+2;j<chart_size;j++)
		{
			struct chart_cell	*c = cells + i*chart_size + j;
			int k;
			for(k=0;k<c->p_nedges;k++)
			{
				struct edge	*E = c->p_edges[k];
				int l;
				for(l=-1;l<E->npack;l++)
				{
					struct edge	*e = (l==-1)?E:E->pack[l];
					struct unpack_info	*u = e->unpack;
					if(u)
					{
						int m;
						for(m=0;m<u->ncuis;m++)
						{
							int o, ns = 0;
							for(o=0;o<u->cuis[m]->nhypotheses;o++)
							{
								int	ires = instantiate_hypothesis(u->cuis[m]->hypotheses[o]);
								if(ires == 0)ns++;
							}
							printf("edge #%d cui %d had %d hypotheses ; %d instantiate\n", e->id, m, u->cuis[m]->nhypotheses, ns);
						}
					}
				}
			}
		}
	}*/
	return count;
}

void report_unpacking()
{
	if(!debug_level)return;
	fprintf(stderr, "%d total hypotheses generated\n", total_hyps);
	fprintf(stderr, "%lld total nodes reconstructed\n", total_reconstructed_nodes);
}

char	*slab_escape(char	*str)
{
	int	len = strlen(str) * 2 + 1;
	len -= len%4; len += 4;
	char	*esc = slab_alloc(len), *ep = esc;
	while(*str)
	{
		if(*str=='\\' || *str=='"')
			*ep++ = '\\';
		*ep++ = *str++;
	}
	*ep = 0;
	return esc;
}

char	*slab_unescape(char	*str)
{
	char	*out = freeze_string(str), *p = out, *q = str;

	while(*q)
	{
		if(*q=='\\' && q[1])
		{
			q+=2;
			switch(q[-1])
			{
				case	'\'':	*p++ = '\'';	break;
				case	'\"':	*p++ = '\"';	break;
				default:
					// preserve escapes we don't understand
					*p++ = '\\';
					*p++ = q[-1];
					break;
			}
		}
		else *p++ = *q++;
	}
	*p = 0;
	return out;
}
