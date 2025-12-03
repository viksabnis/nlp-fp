#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<assert.h>
#include	<signal.h>

#include	"csaw.h"

#include	"../token.h"
#include	"../chart.h"
#include	"../lexicon.h"
#include	"../morpho.h"
#include	"../lexical-parse.h"
#include	"../unpack.h"
#include	"../tnt.h"

#include	"../reconstruct.h"

char	*csaw_grammar_path = NULL;

int	csaw_init(char	*grammar_path, char	*csaw_grammar_path)
{
	csaw_load_pcfg(csaw_grammar_path);
	return 0;
}

extern int	rooted_derivations;

extern int reconstruction_noise_level;

csaw_separate_punctuation(struct lattice	*lc, int	**Orig_vtx_ids)
{
	while(1)
	{
		int	i;
		// find a punctuation rule lurking somewhere
		struct rule	*pr = NULL;
		struct lattice_vertex	*to = NULL;
		for(i=0;i<lc->nedges;i++)
		{
			struct lattice_edge	*le = lc->edges[i];
			struct edge	*e = le->edge;
			if(e->rule && strstr(e->rule->name, "_plr"))
			{
				pr = e->rule;
				to = le->to;
				//printf("lattice edge %p triggered psplit\n", le);
				break;
			}
		}
		if(i==lc->nedges)break;
		assert(to != NULL);
		//printf("found punctuation %s lurking before vertex %d\n", pr->name, to->id);
		// add a new vertex 'mid'
		struct lattice_vertex	*new_lattice_vertex(struct lattice*);
		struct lattice_vertex	*mid = new_lattice_vertex(lc);
		// when we go back and patch things ending at 'mid' to have original vertex IDs, use `to'.
		assert(mid == lc->vertices[lc->nvertices-1]);
		(*Orig_vtx_ids) = realloc((*Orig_vtx_ids), sizeof(int) * lc->nvertices);
		// can't use to->id, because it might itself be a new punctuation midpoint; find its original ID.
		int	to_idx = 0;
		for(to_idx=0;to_idx<lc->nvertices;to_idx++)if(lc->vertices[to_idx]==to)break;
		assert(to_idx<lc->nvertices);
		(*Orig_vtx_ids)[lc->nvertices-1] = (*Orig_vtx_ids)[to_idx];
		// consider all edges ending at 'to'
		for(i=0;i<lc->nedges;i++)
		{
			// those with 'pr' as their first rule drop it and bridge to 'mid'
			struct lattice_edge	*le = lc->edges[i];
			if(le->to != to)continue;
			struct edge	*e = le->edge;
			if(!e->rule || strcmp(e->rule->name, pr->name))continue;
			//printf("lattice edge %p tweaked\n", le);
			le->edge = e->daughters[0];
			le->to = mid;
		}
		//add a punctuation token from 'mid' to 'to'
		struct lattice_edge	*punc = slab_alloc(sizeof(*punc));
		bzero(punc,sizeof(*punc));
		punc->from = mid;
		punc->to = to;
		struct edge	*new_edge(struct dg*);
		punc->edge = new_edge(NULL);
		punc->edge->lex = slab_alloc(sizeof(struct lexeme));
		bzero(punc->edge->lex, sizeof(struct lexeme));
		punc->edge->lex->word = "PUNC";
		punc->edge->lex->stemlen = 1;
		punc->edge->lex->lextype = slab_alloc(sizeof(struct type));
		bzero(punc->edge->lex->lextype, sizeof(struct type));
		punc->edge->lex->lextype->name = pr->name;
		//printf("punc %p from %p / %d to %p / %d\n", punc, punc->from, punc->from->id, punc->to, punc->to->id);
		struct token	*pt = slab_alloc(sizeof(struct token));
		bzero(pt,sizeof(*pt));
		pt->string = "PUNC";
		pt->dg = atomic_dg("token");
		punc->edge->daughters = malloc(sizeof(struct token**));
		punc->edge->daughters[0] = (struct edge*)pt;
		add_lattice_edge(lc, punc);
	}
}

int	csaw_repair_vertex(int	idx, int	nvtx, int	*vtx_id_map)
{
	while(idx<nvtx && vtx_id_map[idx]==-1)idx++;
	assert(idx<nvtx);
	return vtx_id_map[idx];
}

csaw_eliminate_unwanted_rules(struct lattice	*lc)
{
	int i;
	for(i=0;i<lc->nedges;i++)
	{
		struct lattice_edge	*le = lc->edges[i];
		struct edge	*e = le->edge, **Ep = &le->edge;
		while(e->rule)
		{
			if(!strcmp(e->rule->name, "w_italics_dlr"))
				*Ep = e->daughters[0];
			Ep = &e->daughters[0];
			e = e->daughters[0];
		}
	}
}

csaw_repair_spans(struct tree	*t, int	nvtx, int	*vtx_id_map)
{
	int i;
	t->tfrom = csaw_repair_vertex(t->tfrom, nvtx, vtx_id_map);
	t->tto = csaw_repair_vertex(t->tto, nvtx, vtx_id_map);
	for(i=0;i<t->ndaughters;i++)
		csaw_repair_spans(t->daughters[i], nvtx, vtx_id_map);
}

/*
struct tree	*duplicate_tree(struct tree	*t)
{
	struct tree	*T = calloc(sizeof(*T),1);
	*T = *t;
	T->label = strdup(t->label);
	T->tokens = malloc(sizeof(char*)*T->ntokens);
	int i;
	for(i=0;i<T->ntokens;i++)T->tokens[i] = strdup(t->tokens[i]);
	T->daughters = malloc(sizeof(struct tree*)*T->ndaughters);
	for(i=0;i<T->ndaughters;i++)T->daughters[i] = duplicate_tree(t->daughters[i]);
	return T;
}
*/

struct tree	*csaw_parse_lattice(struct lattice	*lexical_chart)
{
// up to here, same as normal ACE parsing; all we need(?) for rest of processing is `lexical_chart'
// need to make a copy of it to avoid overwriting the main parser's storage
	lexical_chart = duplicate_lexical_lattice(lexical_chart);

// prepare CSAW chart
	//printf("before separate_punctuation()...\n"); print_lexical_chart(lexical_chart);
	csaw_eliminate_unwanted_rules(lexical_chart);
	int	*orig_vtx_ids = orig_vtx_ids = malloc(sizeof(int)*lexical_chart->nvertices);
	int i;
	for(i=0;i<lexical_chart->nvertices;i++)
		orig_vtx_ids[i] = lexical_chart->vertices[i]->id;
	csaw_separate_punctuation(lexical_chart, &orig_vtx_ids);
	//printf("after separate_punctuation()...\n"); print_lexical_chart(lexical_chart);

	// put sensible from/to's on lexical edges
	sort_lattice(lexical_chart);
	int	vtx_id_map[lexical_chart->nvertices];
	for(i=0;i<lexical_chart->nvertices;i++)
		vtx_id_map[lexical_chart->vertices[i]->id] = orig_vtx_ids[i];
	for(i=0;i<lexical_chart->nedges;i++)
	{
		struct lattice_edge	*le = lexical_chart->edges[i];
		assert(le->edge != NULL);
		le->edge->from = le->from->id;
		le->edge->to = le->to->id;
	}

	csaw_reset_pcfg_tokens();
	clear_dstr_cache();
	extern int derivations_include_roots;
	int save_derivations_include_roots = derivations_include_roots;
	derivations_include_roots = 0;
	for(i=0;i<lexical_chart->nedges;i++)
	{
		struct lattice_edge	*e = lexical_chart->edges[i];
		struct edge	*t = e->edge;
		//printf("lexical edge #%d le %p vtx [%d-%d] lexeme '%s'\n",
			//t->id, e, e->from->id, e->to->id, t->lex->word);
		char	deriv[10240]="", pcfg_term[1024]="", *dp = deriv, *tp = pcfg_term;
		struct edge	*chain[128];
		int			nchain = 0;
		while(t && t->have)
		{
			//printf("lattice edge %p rule %s\n", e, t->rule->name);
			t->from = e->from->id;
			t->to = e->to->id;
			if(!strstr(t->rule->name, "_plr"))
			{
				chain[nchain++] = t;
				dp += sprintf(dp, "(%d %s 0.0 %d %d ", t->id, t->rule->name, e->from->id, e->to->id);
			}
			else fprintf(stderr, "WARNING: UNEXPECTED punctuation lexical rule %s left over in lexical chart!\n", t->rule->name);
			t = t->daughters[0];
		}
		assert(t && !t->have && t->lex);
		t->from = e->from->id;
		t->to = e->to->id;
		//fprintf(stderr, "setting %s to %d-%d\n", t->lex->word, t->from, t->to);
		struct hypothesis	*thyp = calloc(sizeof(*thyp),1);
		thyp->eid = t->id;
		thyp->toklen = e->to->id - e->from->id;
		thyp->edge = t;
		char	*lderiv = hypothesis_to_dstring_from(thyp, e->from->id);
		dp += sprintf(dp, "%s", lderiv);
		tp += sprintf(tp, "%s", t->lex->lextype->name);
		int j;
		for(j=nchain-1;j>=0;j--)
		{
			dp += sprintf(dp, ")");
			tp += sprintf(tp, "&%s", chain[j]->rule->name);
		}
		int	slen = 0;
		for(j=0;j<t->lex->stemlen;j++)
			slen += 1 + strlen(((struct token*)t->daughters[j])->string);
		char	*surface = malloc(1 + slen);
		*surface = 0;
		for(j=0;j<t->lex->stemlen;j++)
		{
			if(j)strcat(surface, " ");
			strcat(surface, ((struct token*)t->daughters[j])->string);
		}
		csaw_add_pcfg_token(e->from->id, e->to->id, strdup(pcfg_term), strdup(deriv), surface);
		//printf("term %s with surface '%s' ; chart %d - %d, orig %d - %d\n", pcfg_term, surface, t->from, t->to, vtx_id_map[t->from], vtx_id_map[t->to]);
		free(surface);
	}
	clear_dstr_cache();
	derivations_include_roots = save_derivations_include_roots;

	// parse and unpack best 1 tree
	struct tree	*found_tree = NULL;
	void visitor(struct tree	*t)
	{
		clear_mrs();
		csaw_denormalize_tree(t);
		csaw_repair_spans(t, lexical_chart->nvertices, vtx_id_map);
		found_tree = t;
	}

	csaw_parse_these_tokens(1, visitor);
	csaw_free_chart();
	return found_tree;
}
