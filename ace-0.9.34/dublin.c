#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

#include	"freeze.h"
#include	"token.h"
#include	"tree.h"
#include	"reconstruct.h"
#include	"csaw/csaw.h"

// approximation of the Dublin pub idea (conversation between sweaglesw and oe at SemEval 2014)
// take a robust parse as input (e.g. from csaw).  using robust unification, construct edges corresponding to all the nodes in that tree, and add them to the agenda for a full TFS parse.

int	enable_dublin = 0;

struct edge	*find_lex_edge(struct lattice	*lc, struct tree	*lt)
{
	struct lexeme	*lex = get_lex_by_name_hash(lt->label);
	struct tree	*tw = lt->daughters[0];
	int i, j;
	//fprintf(stderr, "want lexical edge %s [%d-%d]\n", lt->label, lt->tfrom, lt->tto);
	for(i=0;i<lc->nedges;i++)
	{
		struct edge	*e = lc->edges[i]->edge;
		while(e->rule)e = e->daughters[0];	// only want the lexemes, not lexical rules.
		if(e->from != lt->tfrom)continue;
		if(e->to != lt->tto)continue;
		if(e->lex != lex)continue;
		for(j=0;j<e->lex->stemlen;j++)
		{
			//printf("  token %d vs %d\n", ((struct token*)e->daughters[j])->eid, tw->tokenids[j]);
			if(((struct token*)e->daughters[j])->eid != tw->tokenids[j])break;
		}
		if(j<e->lex->stemlen)continue;
		//fprintf(stderr, "dublin lexical edge %s [%d-%d] = preexisting #%d\n", lt->label, lt->tfrom, lt->tto, e->id);
		return e;
	}
	assert(!"no such dublin lexeme");
	return NULL;
}

struct edge	*find_lexrule_edge(struct lattice	*lc, struct tree	*lt)
{
	int	i;
	struct rule	*rule = lookup_rule(lt->label);
	assert(rule != NULL);
	assert(lt->ndaughters == 1 && lt->daughters[0]->ndaughters==1);
	struct edge	*dtr;
	if(lt->daughters[0]->daughters[0]->ndaughters==0)dtr = find_lex_edge(lc, lt->daughters[0]);
	else dtr = find_lexrule_edge(lc, lt->daughters[0]);
	if(!dtr)return NULL;
	for(i=0;i<lc->nedges;i++)
	{
		struct edge	*e = lc->edges[i]->edge;
		if(e->from != lt->tfrom)continue;
		if(e->to != lt->tto)continue;
		while(e->rule)
		{
			// check all edges in this derivation; not all are visible from the top level of the lexical chart.
			if(e->rule == rule)
			{
				assert(e->have==1);
				if(e->daughters[0]==dtr)return e;
			}
			e = e->daughters[0];
		}
	}
	return NULL;
}

struct tree	*csaw_parse(char	*sentence);
extern char	*csaw_grammar_path;

static struct tree	*dublin_tree;
static struct edge	*dublin_root;

void dublin_robustness(struct lattice	*lexical_chart, char	*sentence)
{
	if(!enable_dublin)return;
	/*print_lexical_chart(lexical_chart);
	fflush(stdout);
	FILE	*f = fopen("/tmp/dublin","r");
	if(!f){perror("/tmp/dublin");exit(-1);}
	char	deriv[102400];
	int	l = fread(deriv, 1, 102399, f);
	assert(l>=0);
	deriv[l] = 0;
	struct tree	*t = string_to_tree(deriv);*/
	struct tree	*t = csaw_parse_lattice(lexical_chart);
	if(!t)
	{
		fprintf(stderr, "NOTE: no PCFG helper tree\n");
		dublin_root = NULL;
		dublin_tree = NULL;
		return;
	}
	//printf("DUBLIN tree:\n");
	//print_tree(t,0);
	void got_edge(struct tree	*tx, struct dg	*d)
	{
		int i;
		struct edge	*e = NULL;
		if(tx->ndaughters==1 && tx->daughters[0]->ndaughters==0)
		{
			// lexical; these should all be on the agenda already
			e = find_lex_edge(lexical_chart, tx);
			assert(e!=NULL);
			//printf("found preexisting lexeme edge #%d for dublin lex %s\n", e->id, e->lex->word);
		}
		else
		{
			struct rule	*r = lookup_rule(tx->label);
			assert(r != NULL);
			if(r->lexical)
			{
				//printf("looking for preexisting %s[%d-%d]\n", r->name, tx->tfrom, tx->tto);
				e = find_lexrule_edge(lexical_chart, tx);
			}
			if(!e)
			{
				e = slab_alloc(sizeof(*e));
				bzero(e,sizeof(*e));
				callable_generalize_certain_paths(d);	// bleach top-level type to 'sign' to be packable
				e->dg = d;
				e->from = tx->tfrom;
				e->to = tx->tto;
				e->id = next_eid();
				// rule
				e->rule = lookup_rule(tx->label);
				e->have = e->need = tx->ndaughters;
				e->daughters = slab_alloc(sizeof(void*)*e->have);
				for(i=0;i<tx->ndaughters;i++)
				{
					e->daughters[i] = (void*)tx->daughters[i]->lexhead;
					e->daughters[i]->built_on = 1;
				}
				if(e->rule->lexical)e->lex = e->daughters[0]->lex;
				e->qc = extract_qc(d);
				//printf("dublin rule edge #%d = %s\n", e->id, e->rule?e->rule->name:e->lex->word);
				add_agenda(e);
			}
			else
			{
				//printf("found preexisting lexical rule edge #%d for dublin rule %s\n", e->id, r->name);
			}
		}
		e->neps = -1;	// signal that this edge is part of the dublin tree.
		tx->lexhead = (void*)e;
	}
	t->lexhead = NULL;
	enable_robust_unification();
	reconstruct_tree(t, got_edge);
	disable_robust_unification();
	dublin_tree = t;
	dublin_root = (struct edge*)dublin_tree->lexhead;
}

int	dublin_tree_contains(char	*mother, int	from, int	to, char	*daughter, int	dfrom, int	dto)
{
	if(!dublin_tree)return 0;
	if(from==-1)
	{
		//printf("is %s over %s[%d-%d] dublin?\n", mother, daughter, dfrom, dto);
		// only know daughter span -- but it's definitely a non-unary.
		struct tree	*dtr = find_subtree_with_trange(dublin_tree, dfrom, dto);
		if(!dtr)return 0;
		if(dtr->tfrom!=dfrom || dtr->tto!=dto)return 0;
		//printf("that daughter span exists as %s\n", dtr->label);
		if(strcmp(dtr->label, daughter))return 0;
		struct tree	*node = dtr->parent;
		if(!node)return 0;
		//printf("its mother is %s\n", node->label);
		if(strcmp(node->label, mother))return 0;
		return 1;
	}
	else
	{
		// know mother span and daughter span
		//printf("is %s[%d-%d] over %s[%d-%d] in dublin?\n", mother, from, to, daughter, dfrom, dto);
		struct tree	*node = find_subtree_with_trange(dublin_tree, from, to);
		if(!node)return 0;
		if(node->tfrom!=from || node->tto!=to)return 0;
		while(node && node->ndaughters>0 && !(node->ndaughters==1 && node->daughters[0]->ndaughters==0))
		{
			// for each rule with this span...
			//printf("that mother span is present as %s...\n", node->label);
			if(!strcmp(node->label, mother))
			{
				// same as 'mother'; check whether 'daughter' is present
				int i;
				for(i=0;i<node->ndaughters;i++)
				{
					//printf(" daughter %s[%d-%d]\n", node->daughters[i]->label, node->daughters[i]->tfrom, node->daughters[i]->tto);
					if(!strcmp(node->daughters[i]->label, daughter) && node->daughters[i]->tfrom==dfrom && node->daughters[i]->tto==dto)
						return 1;
				}
			}
			node = node->daughters[0];
		}
		return 0;
	}
}

struct edge	*dublin_last_ditch_root_edge()
{
	if(dublin_root)return dublin_root;
}
