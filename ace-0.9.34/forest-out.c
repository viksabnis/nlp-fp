#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<stdarg.h>
#include	<wctype.h>

#include "dag.h"
#include "chart.h"
#include "lexicon.h"
#include "maxent.h"
#include "unpack.h"
#include "mrs.h"
#include	"token.h"
#include	"unicode.h"

void output_packed_tree(struct edge	*e, struct lattice	*tokens, int waspacked, int wasroot)
{
	if(e->unpack)return;
	e->unpack = (void*)1;
	char	*sign = e->rule?e->rule->name:e->lex->word;
	//char	*sign = e->rule?e->rule->name:e->lex->lextype->name;
	int	i;
	int type = 3;
	if(!e->rule)type=1;
	else if(e->rule->lexical)type=2;
	printf("(%d %s %d %d %d %d [", e->id, sign, e->from, e->to, (waspacked?4:0) | (wasroot?1:0), type);
	for(i=0;i<e->npack;i++)
	{
		if(i)printf(",");
		printf("%d", e->pack[i]->id);
	}
	printf("] (");
	if(!e->rule)
	{
		for(i=0;i<e->lex->stemlen;i++)
		{
			if(i)printf(",");
			printf("%d", ((struct token*)e->daughters[i])->eid);
		}
	}
	else
	{
		for(i=0;i<e->have;i++)
		{
			if(i)printf(",");
			printf("%d", e->daughters[i]->id);
		}
	}
	printf("))\n");
	for(i=0;i<e->npack;i++)output_packed_tree(e->pack[i], tokens, 1, wasroot);
	for(i=0;i<e->have;i++)output_packed_tree(e->daughters[i], tokens, 0, wasroot);
}

set_path_number(struct token	*T, struct path	path, int	n)
{
	char	str[16];
	sprintf(str, "\"%d\"", n);
	// this can in theory break reentrancies, if there's
	// already a node at this path and it's reentrant with somewhere else.
	struct dg	*new_dag_for_unfrozen_string(char	*str);
	T->dg = dg_path_add(T->dg, path, new_dag_for_unfrozen_string(str));
}

void	update_cfrom(struct token	*T, int	new_cfrom)
{
	if(T->cfrom == new_cfrom)return;
	T->cfrom = new_cfrom;
	// also update the AVM path
	set_path_number(T, token_from_path, new_cfrom);
}

void	update_cto(struct token	*T, int	new_cto)
{
	if(T->cto == new_cto)return;
	T->cto = new_cto;
	// also update the AVM path
	set_path_number(T, token_to_path, new_cto);
}

int reestimate_token_cto(struct token	*tok)
{
	//printf("ought to reestimate token '%s''s CTO\n", tok->string);
	extern char	current_sentence[];

	wchar_t	*wtok = towide(tok->string);
	// the following doesn't work in YY mode... since current_sentence is not available.
	wchar_t	*wsent = towide(current_sentence);
	int	slen = wcslen(wsent), tlen = wcslen(wtok);
	assert(tok->cfrom < slen);
	assert(tok->cfrom+tlen <= slen);
	int i;
	for(i=0;i<tlen;i++)
	{
		//printf("%C vs %C\n", wtok[i], wsent[tok->cfrom+i]);
		if(iswpunct(wtok[i]))
		{
			if(iswpunct(wsent[tok->cfrom+i]))continue;
			else break;
		}
		else
		{
			if(towlower(wsent[tok->cfrom+i]) == towlower(wtok[i]))continue;
			else break;
		}
	}
	free(wtok);
	free(wsent);
	//printf("first %d wide characters match\n", i);
	if(i == 0)return -1;
	update_cto(tok, tok->cfrom + i);
	return 0;
}

improve_token_lattice_characterization(struct lattice	*tokens)
{
	int	vtxcfrom[tokens->nvertices];
	int	vtxcfromn[tokens->nvertices];
	int	vtxcto[tokens->nvertices];
	int	vtxcton[tokens->nvertices];
	int i;
	for(i=0;i<tokens->nvertices;i++)vtxcfrom[i] = vtxcfromn[i] = vtxcto[i] = vtxcton[i] = 0;
	for(i=0;i<tokens->nedges;i++)
	{
		struct lattice_edge	*e = tokens->edges[i];
		int	from = e->from->id, to = e->to->id;
		struct token	*tok = e->token;
		int cfrom = tok->cfrom, cto = tok->cto;
		assert(from >= 0 && from < tokens->nvertices);
		assert(to >= 0 && to < tokens->nvertices);

		if(!vtxcfromn[from]) { vtxcfrom[from] = cfrom; vtxcfromn[from] = 1; }
		else if(vtxcfrom[from] != cfrom)vtxcfromn[from]++;	// count distinct values

		if(!vtxcton[to]) { vtxcto[to] = cto; vtxcton[to] = 1; }
		else if(vtxcto[to] != cto)vtxcton[to]++;	// count distinct values
	}
	char	suspicious[tokens->nvertices];
	for(i=0;i<tokens->nvertices;i++)
	{
		assert(vtxcfromn[i] <= 1);	// we would be surprised to find that two tokens starting at the same vertex had different CFROMs
		assert(vtxcton[i] <= 1);	// likewise CTOs

		suspicious[i] = 0;
		if(vtxcfromn[i] == 0 || vtxcton[i] == 0)continue;
		if(vtxcfrom[i] >= vtxcto[i])continue;	// normal; adjacent tokens are either immediately adjacent or have some whitespace
		//printf("vertex %d is suspect; as CTO=%d, as CFROM=%d\n", i, vtxcto[i], vtxcfrom[i]);
		// not normal: when used as CTO, this vertex is farther to the right than when used as CFROM
		// this means adjacent tokens overlap according to CFROM/CTO. this is an error in characterization from one or more of the tokens abutting this vtx.
		// look at each token abutting this vtx, and use hackery to estimate a new CFROM/CTO for whichever side of that token this vtx is on
		suspicious[i] = 1;
	}
	int progress, retry = 10;
do_retry:
	progress = 0;
	for(i=0;i<tokens->nedges;i++)
	{
		int from_susp = suspicious[tokens->edges[i]->from->id];
		int to_susp = suspicious[tokens->edges[i]->to->id];
		if(to_susp && !from_susp)
		{
			if(reestimate_token_cto(tokens->edges[i]->token) == -1)continue;
			int new_cto = tokens->edges[i]->token->cto;
			//printf("reestimated vertex %d at %d\n", tokens->edges[i]->to->id, new_cto);
			// go find everyone talking aobut the suspicious vertex and update them.
			// make both CFROM and CTO = this new value; this situation usually arises internally to a word, so we needn't allow for space between tokens.
			int j;
			for(j=0;j<tokens->nedges;j++)
			{
				struct token	*T = tokens->edges[j]->token;
				if(tokens->edges[j]->from == tokens->edges[i]->to)
					update_cfrom(T, new_cto);
				if(tokens->edges[j]->to == tokens->edges[i]->to)
					update_cto(T, new_cto);
			}
			suspicious[tokens->edges[i]->to->id] = 0;
			progress = 1;
		}
	}
	if(progress && retry-- > 0)goto do_retry;
}

char	*this_edge_is_root(struct edge	*edge);

output_forest(struct chart_cell	*cell, struct lattice	*tokens)
{
	int	i;
	int	found_root = 0;
	extern int do_forest;
	struct edge	*edge;
	// output rooted passive edges, and root-condition pseudoedges
	for(i=0;i<cell->p_nedges;i++)
	{
		edge = cell->p_edges[i];
		char	*symbol = this_edge_is_root(edge);
		if(symbol)
		{
			printf("root %d %d %d %d %s\n", next_eid(), edge->from, edge->to, edge->id, symbol);
			output_packed_tree(edge, tokens, 0, 1);
			found_root = 1;
		}
	}
	if(do_forest > 1)	// output all passive edges
	{
		int c;
		for(c=0;c<chart_size*chart_size;c++)
		{
			struct chart_cell	*cell = cells+c;
			for(i=0;i<cell->p_nedges;i++)
				output_packed_tree(cell->p_edges[i], tokens, 0, 0);
		}
	}
	// output an edge for each token
	extern int yy_mode;
	// if we have a reliable input string (i.e. we used repp), we can sometimes improve on the CFROM/CTO produced by token mapping.
	// this is useful for the treebanking tool...
	if(!yy_mode)improve_token_lattice_characterization(tokens);
	for(i=0;i<tokens->nedges;i++)
	{
		struct lattice_edge	*le = tokens->edges[i];
		struct token	*t = le->token;
		char	token_str[10240];
		if(enable_token_avms)
		{
			extern int dag_print_style;
			dag_print_style = 1;
			snprint_dg(token_str, 10239, t->dg);
			dag_print_style = 0;
		}
		else
		{
			//sprintf(token_str, "%s", t->string);
			char	*heap_escape(char	*str);
			char	*formesc = heap_escape(t->string);
			sprintf(token_str, "token [ +FROM \"%d\" +TO \"%d\" +FORM \"%s\" ]", t->cfrom, t->cto, formesc);
			free(formesc);
		}
		printf("token %d %d %d %d %s\n", t->eid, le->from->id, le->to->id, t->used, token_str);
	}
	return found_root;
}
