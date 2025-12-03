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
#ifdef POST
#include "post.h"
#endif
#include	"token.h"
#include	"type.h"
#include	"tnt.h"

extern int trace;

int enable_tnt = 0;

int	enable_token_avms = 0;

char	*get_token_carg(struct token	*t)
{
	struct dg	*c = dg_hop(t->dg, lookup_fname("+CARG"));
	if(c && c->xtype->name[0]=='"')
	{
		char	buffer[1024];
		sprintf(buffer, "%.*s", (int)(strlen(c->xtype->name+1)-1), c->xtype->name+1);
		return freeze_string(buffer);
	}
	return NULL;
}

struct dg	*new_dag_for_unfrozen_string(char	*str)
{
	str = freeze_string(str);
	struct type	*ty = add_string(str);
	struct dg	*dg = atomic_dg(top_type);
	dg->type = dg->xtype = ty;
	return dg;
}

struct dg	*build_one_pos_tags_list(char	*tag, struct dg	*rest)
{
	// jacy POS tags are loooong...
	//char	tag_str[32];
	char	*tag_str = malloc(strlen(tag)+3);
	if(tag)sprintf(tag_str, "\"%s\"", tag);
	struct dg	*list = atomic_dg(g_cons_type);
	struct dg	*tagdg = tag?new_dag_for_unfrozen_string(tag_str):atomic_dg(default_type_hierarchy()->strtype->name);
	list = add_dg_hop(list, 1, tagdg);	// FIRST
	list = add_dg_hop(list, 2, rest?:type_dg(g_null_type));	// REST
	free(tag_str);
	return list;
}

struct dg	*build_pos_tags_list(int	ntags, struct postag	*tags)
{
	int i;
	struct dg	*rest = type_dg(g_null_type);
	for(i=ntags-1;i>=0;i--)
		rest = build_one_pos_tags_list(tags[i].tag, rest);
	return rest;
}

struct dg	*build_pos_prbs_list(int	ntags, struct postag	*tags)
{
	int i;
	struct dg	*rest = type_dg(g_null_type);
	for(i=ntags-1;i>=0;i--)
		rest = build_one_pos_tags_list(tags[i].prob, rest);
	return rest;
}

struct dg	*build_id_list(int	nids, int	*ids, struct dg	**last)
{
	if(nids<=0)
	{
		*last = type_dg(g_list_type);
		return *last;
	}
	struct dg	*rest = build_id_list(nids-1, ids+1, last);
	struct dg	*list = atomic_dg(g_cons_type);
	char		idstr[1024];
	sprintf(idstr, "\"%d\"", ids[0]);
	struct dg	*iddg = new_dag_for_unfrozen_string(idstr);
	list = add_dg_hop(list, 1, iddg);
	list = add_dg_hop(list, 2, rest);
	return list;
}

struct dg	*build_id_dlist(int	nids, int	*ids)
{
	struct dg	*dl = atomic_dg(g_diff_list_type);
	struct dg	*last = NULL;
	dl = add_dg_feature(dl, "LIST", build_id_list(nids, ids, &last));
	dl = add_dg_feature(dl, "LAST", last);
	return dl;
}

void	build_token_dag(struct token	*t)
{
	struct dg	*dg = type_dg(token_type);
	char	c_from_str[16], c_to_str[16];
	char	bigger_string[1024];

char	*slab_escape(char*);
	sprintf(bigger_string, "\"%s\"", slab_escape(t->string));
	sprintf(c_from_str, "\"%d\"", t->cfrom);
	sprintf(c_to_str, "\"%d\"", t->cto);
	//print_dg(dg);
	dg = dg_path_add(dg, token_form_path, new_dag_for_unfrozen_string(bigger_string));
	dg = dg_path_add(dg, token_from_path, new_dag_for_unfrozen_string(c_from_str));
	dg = dg_path_add(dg, token_to_path, new_dag_for_unfrozen_string(c_to_str));
	dg = dg_path_add(dg, token_postags_path, build_pos_tags_list(t->npostags, t->postags));
	dg = dg_path_add(dg, token_posprobs_path, build_pos_prbs_list(t->npostags, t->postags));
	dg = dg_path_add(dg, token_id_path, build_id_dlist(t->nids, t->ids));
	dg = wellform_dg(dg);
	assert(dg != NULL);
	t->dg = dg;
	//printf("token '%s' pos '%s'\n", t->string, t->postag);
}

struct lattice	*build_token_chart(int	nwords, char	**words, int	*cfrom, int	*cto)
{
	struct lattice	*tc = slab_alloc(sizeof(*tc));
	int	i;

	int		*ntags = calloc(sizeof(int),nwords);
	char	***tags = calloc(sizeof(char**),nwords);
	char	***probs = calloc(sizeof(char**),nwords);
	int		*unk = malloc(sizeof(int)*nwords);

	if(enable_tnt)
	{
		struct tnt_result	results[nwords];
		int res = tnt_tag_sequence(nwords, words, results);
		if(res == 0)
		{
			// TODO complete filling in ntags, tags, probs properly
			// also write build_pos_tags_list() with new fingerprint...
			// also see what other parts of the code used to refer to token->postag and now need to be changed
			for(i=0;i<nwords;i++)
			{
				ntags[i] = results[i].ntags;
				tags[i] = malloc(sizeof(char*) * ntags[i]);
				probs[i] = malloc(sizeof(char*) * ntags[i]);
				int j;
				for(j=0;j<ntags[i];j++)
				{
					tags[i][j] = results[i].tags[j].tag;
					char	p[64];
					sprintf(p, "%f", results[i].tags[j].prob);
					probs[i][j] = freeze_string(p);
				}
				unk[i] = 0;
			}
		}
	}
	else if(enable_post)
	{
#ifdef	POST
		char	*tags1[nwords];
		char	*one = freeze_string("1.0");
		post_tag_sequence(nwords, words, tags1, unk);
		for(i=0;i<nwords;i++)
		{
			ntags[i] = 1;
			tags[i] = malloc(sizeof(char*));
			tags[i][0] = tags1[i];
			probs[i] = malloc(sizeof(char*));
			probs[i][0] = one;
		}
#else
		assert(!"grammar built for POS tagging, but ACE built without tagger.");
#endif
	}
	else for(i=0;i<nwords;i++)
	{
		tags[i] = NULL;//"NNP";
		unk[i] = 1;
	}
	if(trace)
	{
		for(i=0;i<nwords;i++)fprintf(stderr, "%s/%s%s ", words[i], tags[i]?tags[i][0]:NULL, unk[i]?"?":"");
		fprintf(stderr, "\n");
	}

	bzero(tc, sizeof(*tc));
	for(i=0;i<=nwords;i++)new_lattice_vertex(tc);
	tc->start = tc->vertices[0];
	tc->end = tc->vertices[nwords];
	tc->nedges = nwords;
	tc->edges = slab_alloc(sizeof(struct lattice_edge*)*tc->nedges);
	for(i=0;i<tc->nedges;i++)
	{
		struct lattice_vertex	*vfrom = tc->vertices[i];
		struct lattice_vertex	*vto = tc->vertices[i+1];
		struct lattice_edge	*e = slab_alloc(sizeof(*e));
		e->from = vfrom;
		e->to = vto;
		e->token = slab_alloc(sizeof(struct token));
		bzero(e->token, sizeof(struct token));
		tc->edges[i] = e;
		add_lattice_vertex_follower(vfrom, e);
		e->token->eid = next_eid();
		e->token->npostags = ntags[i];
		e->token->postags = slab_alloc(sizeof(struct postag)*ntags[i]);
		int j;
		for(j=0;j<ntags[i];j++)
		{
			e->token->postags[j].tag = tags[i][j];
			e->token->postags[j].prob = probs[i][j];
		}
		e->token->nids = 1;
		e->token->ids = slab_alloc(sizeof(int));
		e->token->ids[0] = i;
		e->token->string = freeze_string(words[i]);
		e->token->cfrom = cfrom[i];
		e->token->cto = cto[i];
		if(enable_token_avms)
			build_token_dag(e->token);
		e->token->oc = NULL;
		free(tags[i]);
		free(probs[i]);
	}
	free(tags);
	free(unk);
	free(ntags);
	free(probs);
	tc->lattice_vertex_id_gen = 10000;
	return tc;
}

static void _mark_followers(struct lattice_vertex	*v)
{
	int i;
	if(v->mark)return;
	v->mark = 1;
	for(i=0;i<v->nfollowers;i++)
		_mark_followers(v->followers[i]->to);
}

int	lattice_vertex_follows(struct lattice	*lat, struct lattice_vertex	*a, struct lattice_vertex	*b)
{
	int i;
	if(a==b)return 0;
	for(i=0;i<lat->nvertices;i++)lat->vertices[i]->mark = 0;
	_mark_followers(b);
	return a->mark;
}

void	sort_lattice(struct lattice	*tc)
{
	/* assign consecutive numbers to each vertex,
	 * consistent with the order implied by the edges in the chart.
	 * these become the numbered vertices of the parse chart...
	 */

	assert(tc->start && tc->end);

	// traverse the lattice, assigning IDs in reverse order as we leave
	int i, id = tc->nvertices - 1;
	for(i=0;i<tc->nvertices;i++)
		tc->vertices[i]->mark = 0;
	// the idea is that once we can guarantee that everything following 'v' already has a number > 'id', it is safe to assign 'id' to 'v'.
	void traverse(struct lattice_vertex	*v)
	{
		int j;
		if(v->mark)return;	// already got an id.
		for(j=0;j<v->nfollowers;j++)
			traverse(v->followers[j]->to);
		v->id = id--;
		v->mark = 1;
	}
	traverse(tc->end);	// make sure tc->end gets the highest id
	for(i=0;i<tc->nvertices;i++)
		if(tc->vertices[i] != tc->start)
			traverse(tc->vertices[i]);
	traverse(tc->start);	// make sure tc->start gets the lowest id
	assert(id == -1);

	// to determine: do we need to sort the vertex array on the new IDs?
	tc->lattice_vertex_id_gen = tc->nvertices;
}

void	print_token_chart(struct lattice	*tc)
{
	int	i;
	for(i=0;i<tc->nedges;i++)
	{
		struct lattice_edge	*e = tc->edges[i];
		struct token	*t = e->token;
		printf("token #%d le %p vtx [%d-%d] char [%d-%d] string '%s' dag ",
			t->eid, e, e->from->id, e->to->id, t->cfrom, t->cto, t->string);
		if(enable_token_avms)
			print_dg(t->dg);
		printf("\n");
	}
}

int	test_first_token_in_lex_dg(struct dg	*le_dg, struct token	*tok)
{
	if(!enable_token_avms)return 0;
	struct dg	*toklist = dg_path(le_dg, lex_tokens_list_path);
	//printf(" .. token %s\n", tokens[i]->string);
	assert(toklist);
	struct dg	*lex_tok_dg = dg_hop(toklist, 1);	// FIRST
	if(lex_tok_dg)
	{
		//printf("candidate token site: "); print_dg(lex_tok_dg); printf("\n");
		int res = unify_dg_tmp(lex_tok_dg, tok->dg, -1);
		forget_tmp();
		if(res != 0)
		{
			//unify_backtrace();
			return -1;
		}
	}
	return 0;
}

struct dg	*build_token_list(int	n, struct token	**toks, struct dg	**last_token_dg)
{
	if(n<=0)return atomic_dg(g_null_type);
	struct dg	*list = atomic_dg(g_cons_type);
	struct dg	*first = copy_dg(toks[0]->dg);
	struct dg	*rest = build_token_list(n-1, toks+1, last_token_dg);
	if(n==1)*last_token_dg = first;
	list = add_dg_feature(list, "FIRST", first);
	list = add_dg_feature(list, "REST", rest);
	return list;
}

int	install_tokens_in_le(struct edge	*le, struct token	**tokens)
{
/*
	struct dg	*toklist = dg_path(le->dg, lex_tokens_list_path), *last_token_dg = NULL;
	int i;
	printf("installing tokens in lexeme '%s'\n", le->lex->word);
	for(i=0;i<le->lex->stemlen;i++)
	{
		printf(" .. token %s %p\n", tokens[i]->string, tokens[i]);
		assert(toklist);
		struct dg	*lex_tok_dg = dg_hop(toklist, 1);	// FIRST
		if(lex_tok_dg)
		{
			struct dg	*tok_dg = copy_dg(tokens[i]->dg);
			printf("candidate token site: "); print_dg(lex_tok_dg); printf("\n");
			if(0 != unify_dg_infrom(lex_tok_dg, tok_dg))
			{
				fprintf(stderr, " failed to unify token with lexeme!\n");
				printf("trying to unify in token dag:\n");
				print_dg(tokens[i]->dg);
				printf("\n");
#ifdef	UNIFY_PATHS
			unify_backtrace();
#endif
				return -1;
			}
			else printf("SUCESSFULLY unified in token dag\n");
			last_token_dg = lex_tok_dg;
		}
		else
		{
			last_token_dg = copy_dg(tokens[i]->dg);
			toklist = add_dg_hop(toklist, 1, last_token_dg);	// FIRST
		}
		if(i+1 < le->lex->stemlen)
		{
			struct dg	*rest = dg_hop(toklist, 2);	// REST
			if(!rest)
			{
				rest = type_dg(g_cons_type);
				toklist = add_dg_hop(toklist, 2, rest);	// REST
			}
			toklist = rest;
		}
	}
	struct dg	*toklast = dg_path(le->dg, lex_tokens_last_path);
	assert(toklast);
	if(0 != unify_dg_infrom(toklast, last_token_dg))
	{
		fprintf(stderr, " failed to unify tokens LAST pointer\n");
		return -1;
	}
*/

	assert(le->daughters == NULL);
	le->daughters = slab_alloc(sizeof(struct token*) * le->lex->stemlen);
	int	i;
	for(i=0;i<le->lex->stemlen;i++)
		le->daughters[i] = (struct edge*)tokens[i];

	if(!enable_token_avms)return 0;

	struct dg	*le_toklist = dg_path(le->dg, lex_tokens_list_path);
	struct dg	*le_toklast = dg_path(le->dg, lex_tokens_last_path);
	struct dg	*in_toklist, *in_toklast;
	if(!le_toklist || !le_toklast)
	{
		fprintf(stderr, "ERROR: toklist or toklast missing on a token\n");
		//fprintf(stderr, " ... for word: %s\n", le->lex->word);
		//print_dg(le->dg);printf("\n");
		return -1;
	}
	in_toklist = build_token_list(le->lex->stemlen, tokens, &in_toklast);
	//printf(" ... in_toklist.first = %p ; in_toklast = %p\n", dg_hop(in_toklist,lookup_fname("FIRST")), in_toklast);
	assert(le_toklist && le_toklast && in_toklist && in_toklast);

	if(0 != unify_dg_infrom(le_toklist, in_toklist))
	{
		if(trace) { fprintf(stderr, "failed to unify tokens LIST\n"); unify_backtrace(); }
		return -1;
	}
	if(0 != unify_dg_infrom(le_toklast, in_toklast))
	{
		if(trace) { fprintf(stderr, "failed to unify tokens LAST\n"); unify_backtrace(); }
		return -1;
	}

	//printf("after unify, le_toklast:\n");print_dg(le_toklast);printf("\n");
	//printf("after unify, in_toklast:\n");print_dg(in_toklast);printf("\n");

	//printf("lexeme dag:\n");
	//print_dg(le->dg);
	//printf("\n");

	return 0;
}
