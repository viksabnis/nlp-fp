#include	<stdio.h>
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>

#include	"conf.h"
#include	"dag.h"
#include	"chart.h"
#include	"unpack.h"
#include	"rule.h"
#include	"type.h"
#include	"lexicon.h"
#include	"dag-provenance.h"

print_prov(struct dg_provenance	*p)
{
	switch(p->kind)
	{
		case	FROM_LUI_TREE:	printf("lui tree %s", p->arg0id);	break;
		case	FROM_LUI_EDGE:	printf("lui edge %s", p->arg0id);	break;
		case	FROM_TREE:	printf("tree %p / #%d", p->arg0ptr, ((struct hypothesis*)p->arg0ptr)->edge->id);	break;
		case	FROM_EDGE:	printf("edge #%d", ((struct edge*)p->arg0ptr)->id);	break;
		case	FROM_TYPE:	printf("type %s", ((struct type*)p->arg0ptr)->name);	break;
		case	FROM_TYPE_LOCAL:	printf("type %s local constraints", ((struct type*)p->arg0ptr)->name);	break;
		case	FROM_LEX:	printf("lexeme %s", ((struct lexeme*)p->arg0ptr)->word);	break;
		case	FROM_LEX_LOCAL:	printf("lexeme %s local constraints", ((struct lexeme*)p->arg0ptr)->word);	break;
		case	FROM_RULE:	printf("rule %s", ((struct rule*)p->arg0ptr)->name);	break;
		case	FROM_RULE_LOCAL:	printf("rule %s local constraints", ((struct rule*)p->arg0ptr)->name);	break;
		case	FROM_UNIFY:	printf("interactive unification");	break;
	}
}

show_provenance(struct path	path, struct dg_provenance	*p)
{
	printf("computing provenance of path ");
	print_path(path);
	printf(" in a dag\n");
	struct edge	*e = NULL;
	struct hypothesis	*h = NULL;
	switch(p->kind)
	{
		case	FROM_LUI_TREE:
			printf("that dag comes from tree LUI#=%s\n", p->arg0id);
			h = lui_find_tree(p->arg0id);
			assert(h);
			e = h->edge;
			goto got_edge;
		case	FROM_LUI_EDGE:
			printf("that dag comes from edge LUI#=%s\n", p->arg0id);
			e = lui_find_edge(p->arg0id);
			goto got_edge;
		case	FROM_TREE:
			h = p->arg0ptr;
			printf("that dag comes from hypothesis %p\n", h);
			e = h->edge;
			goto got_edge;
		case	FROM_EDGE:
			e = p->arg0ptr;
			printf("that comes from edge %p\n", e);
			got_edge:
			assert(e);
			printf(" ... which is edge #%d\n", e->id);
			if(e->rule)
			{
				printf(" = rule %s\n", e->rule->name);
				assert(e->have==e->need);
				struct dg_provenance	rp;
				rp.kind = FROM_RULE;
				rp.arg0ptr = e->rule;
				int i;
				int	arglist[e->have];
				struct dg		*dglist[e->have];
				struct dg_provenance	provlist[e->have];
				struct dg_provenance	*provptrlist[e->have];
				for(i=0;i<e->have;i++)
				{
					printf("  + edge #%d\n", e->daughters[i]->id);
					arglist[i] = i;
					if(p->kind == FROM_EDGE || p->kind == FROM_LUI_EDGE)
					{
						provlist[i].kind = FROM_EDGE;
						provlist[i].arg0ptr = e->daughters[i];
						dglist[i] = e->daughters[i]->dg;
					}
					else
					{
						assert(h != NULL);
						provlist[i].kind = FROM_TREE;
						provlist[i].arg0ptr = h->rhslist[i];
						dglist[i] = h->rhslist[i]->dg;
					}
					provptrlist[i] = &provlist[i];
				}
				show_provenance_from_unification(path, e->rule->dg, &rp, e->have, dglist, provptrlist, arglist);
			}
			else
			{
				show_provenance_from_lexeme(path, e->lex);
			}
			break;
		case	FROM_LEX_LOCAL:;
			struct lexeme	*lex = p->arg0ptr;
			printf("that comes from the immediate constraints on lexeme %s\n", lex->word);
			break;
		case	FROM_TYPE:;
			struct type	*type = p->arg0ptr;
			printf("that comes from constraints on type %s\n", type->name);
			show_provenance_in_type(path, type);
			break;
		case	FROM_TYPE_LOCAL:;
			type = p->arg0ptr;
			printf("that comes from the immediate constraints on type %s\n", type->name);
			break;
		case	FROM_RULE:;
			struct rule	*r = p->arg0ptr;
			printf("that comes from constraints on rule %s\n", r->name);
			break;
		case	FROM_RULE_LOCAL:;
			r = p->arg0ptr;
			printf("that comes from the immediate constraints on rule %s\n", r->name);
			break;
		case	FROM_LEX:;
			struct lexeme	*l = p->arg0ptr;
			printf("that comes from constraints on lexeme %s\n", l->word);
			show_provenance_from_lexeme(path, l);
			break;
		default:
			printf("that comes from provenance type %d\n", p->kind);
			break;
	}
}

void	collect_paths(struct dg	*from, struct dg	*to, int	*N, struct path	**P, int	len, int	*path)
{
	from = dereference_dg(from);
	if(from==to)
	{
		struct path	p;
		p.count = len;
		p.fnums = malloc(sizeof(int)*len);
		memcpy(p.fnums, path, sizeof(int)*len);
		(*N)++;
		*P = realloc(*P,sizeof(struct path)*(*N));
		(*P)[(*N)-1] = p;
	}
	if(len>=1000)
	{
		fprintf(stderr, "surprisingly deep dag (1000 levels); terminating search\n");
		return;
	}
	int	i;
	struct dg	**darcs = DARCS(from);
	for(i=0;i<from->narcs;i++)
	{
		path[len] = from->label[i];
		collect_paths(darcs[i], to, N, P, len+1, path);
	}
	extern unsigned int generation;
	if(from->gen != generation)return;
	for(i=0;i<from->ncarcs;i++)
	{
		path[len] = from->carcs[i].label;
		collect_paths(from->carcs[i].dest, to, N, P, len+1, path);
	}
}

struct path	arg_subpath(struct path	p, int	arg)
{
	struct path	p2 = p;
	if(arg==-1)return p;
	// get a shortened path, making sure it's actually inside the right arg
	if(!p2.count-- || *p2.fnums++!=lookup_fname("ARGS"))assert(!"no such arg subpath");
	while(arg-->0)
		if(!p2.count-- || *p2.fnums++!=lookup_fname("REST"))assert(!"no such arg subpath");
	if(!p2.count-- || *p2.fnums++!=lookup_fname("FIRST"))assert(!"no such arg subpath");
	return p2;
}

struct dg	*dg_path_in_arg(struct dg	*from, struct path	p, int	arg)
{
	struct path	p2 = p;
	if(arg==-1)return dg_path(from, p);
	// get a shortened path, making sure it's actually inside the right arg
	if(!p2.count-- || *p2.fnums++!=lookup_fname("ARGS"))return NULL;
	while(arg-->0)
		if(!p2.count-- || *p2.fnums++!=lookup_fname("REST"))return NULL;
	if(!p2.count-- || *p2.fnums++!=lookup_fname("FIRST"))return NULL;
	return dg_path(from, p2);
}

show_provenance_from_unification(struct path	path, struct dg	*left, struct dg_provenance	*leftp, int	nright, struct dg	**rightlist, struct dg_provenance	**rightplist, int	*rightarglist)
{
	// make copies so we don't see any structure sharing
	//printf("right0 on input:\n"); print_dg(rightlist[0]);printf("\n");
	enable_packing(0);
	left = copy_dg(left);
	int	i,s;
	for(i=0;i<nright;i++)
		rightlist[i] = copy_dg(rightlist[i]);
	for(i=0;i<nright;i++)
	{
		int	result = unify_dg_tmp(rightlist[i], left, rightarglist[i]);
		if(result)
		{
			unify_backtrace();
			assert(result==0);
		}
	}
	struct dg	*node = dg_path(left, path);
	if(!node)
	{
		printf("SURPRISE: that path is missing.  weird.\n");
		printf("wanted path: "); print_path(path); printf("\n");
		print_within_generation(left);
		printf("\n");
		assert(node != NULL);
	}
	extern unsigned int	generation;
	struct type	*t = (node->gen==generation)?node->type:node->xtype;
	printf("unified value is %s\n", t->name);
	int		nupaths = 0;
	struct path	*upaths = NULL;
	int		pathstack[1024];
	collect_paths(left, node, &nupaths, &upaths, 0, pathstack);
	forget_tmp();
	struct type	*g = get_top();
	int		ndghit = 0;
	struct dg	**dghit = NULL;
	struct dg_provenance	**dghitprov = NULL;
	int			*dghitpath = NULL, *dghitarg = NULL;
	int	sufficienti=-1, sufficientd;
	for(i=0;i<nupaths;i++)
	{
		printf("that node can be reached at: "); print_path(upaths[i]); printf("\n");
		for(s=-1;s<nright;s++)
		{
			struct dg	*side;
			struct dg_provenance	*sidep;
			if(s==-1)
			{
				side = dg_path(left, upaths[i]);
				sidep = leftp;
			}
			else
			{
				side = dg_path_in_arg(rightlist[s], upaths[i], rightarglist[s]);
				sidep = rightplist[s];
			}
			//struct dg	*side = dg_path(s?left:right, upaths[i]);
			//struct dg_provenance	*sidep = s?leftp:rightp;
			if(!side)
			{
				printf("	");
				print_prov(sidep);
				printf(" -- no value there at all\n");
				continue;
			}
			int	j;
			for(j=0;j<ndghit;j++)
				if(dghit[j]==side)break;
			if(j<ndghit)
			{
				printf("	");
				print_prov(sidep);
				printf(" -- node was already seen at a different path\n");
				continue;
			}
			ndghit++;
			dghit = realloc(dghit,sizeof(struct dg*)*ndghit);
			dghitprov = realloc(dghitprov,sizeof(struct dg_provenance*)*ndghit);
			dghitpath = realloc(dghitpath,sizeof(int)*ndghit);
			dghitarg = realloc(dghitarg,sizeof(int)*ndghit);
			dghit[ndghit-1] = side;
			dghitprov[ndghit-1] = sidep;
			dghitpath[ndghit-1] = i;
			dghitarg[ndghit-1] = (s==-1)?-1:rightarglist[s];
			struct type	*stype = side->xtype;
			printf("	");
			print_prov(sidep);
			printf(" -- value before was %s\n", stype->name);
			if(stype==t)
			{
				sufficienti = i;
				sufficientd = ndghit-1;
			}
			struct type	*g2 = glb(g, stype);
			if(g!=g2)
			{
				if(g != get_top())
				{
					printf("	which lowers the GLB to %s\n", g2->name);
				}
				g = g2;
			}
		}
	}
	if(g == t)
	{
		printf("and that adequately explains the value '%s'\n", t->name);
	}
	else
	{
		printf("but that is not enough to explain '%s'; there must be type lowering higher in the AVM.\n", t->name);
	}
	if(sufficienti>=0)
	{
		printf("recursing on sufficient provenance from: ");
		print_prov(dghitprov[sufficientd]); printf("\n");
		struct path	subpath = arg_subpath(upaths[sufficienti], dghitarg[sufficientd]);
		show_provenance(subpath, dghitprov[sufficientd]);
	}
	else
	{
		printf("recursing on all %d sources:\n", ndghit);
		for(i=0;i<ndghit;i++)
		{
			print_prov(dghitprov[i]); printf("\n");
			struct path	subpath = arg_subpath(upaths[dghitpath[i]], dghitarg[i]);
			show_provenance(subpath, dghitprov[i]);
		}
	}
	if(upaths)free(upaths);
}

show_provenance_in_type(struct path	p, struct type	*t)
{
	assert(t->tdl);
	struct dg	*node = dg_path(t->dg, p);
	struct type	*value = node->xtype;
	char	*tdl = t->tdl->rhs;
	char	*bracket = strchr(tdl, '[');
	struct dg_provenance	local_prov;
	struct dg		*local;
	local_prov.kind = FROM_TYPE_LOCAL;
	local_prov.arg0ptr = t;
	if(!bracket)
		local = copy_dg(get_top()->dg);
	else
	{
		printf("reconstructing dg for local constraints: %s\n", bracket);
		struct dg	*localraw = dagify(strdup(bracket), NULL);
		struct dg	*rnode = dg_path(localraw, p);
		if(rnode && rnode->xtype==value)
		{
			printf("that value (%s) is present on the expanded local constraints for %s\n", value->name, t->name);
			return 0;
		}
		local = copy_dg(localraw);
		wellform(local, "provenance calculation");
		struct dg	*wnode = dg_path(local, p);
		if(wnode && wnode->xtype==value)
		{
			printf("that value (%s) is present on the expanded local constraints for %s, but only after wellformedness has applied\n", value->name, t->name);
			return 0;
		}
	}
	printf("that constraint is at least partially inherited\n");
	struct dg		*super[t->nparents];
	struct dg_provenance	superprov[t->nparents];
	struct dg_provenance	*superprovp[t->nparents];
	int			superarg[t->nparents];
	int i, nsuper = 0;
	for(i=0;i<t->nparents;i++)
	{
		// can safely skip constraints on parents that are GLB types, I think.
		// those will just be unification of the GLB type's parents, which in turn (ultimately) will be the authored parents. no new info, and it makes tracing to TDL harder.
		if(!strncmp(t->parents[i]->name, "g(", 2))continue;
		super[nsuper] = t->parents[i]->dg;
		superprovp[nsuper] = &superprov[nsuper];
		superarg[nsuper] = -1;
		superprov[nsuper].kind = FROM_TYPE;
		superprov[nsuper].arg0ptr = t->parents[i];
		nsuper++;
	}
	show_provenance_from_unification(p, local, &local_prov, nsuper, super, superprovp, superarg);
}

show_provenance_from_lexeme(struct path	p, struct lexeme	*lex)
{
	printf(" = lex %s\n", lex->word);
	printf("which is the unification of lextype %s with its lexent constraints\n", lex->lextype->name);
	struct dg_provenance	ltp, localp;
	bzero(&ltp,sizeof(ltp));
	bzero(&localp,sizeof(localp));
	ltp.kind = FROM_TYPE;
	ltp.arg0ptr = lex->lextype;
	localp.kind = FROM_LEX_LOCAL;
	localp.arg0ptr = lex;
	struct dg	*local = lex->dg;
	extern int enable_simple_form_lexicon;
	if(enable_simple_form_lexicon)local = expand_lexeme(lex);
	int	arg = -1;
	struct dg_provenance	*provlist = &localp;
	show_provenance_from_unification(p, lex->lextype->dg, &ltp, 1, &local, &provlist, &arg);
}
