#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

#include	"dag.h"
#include	"freeze.h"

static void flat_print_dg(struct dg	*d);

extern char	**fnames;
extern char	*unify_restrictor, *copy_restrictor;
void enable_trim(int trim);

#define PACKING_RESTRICTOR(label)	(unify_restrictor && unify_restrictor[label])
#define SHOULD_TRIM(label)			(copy_restrictor && copy_restrictor[label])

extern int	g_loaded;
extern unsigned int	generation;

struct copy_list
{
	int	count;
	struct dg	*copies[0];
};

struct copy_list	*extend_copy_list(struct copy_list	*cl, struct dg	*add)
{
	int	n = 1;
	if(cl)n = cl->count+1;
	struct copy_list	*ncl = slab_alloc(sizeof(struct copy_list) + sizeof(struct dg*)*n);
	ncl->count = n;
	if(cl)memcpy(ncl->copies, cl->copies, sizeof(struct dg*)*cl->count);
	ncl->copies[n-1] = add;
	return ncl;
}

struct dg	*intersect_copy_lists(struct copy_list	*a, struct copy_list	*b)
{
	int i, j;
	if(!a || !b)return NULL;
	for(i=0;i<a->count;i++)
		for(j=0;j<b->count;j++)
			if(a->copies[i] == b->copies[j])return a->copies[i];
	return NULL;
}

// returns a dg that subsumes both 'a' and 'b', possibly with reentrancies
// hopefully returns the most specific such dg?
struct dg	*generalize(struct dg	*a, struct dg	*b)
{
	struct type	*t, *t1, *t2;

	if(a->gen!=generation)a->copy=NULL;
	if(b->gen!=generation)b->copy=NULL;

	// see if there is a way 'a' and 'b' can agree on a reentrancy
	struct dg	*sc = intersect_copy_lists((struct copy_list*)a->copy, (struct copy_list*)b->copy);
	if(sc)return sc;

	// otherwise, we're making a new dg and adding it to both 'a' and 'b's copy lists

	a = dereference_dg(a);
	b = dereference_dg(b);
	t1 = (a->gen==generation)?a->type:a->xtype;
	t2 = (b->gen==generation)?b->type:b->xtype;

	t = lub(t1, t2);

	int	narcs = 0, i;
	if(t->dg)
	{
		for(i=0;i<t->dg->narcs;i++)
			if(!PACKING_RESTRICTOR(t->dg->label[i]) && !SHOULD_TRIM(t->dg->label[i]))
				narcs++;
	}
	int ab = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(narcs);
	struct dg	*g = slab_alloc(sizeof(struct dg) + ab + sizeof(struct dg*)*narcs), *aa, *bb;

	g->type = g->xtype = t;
	g->copy = NULL;
	g->narcs = 0;
	g->ncarcs = 0;
	g->forwarded = 0;
	g->carcs = NULL;
	g->narcs = narcs;
	g->gen = generation;
	narcs = 0;

	if(t->dg)
	{
		// consider all features that are appropriate to type 't'
		for(i=0;i<t->dg->narcs;i++)
		{
			if(PACKING_RESTRICTOR(t->dg->label[i]))continue;
			if(SHOULD_TRIM(t->dg->label[i]))continue;
			aa = dg_hop(a, t->dg->label[i]);
			bb = dg_hop(b, t->dg->label[i]);
			struct dg	*G = NULL;
			struct dg	*atomic_top();
			if(aa&&bb)G = generalize(aa,bb);
			else if(aa)G = generalize(aa,aa);
			else if(bb)G = generalize(bb,bb);
			else G = generalize(atomic_top(), atomic_top());
			/*if(!(aa&&bb))
			{
				if(aa)
				fprintf(stderr, "ERROR: feature '%s' missing from types '%s' and '%s' inheriting from '%s'\n",
					fnames[t->dg->label[i]], t1->name, t2->name, t->name);
				assert(aa && bb);
			}*/
			g->label[narcs] = t->dg->label[i];
			(DARCS(g))[narcs] = G;//generalize(aa, bb);
			narcs++;
		}
	}

	a->copy = (struct dg*)extend_copy_list((struct copy_list*)a->copy, g);
	b->copy = (struct dg*)extend_copy_list((struct copy_list*)b->copy, g);

	return g;
}

generalization_experiments()
{
	struct type	*t1 = lookup_type("s_coord_mid_eg_phr");
	struct type	*t2 = lookup_type("np_title_cmpnd_rule");

	enable_packing(1);
	enable_trim(1);

	printf("%s:\n", t1->name);
	print_dg(trim_copy(t1->dg));printf("\n");
	printf("%s:\n", t2->name);
	print_dg(trim_copy(t2->dg));printf("\n");
	generation++;
	int i;
	struct dg	*g;
	for(i=0;i<100000;i++)
	{
		generation++;
		g = generalize(t1->dg, t2->dg);
	}
	printf("generalization of %s and %s:\n", t1->name, t2->name);
	print_dg(g);printf("\n");
	enable_trim(0);
}
