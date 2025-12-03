#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>

#include	<assert.h>

#include	"hash.h"
#include	"type.h"

static int	shortcomp(const void	*a, const void	*b) { return *(unsigned short*)a - *(unsigned short*)b; }

void	add_to_type_daughters(struct type	*par, struct type	*d)
{
	par->ndaughters++;
	par->daughters = realloc(par->daughters, sizeof(struct type*)*par->ndaughters);
	par->daughters[par->ndaughters-1] = d;
}

void	recompute_type_daughters(struct type_hierarchy	*th)
{
	int	i, j;
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*t = th->types[i];
		if(t->daughters)free(t->daughters);
		t->daughters = NULL;
		t->ndaughters = 0;
	}
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*t = th->types[i];
		for(j=0;j<t->nparents;j++)
			add_to_type_daughters(t->parents[j], t);
	}
}

void	clear_descendents_and_daughters(struct type_hierarchy	*th)
{
	int i;
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*t = th->types[i];
		if(t->descendents)free(t->descendents);
		t->descendents = NULL;
		if(t->daughters)free(t->daughters);
		t->daughters = NULL;
	}
}

void	recompute_descendents(struct type	*t)
{
	if(t->descendents)return;
	int	max = 1, i;
	for(i=0;i<t->ndaughters;i++)
	{
		recompute_descendents(t->daughters[i]);
		max += t->daughters[i]->ndescendents;
	}
	unsigned short	*list = malloc(sizeof(unsigned short)*max);
	int	n = 1, j, k;
	list[0] = t->tnum;

	for(i=0;i<t->ndaughters;i++)
	{
		unsigned short	*dlist = t->daughters[i]->descendents, dn = t->daughters[i]->ndescendents;
		for(j=0;j<dn;j++)
			list[n++] = dlist[j];
	}
	// sort descendents and remove duplicates
	qsort(list, n, sizeof(short), shortcomp);
	assert(n == max);
	assert(n >= 1);
	for(i=n=1;i<max;i++)
		if(list[i] != list[n-1])
			list[n++] = list[i];

	t->ndescendents = n;
	t->descendents = realloc(list, sizeof(unsigned short) * n);
}

void	recompute_tnums(struct type_hierarchy	*th)
{
	int	i,j;

	struct type	**old_type_array;
	old_type_array = malloc(sizeof(struct type*) * th->ntypes);
	memcpy(old_type_array, th->types, sizeof(struct type*)*th->ntypes);

	// perform a topological sort of the type hierarchy,
	// storing the result in the types[] array, back to front.
	char	*have = calloc(1, th->ntypes);
	int idx = th->ntypes-1;
	void tsort(struct type	*t)
	{
		if(have[t->tnum])return;
		int i;
		for(i=0;i<t->ndaughters;i++)
			tsort(t->daughters[i]);
		have[t->tnum] = 1;
		assert(idx >= 0);
		th->types[idx--] = t;
	}
	tsort(th->top);
	assert(idx == -1);
	assert(th->types[0] == th->top);

	// renumber all the types
	//printf("renumbering\n");fflush(stdout);
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*T = th->types[i];
		T->tnum = i;
	}

	// renumber all the descendent arrays
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*T = th->types[i];
		for(j=0;j<T->ndescendents;j++)
			T->descendents[j] = old_type_array[T->descendents[j]]->tnum;
		qsort(T->descendents, T->ndescendents, sizeof(short), shortcomp);
	}

	free(old_type_array);
}

// FIXME
// the problem with recompute_descendents(),
// both for the old version of the GLB code and the new version,
// may be that types below a GLB type never get their ->parent[] array updated to include the new GLB type
//  -> the GLB type doesn't see any daughters
//  -> the GLB type doesn't see any descendents
// NOTE: this proved to be the case, for the old code.
//   i.e. after fixing that, a rebuild_hierarchy() after computing GLBs causes no noticeable damage.

// on input, the ->parents[] links must be correct.
// on output, the ->daughters[] links and ->descendents[] links have been recomputed,
// and the types[] array is reordered according to a topological sort.
rebuild_hierarchy(int	report_changes, struct type_hierarchy	*th)
{
	unsigned short	**old_d;
	int	i, *old_dn;
	if(report_changes)
	{
		old_d = malloc(sizeof(unsigned short*) * th->ntypes);
		old_dn = malloc(sizeof(int) * th->ntypes);
		for(i=0;i<th->ntypes;i++)
		{
			old_dn[i] = th->types[i]->ndescendents;
			old_d[i] = th->types[i]->descendents;
			th->types[i]->descendents = NULL;
			th->types[i]->ndescendents = 0;
		}
	}
	clear_descendents_and_daughters(th);
	recompute_type_daughters(th);
	recompute_descendents(th->top);
	if(report_changes)
	{
		for(i=0;i<th->ntypes;i++)
		{
			if(old_dn[i] != th->types[i]->ndescendents)
				printf("type '%s': had %d desc, now %d\n", th->types[i]->name, old_dn[i], th->types[i]->ndescendents);
		}
	}
	recompute_tnums(th);
}
