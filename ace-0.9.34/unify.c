// implementation of Tomabechi's SS Quasi-Destructive Unifier

#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	"chart.h"
#include	"dag.h"
#include	"freeze.h"
#include	"conf.h"

static void flat_print_dg(struct dg	*d);

extern char	**fnames;
extern char	*unify_restrictor, *copy_restrictor;
void enable_trim(int trim);

extern int	g_loaded;

int	in_slash, slash_fname, xarg_fname, sind_fname, mod_fname;
extern int	glb_always_succeeds;

static inline int slash_restricted(int l)
{
	return 0;
	if(l == xarg_fname)return 1;
	if(l == sind_fname)return 1;
	if(l == mod_fname)return 1;
	return 0;
}

//#define SHOULD_TRIM(label)			(copy_restrictor && copy_restrictor[label])
// it is possible for glb constraints to pull features back in that our packing-restrictor'd rule and lexeme AVMs do not contain, so apply the packing restrictor when copying as well.
#define PACKING_RESTRICTOR(label)	(unify_restrictor && (unify_restrictor[label] || (in_slash && slash_restricted(label))))
#define SHOULD_TRIM(label)			((copy_restrictor && copy_restrictor[label]) || PACKING_RESTRICTOR(label))

// global generation counter for invalidating quasi-destructive operations
unsigned int	generation = 10;

// when freezing a grammar, start all copy generations at 10
void	null_generation() { generation = 10; }
struct darc	*realloc_carcs(struct darc	*ptr, int	old, int	new);

#define	MAX_COPY_PATH	1024
int	copypath[MAX_COPY_PATH + 10], copypathp;

#ifdef	UNIFY_PATHS
extern int	upath[MAX_COPY_PATH + 10];
extern int	upathl, upathgl;
extern struct type *uglb;
extern struct type	*ut1, *ut2;
#endif

#ifdef	COPY_COUNTS
long long copycount, copytraverse, copysharecount, copyreentcount;
#endif

long top_copies, top_unifies;

void dagreset_c(struct dg	*d);

static inline void	p_forward_dg(struct dg	*from, struct dg	*to)
{
	_set_forward(from, to);
	from->gen = 9;
	from->ncarcs = 0;
	from->carcs = 0;
}

void	permanent_forward_dg(struct dg	*from, struct dg	*to)
{
	p_forward_dg(from, to);
}

static inline void	forward_dg(struct dg	*from, struct dg	*to)
{
	_set_forward(from, to);
	if(from->gen != generation)
	{
		from->ncarcs = 0;
		from->carcs = 0;
		from->gen = generation;
	}
}

#define	HAVE_CHECK_CYCLES	1
#ifdef	HAVE_CHECK_CYCLES
// this is called from trimmed_portion_is_cyclic(),
// right after we copy_dg_with_comp_arcs_ss() some other portions of the dag.
// if we enter into a part that has been copied, that portion has already
// been shown to be cycle free, so skip out.
// the marker is that ->copy is a pointer and ->copy->gen is current
// also, if ->copy is 0x5, then copy() decided to share the node, and it is also known to be cycle-free.
int	check_cycles(struct dg	*dg)
{
	int	i;
	struct dg	**arcs;

	if(!dg)return -1;
	dg = dereference_dg(dg);
	if(!dg)return -1;

	if(dg->gen != generation)
	{
		dg->gen = generation;
		dg->forwarded = 0;
		dg->ncarcs = 0;
		dg->carcs = 0;
		dg->type = dg->xtype;
	}
	else if(dg->copy == (void*)1)return -1;
	else if(dg->copy == (void*)2)return 0;
	else if(dg->copy == (void*)5)return 0;	// copy() has been here (and shared)
	else if((void*)dg->copy > (void*)10 && dg->copy->gen == generation)
		return 0;	// copy() has been here and copied()
	dg->copy = (void*)1;

	arcs = DARCS(dg);
	for(i=0;i<dg->narcs;i++)
		if(check_cycles(arcs[i]))return -1;
	if(dg->gen == generation)for(i=0;i<dg->ncarcs;i++)
		if(check_cycles(dg->carcs[i].dest))return -1;
	dg->copy = (void*)2;
	return 0;
}
#endif

static struct dg	*copy_dg_no_comp_arcs(struct dg	*dg)
{
	struct dg	*newcopy;
	struct dg	**aptr, **optr;
	int		i;

	dg = p_dereference_dg(dg);
	if(!dg)return 0;

	// ignore mark left by check_cycles() et al
	if((unsigned long)dg->copy<=5)dg->copy = 0;

	if(dg->copy)return dg->copy;

	//int	ab = (dg->narcs-2+3)/4 * 4;
	int	ab = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(dg->narcs);
	newcopy = slab_alloc(sizeof(struct dg) + ab + sizeof(struct dg*)*dg->narcs);
	dg->copy = newcopy;
	*newcopy = *dg;
	newcopy->type = newcopy->xtype;
	newcopy->copy = 0;
	newcopy->ncarcs = 0;
	newcopy->carcs = 0;
	//newcopy->narcs = dg->narcs;
	assert(dg->gen != 9);	// we've already dereferenced it...
	//if(dg->gen==9){}//newcopy->gen = 9;
	//else
	//{
		newcopy->forwarded = 0;
		newcopy->gen = generation;
	//}
	memcpy(newcopy->label, dg->label, sizeof(unsigned short) * dg->narcs);
	aptr = DARCS(newcopy);
	optr = DARCS(dg);

	for(i=0;i<dg->narcs;i++)
	{
		*aptr = copy_dg_no_comp_arcs(*optr);
		if(!*aptr)return 0;
		aptr++; optr++;
	}
	return newcopy;
}

// robust unification needs to be robust to loops in addition to type clashes
struct dg	*copy_dg_with_comp_arcs_loopy(struct dg	*dg)
{
	struct dg	*newcopy;
	unsigned short	*alptr, *olptr;
	struct dg	**aptr, **optr;
	int		i, j;

	dg = dereference_dg(dg);
	if(!dg)return 0;

#ifdef	HAVE_CHECK_CYCLES
	// ignore mark left by check_cycles()
	if((unsigned long)dg->copy<=2)dg->copy = 0;
#endif

	if(dg->gen != generation)
	{
		dg->copy = 0;
		dg->forwarded = 0;
		dg->ncarcs = 0;
		dg->carcs = 0;
		dg->type = dg->xtype;
		dg->gen = generation;
	}
	else if(dg->copy)
	{
		/*if((unsigned long long)dg->copy == 3)
		{
			// cycle detected!
			//fprintf(stderr, "NOTE: cycle\n");
			return NULL;
		}*/
		if(dg->copy->gen == generation)
			return dg->copy;
		assert(!"not reached -- why would copy be set and not be up-to-generation?");
	}

	int	na = dg->narcs + dg->ncarcs;
	for(i=0;i<dg->narcs;i++)
		if(SHOULD_TRIM(dg->label[i]))na--;
	for(i=0;i<dg->ncarcs;i++)
		if(SHOULD_TRIM(dg->carcs[i].label))na--;

	//int	ab = (na-2 + 3)/4 * 4;
	int		ab = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(na);
	newcopy = slab_alloc(sizeof(struct dg) + ab + sizeof(struct dg*)*na);
	*newcopy = *dg;
	newcopy->xtype = newcopy->type = (dg->gen==generation)?dg->type:dg->xtype;
	newcopy->gen = generation;
	newcopy->copy = NULL;
	newcopy->ncarcs = 0;
	newcopy->carcs = NULL;
	newcopy->narcs = na;
	newcopy->forwarded = 0;
	alptr = newcopy->label;
	aptr = DARCS(newcopy);
	olptr = dg->label;
	optr = DARCS(dg);

	// set ->copy now, so cycles can be copied
	dg->copy = newcopy;

	for(j=0,i=0;i<dg->narcs || j<dg->ncarcs;) // mergesort
	{
		struct dg		*copyme;
		int				copylabel;
		if(j<dg->ncarcs && i<dg->narcs)
		{
			if(olptr[(int)i] < dg->carcs[(int)j].label)
			{
				copylabel = olptr[(int)i];
				copyme = optr[(int)i++];
			}
			else
			{
				copylabel = dg->carcs[(int)j].label;
				copyme = dg->carcs[(int)j++].dest;
			}
		}
		else if(i<dg->narcs)
		{
			copylabel = olptr[(int)i];
			copyme = optr[(int)i++];
		}
		else
		{
			copylabel = dg->carcs[(int)j].label;
			copyme = dg->carcs[(int)j++].dest;
		}
		if(SHOULD_TRIM(copylabel))
			continue;
		//fprintf(stderr, "copying primary `%s' arc from %s to %p\n",
		//		fnames[aptr->label], newcopy->xtype->name, xarc.dest);

		*alptr = copylabel;
		*aptr = copy_dg_with_comp_arcs_loopy(copyme);

		if(!*aptr)return NULL;
		aptr++; alptr++;
	}

	dg->copy = newcopy;
	return newcopy;
}

static int darc_cmp(const void	*a, const void	*b)
{
	return ((const struct darc*)a)->label - ((const struct darc*)b)->label;
}

static void print_copy_path(char	*name)
{
	int	i;

	printf("%s", name);
	for(i=0;i<copypathp;i++)
		printf(" %s.%d", fnames[copypath[i]], copypath[i]);
	printf("\n");
}

// we don't share FROZEN dags because we make epsilon edges that directly reference the rule in the frozen grammar, without copying.
// note that *lexical* edges do get copied before entering the chart.

#define	FROZENLY_UNSHARABLE(x)	FROZEN(x)

int discard_inappropriate_types_during_copy = 0;

static struct dg	*copy_dg_with_comp_arcs_ss(struct dg	*dg_underef, char	*chret)
{
extern struct darc	*carcstack;
	struct dg	*dg, **aptr, **optr;
	unsigned short	*alptr, *olptr;
	struct dg	*newcopy;
	char		forwarded, i, j, ch, st;
	struct slab_state	state;

	//slab_warm_cache();

#ifdef	COPY_COUNTS
	copytraverse++;
#endif
	dg = dereference_dg(dg_underef);
	if(!dg)return NULL;
	forwarded = (dg != dg_underef);

	if(dg->gen != generation)
	{
		dg->copy = 0;
		dg->forwarded = 0;
		dg->ncarcs = 0;
		dg->carcs = 0;
		dg->type = dg->xtype;
		dg->gen = generation;
		if(!dg->narcs && !FROZENLY_UNSHARABLE(dg))
		{
#ifdef	COPY_COUNTS
			copysharecount++;
#endif
			goto share;
		}
	}
	else
	{
#ifdef	HAVE_CHECK_CYCLES
		// ignore mark left by check_cycles()
		if((unsigned long long)dg->copy<=2)dg->copy = 0;
#endif

		if((unsigned long long)dg->copy == 3)	// cycle marker
		{
		extern int trace;
			if(trace > 1)print_copy_path("CYCLE ending at");
			return NULL;
		}
		if((unsigned long long)dg->copy == 5)	// sharable marker
		{
#ifdef	COPY_COUNTS
			copyreentcount++;
#endif
			goto share;
		}

		if(dg->copy && dg->copy->gen == generation)
		{
			*chret = 1;	// if 'copy' is set, a copy was made... so changed.
#ifdef	COPY_COUNTS
			copyreentcount++;
#endif
			return dg->copy;
		}
	}

	if(!dg->narcs && dg->type==dg->xtype && !FROZENLY_UNSHARABLE(dg) && !dg->ncarcs)
	{
#ifdef	COPY_COUNTS
		copysharecount++;
#endif
		goto share;
	}

	// leaf-types can be shared nomatter what
	//if(dg->xtype->ndescendents==0)goto share;

	// mark that we are inside this node, to detect cycles
	dg->copy = (struct dg*)3;//dg;

	get_slabstate(&state);

	int	na = dg->narcs+dg->ncarcs;
	if(!discard_inappropriate_types_during_copy || copypathp==0)	// copypathp==0 for the root level of the dag; don't want to discard down to 'sign'
	{
		for(i=0;i<dg->narcs;i++)
			if(SHOULD_TRIM(dg->label[i]))na--;
		for(i=0;i<dg->ncarcs;i++)
			if(SHOULD_TRIM(dg->carcs[i].label))na--;
	}
	else
	{
		// count intersection of dg->label and dg->xtype->dg->label
		assert(!dg->ncarcs);
		na = 0;
		if(dg->narcs)
		{
			short	*typelabels = dg->type->dg->label;
			int		ntypelabels = dg->type->dg->narcs;
			for(i=0;i<dg->narcs;i++)
			{
				if(SHOULD_TRIM(dg->label[i]))continue;
				while(ntypelabels > 0 && *typelabels < dg->label[i])
					{ typelabels++; ntypelabels--; }
				if(ntypelabels <= 0)break;	// nothing more to copy
				if(*typelabels != dg->label[i])continue;
				na++;
			}
		}
	}

	//int	ab = (na-2 + 3)/4 * 4;
	int		ab = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(na);
	newcopy = slab_alloc(sizeof(struct dg) + ab + sizeof(struct dg*)*na);
	//*newcopy = *dg;
	newcopy->xtype = newcopy->type = dg->type;
	newcopy->carcs = 0;
	newcopy->gen = generation;
	newcopy->copy = 0;
	newcopy->ncarcs = 0;
	newcopy->forwarded = 0;
	newcopy->narcs = na;
	aptr = DARCS(newcopy);
	alptr = newcopy->label;
	optr = DARCS(dg);
	olptr = dg->label;

	st = 0;
	if(!dg->ncarcs)
	{
		if(!discard_inappropriate_types_during_copy || copypathp==0)
		{
			for(i=0;i<dg->narcs;i++)
			{
				if(SHOULD_TRIM(*olptr))
				{
					optr++;
					olptr++;
					st=1;
					continue;
				}
				//fprintf(stderr, "copying primary `%s' arc from %s to %p\n",
				//		fnames[aptr->label], newcopy->xtype->name, optr->dest);
				ch = 0;

	#ifdef	COPY_PATHS
				assert(copypathp < MAX_COPY_PATH);
				copypath[copypathp++] = *olptr;
				if(*olptr == slash_fname)in_slash++;
	#endif
				*alptr = *olptr;
				*aptr = copy_dg_with_comp_arcs_ss(*optr, &ch);
	#ifdef	COPY_PATHS
				if(*olptr == slash_fname)in_slash--;
				copypathp--;
	#endif

				if(ch)st = 1;
				if(!*aptr)return 0;
				alptr++;
				aptr++;
				olptr++;
				optr++;
			}
		}
		else if(dg->narcs)
		{
			assert(!dg->ncarcs);
			// slightly fancier: merge-intersect with dg->type->dg->labels
			short	*typelabels = dg->type->dg->label;
			int		ntypelabels = dg->type->dg->narcs;
			int	ngot = 0;
			for(i=0;i<dg->narcs;i++)
			{
				if(SHOULD_TRIM(*olptr))
				{
					optr++;
					olptr++;
					st=1;
					continue;
				}
				while(ntypelabels > 0 && *typelabels < *olptr)
					{ typelabels++; ntypelabels--; }
				if(ntypelabels <= 0)break;	// nothing more to copy
				if(*typelabels != *olptr)
				{
					olptr++;
					optr++;
					continue;
				}
				ngot++;
				//fprintf(stderr, "copying primary `%s' arc from %s to %p\n",
				//		fnames[aptr->label], newcopy->xtype->name, optr->dest);
				ch = 0;

	#ifdef	COPY_PATHS
				assert(copypathp < MAX_COPY_PATH);
				copypath[copypathp++] = *olptr;
				if(*olptr == slash_fname)in_slash++;
	#endif
				*alptr = *olptr;
				*aptr = copy_dg_with_comp_arcs_ss(*optr, &ch);
	#ifdef	COPY_PATHS
				if(*olptr == slash_fname)in_slash--;
				copypathp--;
	#endif

				if(ch)st = 1;
				if(!*aptr)return 0;
				alptr++;
				aptr++;
				olptr++;
				optr++;
			}
			assert(ngot == na);
			if(na < dg->narcs)
			{
				//printf("when copying %s -> %s, discarded from %d to %d arcs\n", dg->xtype->name, newcopy->xtype->name, dg->narcs, newcopy->narcs);
				st = 1;
			}
		}
	}
	else for(j=0,i=0;i<dg->narcs || j<dg->ncarcs;) // mergesort
	{
		struct dg		*copyme;
		int				copylabel;
		if(j<dg->ncarcs && i<dg->narcs)
		{
			if(olptr[(int)i] < dg->carcs[(int)j].label)
			{
				copylabel = olptr[(int)i];
				copyme = optr[(int)i++];
			}
			else
			{
				copylabel = dg->carcs[(int)j].label;
				copyme = dg->carcs[(int)j++].dest;
			}
		}
		else if(i<dg->narcs)
		{
			copylabel = olptr[(int)i];
			copyme = optr[(int)i++];
		}
		else
		{
			copylabel = dg->carcs[(int)j].label;
			copyme = dg->carcs[(int)j++].dest;
		}
		if(SHOULD_TRIM(copylabel))
		{
			st=1;
			continue;
		}
		//fprintf(stderr, "copying primary `%s' arc from %s to %p\n",
		//		fnames[aptr->label], newcopy->xtype->name, xarc.dest);
		ch = 0;

#ifdef	COPY_PATHS
		assert(copypathp < MAX_COPY_PATH);
		copypath[copypathp++] = copylabel;
		if(copylabel == slash_fname)in_slash++;
#endif
		*alptr = copylabel;
		*aptr = copy_dg_with_comp_arcs_ss(copyme, &ch);
#ifdef	COPY_PATHS
		if(copylabel == slash_fname)in_slash--;
		copypathp--;
#endif

		if(ch)st = 1;
		if(!*aptr)return 0;
		aptr++; alptr++;
	}
	dg->copy = newcopy;

//#define	DAG_SIGNATURES
#ifdef	DAG_SIGNATURES
	printf("TYPE %s", newcopy->xtype->name);
	for(i=0;i<newcopy->narcs;i++)
		printf(" %s", fnames[DARCS(newcopy)[i].label]);
	printf("\n");
#endif

	if(dg->ncarcs || dg->type!=dg->xtype || st || FROZENLY_UNSHARABLE(dg))
	{
		*chret = 1;
#ifdef	COPY_COUNTS
		copycount++;
#ifdef	COPY_PATHS
		//print_copy_path("COPY");
#endif
#endif
		return newcopy;
	}
	else
	{
#ifdef	COPY_COUNTS
		copysharecount++;
#endif
		// slab-free the node we just built, it's guaranteed to be on top
		set_slabstate(&state);
		share:
		// mark this node as sharable in case someone reenters into it
		dg->copy = (struct dg*)5;
		if(forwarded)*chret = 1;	// since node was forwarded, parent must consider it changed, even though we're sharing it
		else *chret = 0;
#ifdef	COPY_PATHS
		//print_copy_path("SHARE");
#endif
		return dg;
	}
}

int	cdwca_should_trim = 0;
struct dg	*copy_dg_with_comp_arcs(struct dg	*dg)
{
	struct dg	*newcopy;
	unsigned short	*alptr, *olptr;
	struct dg	**aptr, **optr;
	int		i, j;

	dg = dereference_dg(dg);
	if(!dg)return 0;

#ifdef	HAVE_CHECK_CYCLES
	// ignore mark left by check_cycles()
	if((unsigned long)dg->copy<=2)dg->copy = 0;
#endif

	if(dg->gen != generation)
	{
		dg->copy = 0;
		dg->forwarded = 0;
		dg->ncarcs = 0;
		dg->carcs = 0;
		dg->type = dg->xtype;
		dg->gen = generation;
	}
	else if(dg->copy)
	{
		if((unsigned long long)dg->copy == 3)
		{
			// cycle detected!
			//fprintf(stderr, "NOTE: cycle\n");
			return NULL;
		}
		if(dg->copy->gen == generation)
			return dg->copy;
		assert(!"not reached -- why would copy be set and not be up-to-generation?");
	}

#define	CDWCA_RESTRICTOR(x)	(PACKING_RESTRICTOR(x) || (cdwca_should_trim && SHOULD_TRIM(x)))
	int	na = dg->narcs + dg->ncarcs;
	for(i=0;i<dg->narcs;i++)
		if(CDWCA_RESTRICTOR(dg->label[i]))na--;
	for(i=0;i<dg->ncarcs;i++)
		if(CDWCA_RESTRICTOR(dg->carcs[i].label))na--;

	//int	ab = (na-2 + 3)/4 * 4;
	int		ab = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(na);
	newcopy = slab_alloc(sizeof(struct dg) + ab + sizeof(struct dg*)*na);
	*newcopy = *dg;
	newcopy->xtype = newcopy->type = (dg->gen==generation)?dg->type:dg->xtype;
	newcopy->gen = generation;
	newcopy->copy = NULL;
	newcopy->ncarcs = 0;
	newcopy->carcs = NULL;
	newcopy->narcs = na;
	newcopy->forwarded = 0;
	alptr = newcopy->label;
	aptr = DARCS(newcopy);
	olptr = dg->label;
	optr = DARCS(dg);

	// mark that we are inside this node, to detect cycles
	dg->copy = (void*)3;

	for(j=0,i=0;i<dg->narcs || j<dg->ncarcs;) // mergesort
	{
		struct dg		*copyme;
		int				copylabel;
		if(j<dg->ncarcs && i<dg->narcs)
		{
			if(olptr[(int)i] < dg->carcs[(int)j].label)
			{
				copylabel = olptr[(int)i];
				copyme = optr[(int)i++];
			}
			else
			{
				copylabel = dg->carcs[(int)j].label;
				copyme = dg->carcs[(int)j++].dest;
			}
		}
		else if(i<dg->narcs)
		{
			copylabel = olptr[(int)i];
			copyme = optr[(int)i++];
		}
		else
		{
			copylabel = dg->carcs[(int)j].label;
			copyme = dg->carcs[(int)j++].dest;
		}
		if(CDWCA_RESTRICTOR(copylabel))
			continue;
		//fprintf(stderr, "copying primary `%s' arc from %s to %p\n",
		//		fnames[aptr->label], newcopy->xtype->name, xarc.dest);

#ifdef	COPY_PATHS
		assert(copypathp < MAX_COPY_PATH);
		copypath[copypathp++] = copylabel;
		if(copylabel == slash_fname)in_slash++;
#endif
		*alptr = copylabel;
		*aptr = copy_dg_with_comp_arcs(copyme);
#ifdef	COPY_PATHS
		if(copylabel == slash_fname)in_slash--;
		copypathp--;
#endif

		if(!*aptr)return NULL;
		aptr++; alptr++;
	}

	dg->copy = newcopy;
	return newcopy;
}

struct dg	*copy_dg(struct dg	*d)
{
	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}
	top_copies++;
	return copy_dg_with_comp_arcs(d);
}

// permanent version of unify1 - destroys dg2
int	unify_dg_infrom(struct dg	*dg1, struct dg	*dg2)
{
	int	i, j, k;
	unsigned char	news[256];
	int	nn=0;
	struct type	*t, *t1, *t2;
	struct dg	*extra=0;
	struct dg	**arcs1, **arcs2;

	dg1 = dereference_dg(dg1);
	dg2 = dereference_dg(dg2);
	if(!dg1 || !dg2)return -1;

	t1 = (dg1->gen==generation)?dg1->type:dg1->xtype;
	t2 = (dg2->gen==generation)?dg2->type:dg2->xtype;

	if(dg1->copy)dg1->copy = 0;
	if(dg2->copy)dg2->copy = 0;
	if(dg1 == dg2)return 0;

	// destructively unify

	t = glb(t1, t2);
	if(!t)
	{
#ifdef	UNIFY_PATHS
		ut1 = t1;
		ut2 = t2;
#endif
		return -1;
	}

	if(t != t1 && t!= t2)
	{
		if(!t->dg && t->name[0]!='"' && !(t->name[0]=='g' && t->name[1]=='('))
		{
			extern struct type	*_current_building_type;
			if(t != _current_building_type)
			{
				//printf(" .. possible extra glb constraints from type '%s' which hasn't been constrained yet. [ while unifying %s and %s ]\n", t->name, t1->name, t2->name);
				if(_current_building_type)
				{
					//printf(" ... _current_building_type = %s\n", _current_building_type->name);
					//printf(" ... going to try to go constrain that type while in the middle of unifying for this one...!\n");
					find_type(t->name, 1);
				}
				else
				{
					fprintf(stderr, "internal error: reached a non-string type with NULL dag\n");
					fprintf(stderr, "glb of %s and %s\n", t1->name, t2->name);
					fprintf(stderr, "type name: %s\n", t->name);
					int k;
					for(k=0;k<t->nparents;k++)
						fprintf(stderr, " parent %d = %s\n", k, t->parents[k]->name);
					exit(-1);
				}
			}
		}
		if(t->dg && t->dg->narcs)
		{
			dagreset_c(t->dg);
			extra = copy_dg_with_comp_arcs(t->dg);
			//printf(" .. extra glb constraint from type '%s'\n", t->name);
			//flat_print_dg(extra);
			//printf("\n");
			dagreset_c(t->dg);
		}
	}
	if(dg1->gen != generation)
	{
		dg1->ncarcs = 0;
		dg1->carcs = 0;
	}
	dg1->forwarded = 0;
	dg1->xtype = dg1->type = t;
	dg1->gen = generation;
	//fprintf(stderr, "type `%s' at ", t->name); unify_backtrace();

	p_forward_dg(dg2, dg1);

	// unify dg2's arcs into dg1's arcs
	// this version of the unifier ignores carcs... for simplicity
	arcs1 = DARCS(dg1);
	arcs2 = DARCS(dg2);
	for(j=0,i=0;i<dg2->narcs;i++)
	{
		for(;j<dg1->narcs && dg2->label[i]>dg1->label[j];j++){}
		if(j==dg1->narcs || dg2->label[i] != dg1->label[j])news[nn++] = i;
		else
		{
#ifdef	UNIFY_PATHS
			upath[upathl++] = dg2->label[i];
#endif
			if(unify_dg_infrom(arcs1[j], arcs2[i]))return -1;
#ifdef	UNIFY_PATHS
			upathl--;
#endif
		}
	}

	// add remaining dg2 arcs to dg1
	if(nn > 0)
	{
		/* XXX quick and dirty replacement for the efficient code below
		dg1->arcs = slab_realloc(dg1->arcs, sizeof(struct darc) * dg1->narcs,
					sizeof(struct darc) * (dg1->narcs + nn));

		for(j=dg1->narcs,k=nn-1;k>=0;k--)
		{
			i = news[k];
			while(j>0 && dg2->arcs[i].label<dg1->arcs[j-1].label)
			{
				dg1->arcs[j+k] = dg1->arcs[j-1];
				j--;
			}
			// add dg2->arcs[i] to dg1->arcs
			dg1->arcs[j+k] = dg2->arcs[i];
		}
		dg1->narcs+=nn;
		*/
		for(k=0;k<nn;k++)
			dg1 = add_dg_hop(dg1, dg2->label[news[k]], arcs2[news[k]]);
		arcs1 = DARCS(dg1);
		//qsort(dg1->arcs, dg1->narcs, sizeof(struct darc), darc_cmp);
	}

	if(extra && unify_dg_infrom(dg1, extra))
	{
		if(!g_loaded)
		{
			fprintf(stderr, "UNIFY: failed additional constraints from glb-type `%s'\n", extra->xtype->name);
			print_dg(extra); printf("\n");
		}
		return -1;
	}

	return 0;
}

// walk the dags together, pushing types to the GLB whenever the GLB exists, returning with no error when it doesn't.
// for now when the GLB doesn't exist, don't recurse.
// we may(?) want to keep going and keep dg1 as the preferred type, only recursing/copying on arcs that are appropriate to dg1's type.
// basically a copy of unify_dg_infrom that doesn't return on inner errors.
int		unify_dg_defaults(struct dg	*dg1, struct dg	*dg2)
{
	int	i, j, k;
	unsigned char	news[256];
	int	nn=0;
	struct type	*t, *t1, *t2;
	struct dg	*extra=0;
	struct dg	**arcs1, **arcs2;

	dg1 = dereference_dg(dg1);
	dg2 = dereference_dg(dg2);
	if(!dg1 || !dg2)return -1;

	t1 = (dg1->gen==generation)?dg1->type:dg1->xtype;
	t2 = (dg2->gen==generation)?dg2->type:dg2->xtype;

	if(dg1->copy)dg1->copy = 0;
	if(dg2->copy)dg2->copy = 0;
	if(dg1 == dg2)return 0;

	// hack to avoid doing any default unifications between two MRS variables whose INSTLOCs are incompatible
	extern int instloc_feature;
	struct dg	*il1 = dg_hop(dg1, instloc_feature);
	struct dg	*il2 = dg_hop(dg2, instloc_feature);
	if(il1 && il2)
	{
		struct type	*il1t = (il1->gen==generation)?il1->type:il1->xtype;
		struct type	*il2t = (il2->gen==generation)?il2->type:il2->xtype;
		if(!glb(il1t,il2t))return -1;
	}

	// destructively unify

	t = glb(t1, t2);
	if(!t)return -1;

	if(t != t1 && t!= t2)
	{
		if(!t->dg && t->name[0]!='"')
			assert(!"not reached");
		if(t->dg && t->dg->narcs)
		{
			dagreset_c(t->dg);
			extra = copy_dg_with_comp_arcs(t->dg);
			dagreset_c(t->dg);
		}
	}
	if(dg1->gen != generation)
	{
		dg1->ncarcs = 0;
		dg1->carcs = 0;
	}
	dg1->forwarded = 0;
	dg1->xtype = dg1->type = t;
	dg1->gen = generation;
	//printf("type `%s' at ", t->name); unify_backtrace();

	p_forward_dg(dg2, dg1);

	int result_code = 0;
	// unify dg2's arcs into dg1's arcs
	// this version of the unifier ignores carcs... for simplicity
	arcs1 = DARCS(dg1);
	arcs2 = DARCS(dg2);
	for(j=0,i=0;i<dg2->narcs;i++)
	{
		for(;j<dg1->narcs && dg2->label[i]>dg1->label[j];j++){}
		if(j==dg1->narcs || dg2->label[i] != dg1->label[j])news[nn++] = i;
		else
		{
#ifdef	UNIFY_PATHS
			upath[upathl++] = dg2->label[i];
#endif
			if(unify_dg_defaults(arcs1[j], arcs2[i]))result_code = -1;
#ifdef	UNIFY_PATHS
			upathl--;
#endif
		}
	}

	// add remaining dg2 arcs to dg1
	if(nn > 0)
	{
		//printf("adding %d new arcs to %s\n", nn, dg1->xtype->name);
		for(k=0;k<nn;k++)
			dg1 = add_dg_hop(dg1, dg2->label[news[k]], arcs2[news[k]]);
		arcs1 = DARCS(dg1);
		//qsort(dg1->arcs, dg1->narcs, sizeof(struct darc), darc_cmp);
	}

	if(extra && unify_dg_infrom(dg1, extra))
		result_code = -1;

	return result_code;
}

static struct dg	*extra_ocons, *extra_substcons, *extra_anti_synsem;
static struct type	*ocons, *substcons, *anti_synsem;

#define		CSDEPTH	10240
struct darc	*carcstack;
int		carcsp, carcsgen;

struct darc	*alloc_carcs(int	n)
{
	struct darc	*ret;

	if(carcsgen != generation) { carcsgen = generation; carcsp = 0; }
	assert(carcsp +n <= CSDEPTH);
	ret = carcstack + carcsp;
	carcsp+=n;
	return ret;
}

struct darc	*realloc_carcs(struct darc	*ptr, int	old, int	new)
{
	struct darc	*nptr;

	if(carcsgen != generation) { carcsgen = generation; carcsp = 0; assert(!old); }
	if(ptr+old == carcstack+carcsp)
	{
		carcsp += new-old;
		return ptr;
	}
	else
	{
		nptr = alloc_carcs(new);
		memcpy(nptr, ptr, old*sizeof(struct darc));
		return nptr;
	}
}

void	setup_carcs_stack()
{
	carcstack = malloc(sizeof(struct darc)*CSDEPTH);
}

int extra_erg_dag_stash = 0;

void	setup_extra_type_dgs()
{
	if(extra_erg_dag_stash)
	{
		ocons = lookup_type("*ocons*");
		extra_ocons = copy_dg(ocons->dg);
		substcons = lookup_type("*substcons*");
		extra_substcons = copy_dg(substcons->dg);
		anti_synsem = lookup_type("anti_synsem");
		extra_anti_synsem = copy_dg(anti_synsem->dg);
		xarg_fname = lookup_fname("XARG");
		sind_fname = lookup_fname("--SIND");
		mod_fname = lookup_fname("MOD");
		slash_fname = lookup_fname("SLASH");
	}
	commit_slab();
}

struct dg	*get_extra_type_dg(struct type	*t)
{
	struct dg	*extra = 0;

	if(extra_erg_dag_stash)
	{
		if(t==ocons)
			if(extra_ocons->gen != generation)
				extra = extra_ocons;
		if(t==substcons)
			if(extra_substcons->gen != generation)
				extra = extra_substcons;
		if(t==anti_synsem)
			if(extra_anti_synsem->gen != generation)
				extra = extra_anti_synsem;
	}

	if(extra)
	{
		extra->forwarded = 0;
		extra->type = extra->xtype;
		extra->ncarcs = 0;
		extra->carcs = 0;
		extra->copy = 0;
		extra->gen = generation;
	}
	else
	{
		dagreset_c(t->dg);
		//fprintf(stderr, "NOTE: extra copy of `%s'\n", t->name);
		extra = copy_dg_no_comp_arcs(t->dg);
		dagreset_c(t->dg);
	}
	return extra;
}

int	unify_always_succeeds = 0;
void	enable_robust_unification()
{ unify_always_succeeds = 1; }
void	disable_robust_unification()
{ unify_always_succeeds = 0; }

is_null(struct type	*t)
{
	static struct type	*null = NULL;
	if(!null)null = lookup_type(g_null_type);
	if(descendent_of(t->tnum, null))return 1;
	return 0;
}

is_cons(struct type	*t)
{
	static struct type	*cons = NULL;
	if(!cons)cons = lookup_type(g_cons_type);
	if(descendent_of(t->tnum, cons))return 1;
	return 0;
}

void check_robust_list_unification(struct dg	*nulldg, struct dg	*consdg)
{
	struct	dg	*doublehop = consdg;
	while(1)
	{
		consdg = dg_hop(consdg, lookup_fname("REST"));
		if(doublehop)doublehop = dg_hop(doublehop, lookup_fname("REST"));
		if(doublehop)doublehop = dg_hop(doublehop, lookup_fname("REST"));
		if(doublehop == consdg)
		{
			fprintf(stderr, "NOTE: avoided falling into a circular list...\n");
			return;
		}
		if(!consdg)return;
		consdg = dereference_dg(consdg);
		struct type	*rt = (consdg->gen==generation)?consdg->type:consdg->xtype;
		if(!is_cons(rt))
		{
			struct type	*nrt = glb(rt, lookup_type(g_null_type));
			if(nrt)
			{
				if(consdg->gen != generation)
				{
					consdg->gen = generation;
					consdg->forwarded = 0;
					consdg->ncarcs = 0;
					consdg->carcs = NULL;
					consdg->copy = NULL;
				}
				//fprintf(stderr, "NOTE: updating REST of a hallucinated list from %s to %s\n", rt->name, nrt->name);
				consdg->type = nrt;
			}
			break;
		}
	}
}

int	allow_unify_swapping = 1;

int	unify1(struct dg	*dg1, struct dg	*dg2)
{
	int	i, j, k;
	struct type	*t, *t1, *t2;
	struct dg	*extra=0;
	struct dg	**arcs1, **arcs2;

	if(dg1 == dg2)return 0;
	dg1 = dereference_dg(dg1);
	dg2 = dereference_dg(dg2);
	if(!dg1 || !dg2)return -1;

	if(dg1 == dg2)return 0;
	if(dg1->copy)dg1->copy = 0;
	if(dg2->copy)dg2->copy = 0;

	t1 = (dg1->gen==generation)?dg1->type:dg1->xtype;
	t2 = (dg2->gen==generation)?dg2->type:dg2->xtype;
//	if(!t1) { printf("unify found a NULL type on dg1. gen = %d, generation = %d, xtype = %p, type = %p\n", dg1->gen, generation, dg1->xtype, dg1->type); unify_backtrace(); }
//	if(!t2) { printf("unify found a NULL type on dg2. gen = %d, generation = %d, xtype = %p, type = %p\n", dg2->gen, generation, dg2->xtype, dg2->type); unify_backtrace(); }

	if(t1 == t2)t = t1;
	else
	{
		t = glb(t1, t2);
		if(!t)
		{
			//printf("no glb for %s and %s\n", t1->name, t2->name);
			if(unify_always_succeeds)
			{
				if(is_null(t1) && is_cons(t2))
					check_robust_list_unification(dg1, dg2);
				else if(is_null(t2) && is_cons(t1))
					check_robust_list_unification(dg2, dg1);
				t = t2;
			}
			else
			{
#ifdef	UNIFY_PATHS
				ut1 = t1;
				ut2 = t2;
#endif
				return -1;
			}
		}
	}

	// apply GLB constraint if necessary
	if(t != t1 && t!= t2 && t->dg && t->dg->narcs)
		/*&& !(0
		|| (t->name[0]=='g' && t->name[1]=='(')
		))*/
	{
//		if(t->name[0]=='g' && t->name[1]=='(')
//			printf("reached glbtype '%s' and will waste time unifying...\n", t->name);
		if(t->dg->gen != generation)
		{
			extra = t->dg;
			extra->forwarded = 0;
			extra->type = extra->xtype;
			extra->ncarcs = 0;
			extra->carcs = 0;
			extra->copy = 0;
			extra->gen = generation;
		}
		else
		{
			// it's REALLY obnoxious that we have to do this
			extra = get_extra_type_dg(t);
		}
#ifdef	UNIFY_PATHS
		uglb = extra->xtype;
		//printf("applying glb constraint `%s'\n", uglb->name);
		upathgl = upathl;
#endif
		if(unify1(dg1, extra))
		{
			if(!g_loaded)
			{
				fprintf(stderr, "UNIFY: failed additional constraints from glb-type `%s'\n", t->name);
				print_dg(extra); printf("\n");
			}
			return -1;
		}
#ifdef	UNIFY_PATHS
		uglb = 0;
#endif
		dg1 = dereference_dg(dg1);
		// don't bother getting new value of t1, since nobody will look at it
	}

	__builtin_prefetch(dg1->label);
	__builtin_prefetch(dg2->label);

	if(!FROZEN(dg2) && allow_unify_swapping)
	{
		if(FROZEN(dg1))goto swap;
		//register int balance = 0;
		//if(dg2->gen==generation && (dg2->ncarcs || dg2->type!=dg2->xtype))balance += 25;
		//if(dg1->gen==generation && (dg1->ncarcs || dg1->type!=dg1->xtype))balance -= 25;
		//balance += 7*dg2->narcs;
		//balance -= 5*dg1->narcs;
		//if(balance>0)
		if(dg2->narcs > dg1->narcs)
		{
			swap:
			// strategy: swap to make dg1 non-frozen if possible
			// rationale: we can never substructure-share a frozen dag (why not?).
			// if we forward to a frozen dag, we are guaranteed to have to copy it.
			// so, if we have the choice, forward to the non-frozen dag.
			// if frozenness is not a choice, try to forward to the dag with more arcs, to avoid using ->carcs and increase chances of already having the right type (-> more sharing)
			extra = dg1;
			dg1 = dg2;
			dg2 = extra;
			extra = 0;
		}
	}

/*
	if(allow_unify_swapping && dg2->narcs > dg1->narcs)
	{
		extra = dg1;
		dg1 = dg2;
		dg2 = extra;
		extra = 0;
	}
*/

	if(dg1->gen != generation)
	{
		dg1->ncarcs = 0;
		dg1->carcs = 0;
		dg1->gen = generation;
	}
	dg1->forwarded = 0;
	dg1->type = t;
	//fprintf(stderr, "type `%s' at ", t->name); unify_backtrace();

	forward_dg(dg2, dg1);

	// quasi-destructively unify the four sets of arcs together!

	unsigned char	news[dg2->narcs], newcs[dg2->ncarcs];
	int	nn=0, nc=0;

	arcs1 = DARCS(dg1);
	arcs2 = DARCS(dg2);
	// unify dg2's arcs into dg1's arcs
	for(j=0,k=0,i=0;i<dg2->narcs;i++)
	{
		if(k>=dg1->narcs && j>=dg1->ncarcs)break;
#ifdef	UNIFY_PATHS
		upath[upathl++] = dg2->label[i];
#endif
		for(;k<dg1->narcs && dg2->label[i] > dg1->label[k];k++) {}
		if(k<dg1->narcs && dg2->label[i] == dg1->label[k])
		{
			if(unify1(arcs1[k++], arcs2[i]))return -1;
		}
		else
		{
			for(;j<dg1->ncarcs && dg2->label[i] > dg1->carcs[j].label;j++) {}
			if(j<dg1->ncarcs && dg2->label[i] == dg1->carcs[j].label)
			{
				if(unify1(dg1->carcs[j++].dest, arcs2[i]))return -1;
			}
			else news[nn++] = i;
		}
#ifdef	UNIFY_PATHS
		upathl--;
#endif
	}
	for(;i<dg2->narcs;i++)news[nn++] = i;

	// unify dg2's comps arcs into dg1's arcs
	for(j=0,k=0,i=0;i<dg2->ncarcs;i++)
	{
		if(k>=dg1->narcs && j>=dg1->ncarcs)break;
#ifdef	UNIFY_PATHS
		upath[upathl++] = dg2->carcs[i].label;
#endif
		for(;k<dg1->narcs && dg2->carcs[i].label > dg1->label[k];k++) {}
		if(k<dg1->narcs && dg2->carcs[i].label == dg1->label[k])
		{
			if(unify1(arcs1[k++], dg2->carcs[i].dest))return -1;
		}
		else
		{
			for(;j<dg1->ncarcs && dg2->carcs[i].label > dg1->carcs[j].label;j++) {}
			if(j<dg1->ncarcs && dg2->carcs[i].label == dg1->carcs[j].label)
			{
				if(unify1(dg1->carcs[j++].dest, dg2->carcs[i].dest))return -1;
			}
			else newcs[nc++] = i;
		}
#ifdef	UNIFY_PATHS
		upathl--;
#endif
	}
	for(;i<dg2->ncarcs;i++)newcs[nc++] = i;

	// add remaining dg2 arcs and comps arcs to dg1's comps arcs
	if(nn+nc > 0)
	{
		/*printf("dg1 type %s ; dg2 type %s\n", dg1->xtype->name, dg2->xtype->name);
		for(j=0;j<dg1->narcs;j++)printf("dg1 %s\n", fnames[dg1->label[j]]);
		for(j=0;j<dg2->narcs;j++)printf("dg2 %s\n", fnames[dg2->label[j]]);
		printf("dg1 had %d carcs; adding %d + %d\n", dg1->ncarcs, nn, nc);*/
		dg1->carcs = realloc_carcs(dg1->carcs, dg1->ncarcs, dg1->ncarcs + nn + nc);

		// merge-sort
		j=k=0;
		/*if(nn&&nc)while(1)
		{
			if(arcs2[news[j]].label < dg2->carcs[newcs[k]].label)
			{
				dg1->carcs[dg1->ncarcs++] = arcs2[news[j++]];
				if(j==nn)break;
			}
			else
			{
				dg1->carcs[dg1->ncarcs++] = dg2->carcs[newcs[k++]];
				if(k==nc)break;
			}
		}*/
		while(j<nn)
		{
			//printf("from dg2 arc %s\n", fnames[dg2->label[news[j]]]);
			dg1->carcs[dg1->ncarcs].label = dg2->label[news[j]];
			dg1->carcs[dg1->ncarcs++].dest = arcs2[news[j++]];
		}
		while(k<nc)
		{
			//printf("from dg2 carc %s\n", fnames[dg2->carcs[newcs[k]].label]);
			dg1->carcs[dg1->ncarcs++] = dg2->carcs[newcs[k++]];
		}
		if(nn+nc < dg1->ncarcs || (nc&&nn))
		{
			//fprintf(stderr, "NOTE: had to sort %d carcs\n", dg1->ncarcs);
			qsort(dg1->carcs, dg1->ncarcs, sizeof(struct darc), darc_cmp);
		}
	}

	return 0;
}

static struct slab_state	tmpstate;

void	setup_tmp()
{
	get_slabstate(&tmpstate);
}

struct dg	*daughter_position(struct dg	*mother, int	arg)
{
	struct dg	*to;
	if(arg>=0)
	{
		int i =0 ;
		to = dg_hop(mother, 0);	// 0 is guaranteed to be ARGS
		while(to && i<arg)
		{
			to = dg_hop(to, 2);	// REST
			i++;
		}
		if(to)to = dg_hop(to, 1);	// FIRST
		if(!to)
		{
			fprintf(stderr, "unify_dg: couldn't get arg %d position in %s\n", arg, mother->xtype->name);
			exit(-1);
		}
	}
	else to = mother;
	return to;
}

#ifdef	TIM_IN
long long base_unify_dg_tmp_succ_count, base_unify_dg_tmp_fail_count, base_finalize_tmp_count;
double	base_unify_dg_tmp_succ_time, base_unify_dg_tmp_fail_time, base_finalize_tmp_time;
#endif

int	unify_dg_tmp(struct dg	*dg1, struct dg	*dg2, int	arg)
{
	struct dg	*to;
	int		i = 0;

	top_unifies++;
	get_slabstate(&tmpstate);

#ifdef	TIM_IN
struct timeval	tv1, tv2;
gettimeofday(&tv1,NULL);
#endif

	if(arg>=0)
	{
		to = dg_hop(dg2, 0);	// 0 is guaranteed to be ARGS
		while(to && i<arg)
		{
			to = dg_hop(to, 2);	// REST
			i++;
		}
		if(to)to = dg_hop(to, 1);	// FIRST
		if(!to)
		{
			fprintf(stderr, "unify_dg: couldn't get arg %d position in %s\n", arg, dg2->xtype->name);
			exit(-1);
		}
	}
	else to = dg2;

#ifdef	UNIFY_PATHS
	upathl = 0;
	uglb = 0;
#endif

	int	res = unify1(to, dg1);
#ifdef	TIM_IN
gettimeofday(&tv2,NULL);
if(res)
{
	base_unify_dg_tmp_fail_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
	base_unify_dg_tmp_fail_count += 1;
}
else
{
	base_unify_dg_tmp_succ_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
	base_unify_dg_tmp_succ_count += 1;
}
#endif
	return res;
}

struct dg	*trim_copy(struct dg	*d)
{
	char	ch = 0;
	enable_trim(1);
	return copy_dg_with_comp_arcs_ss(d, &ch);
}

void bump_generation()
{
	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}
}

int	trimmed_portion_is_cyclic(struct dg	*d)
{
#ifdef	HAVE_CHECK_CYCLES
	int	i;
	d = dereference_dg(d);
	struct dg	**arcs = DARCS(d);
	for(i=0;i<d->narcs;i++)
		if(SHOULD_TRIM(d->label[i]))
			if(check_cycles(arcs[i]))return 1;
	for(i=0;i<d->ncarcs;i++)
		if(SHOULD_TRIM(d->carcs[i].label))
			if(check_cycles(d->carcs[i].dest))return 1;
#endif
	return 0;
}

struct dg	*finalize_tmp(struct dg	*d, int trim)
{
	char		ch = 0;
	struct dg	*res;

#ifdef	TIM_IN
struct timeval	tv1, tv2;
gettimeofday(&tv1, NULL);
#endif

	enable_trim(trim);
	/*if(trim && trimmed_portion_is_cyclic(d))
		res = NULL;
	else res = copy_dg_with_comp_arcs_ss(d, &ch);*/
	if(unify_always_succeeds)
		res = copy_dg_with_comp_arcs_loopy(d);
	else
	{
		res = copy_dg_with_comp_arcs_ss(d, &ch);
		if(res && trim && trimmed_portion_is_cyclic(d))
			res = NULL;
	}

	if(!res)set_slabstate(&tmpstate);
	bump_generation();

#ifdef	TIM_IN
gettimeofday(&tv2, NULL);
base_finalize_tmp_time += tv2.tv_sec - tv1.tv_sec + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
base_finalize_tmp_count += 1;
#endif

	top_copies++;
	return res;
}

#ifdef TIM_IN
__attribute__((destructor)) report_TIM_IN()
{
	fprintf(stderr, "unify_dg_tmp() successes: %.3fs in %lld calls = %gs\n",
		base_unify_dg_tmp_succ_time, base_unify_dg_tmp_succ_count,
		base_unify_dg_tmp_succ_time / base_unify_dg_tmp_succ_count);
	fprintf(stderr, "unify_dg_tmp() failures:  %.3fs in %lld calls = %gs\n",
		base_unify_dg_tmp_fail_time, base_unify_dg_tmp_fail_count,
		base_unify_dg_tmp_fail_time / base_unify_dg_tmp_fail_count);
	fprintf(stderr, "finalize_tmp():  %.3fs in %lld calls = %gs\n",
		base_finalize_tmp_time, base_finalize_tmp_count,
		base_finalize_tmp_time / base_finalize_tmp_count);
}
#endif

struct dg	*finalize_tmp_noss(struct dg	*d, int trim)
{
	struct dg	*res;

	enable_trim(trim);
	cdwca_should_trim = 1;
	if(trim && trimmed_portion_is_cyclic(d))
		res = NULL;
	else res = copy_dg_with_comp_arcs(d);
	cdwca_should_trim = 0;
	if(!res)set_slabstate(&tmpstate);
	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}

	top_copies++;
	return res;
}

void	forget_tmp()
{
	set_slabstate(&tmpstate);
	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}
}

// main entry point
struct dg	*unify_dg(struct dg	*dg1, struct dg	*dg2, int	arg)
{
	if(!unify_dg_tmp(dg1, dg2, arg))
		return finalize_tmp(dg2, 0);
	else
	{
		forget_tmp();
		return 0;
	}
}

struct dg	*unify_dg_noss(struct dg	*dg1, struct dg	*dg2, int	arg)
{
	if(!unify_dg_tmp(dg1, dg2, arg))
		return finalize_tmp_noss(dg2, 0);
	else
	{
		forget_tmp();
		return 0;
	}
}

static long	marker;

void dagreset_c(struct dg	*d)
{
	int	i;
	struct dg	**arcs;

	d = p_dereference_dg(d);
	if(!d)return;

	d->copy = 0;
	arcs = DARCS(d);
	for(i=0;i<d->narcs;i++)
		dagreset_c(arcs[i]);
}

void dagreset_c_including_carcs(struct dg	*d)
{
	int	i;
	struct dg	**arcs;

	d = dereference_dg(d);
	if(!d)return;

	d->copy = 0;
	arcs = DARCS(d);
	for(i=0;i<d->narcs;i++)
		dagreset_c_including_carcs(arcs[i]);
	for(i=0;i<d->ncarcs;i++)
		dagreset_c_including_carcs(d->carcs[i].dest);
}

// as of December 2020, the following function gets to assume the generation has been bumped immediately prior to the top-level call.
void dgreset_r(struct dg	*d)
{
	int	i;
	struct dg	**arcs;

	d = p_dereference_dg(d);
	if(!d)return;
	if(d->gen == generation)return;	// because of the new precondition, up-to-date generation means this substructure is already reset.

	d->ncarcs = 0;
	d->carcs = 0;
	d->copy = 0;
	d->forwarded = 0;
	d->type = d->xtype;
	d->gen = generation;

	arcs = DARCS(d);
	for(i=0;i<d->narcs;i++)
		dgreset_r(arcs[i]);
}

static void dgmark(struct dg	*d)
{
	int	i;
	struct dg	**arcs;

	d = p_dereference_dg(d);
	d->ncarcs++;
	if(d->ncarcs>1)return;

	arcs = DARCS(d);
	for(i=0;i<d->narcs;i++)
		dgmark(arcs[i]);
}

extern char	**fnames;

static void flat_print_dg(struct dg	*d)
{
	int	i;
	struct dg	**arcs;

	d = dereference_dg(d);

	printf("(%p) ", d);
	if(!d->narcs && (d->gen!=generation || !d->ncarcs))
		printf("%s", (d->gen==generation?d->type:d->xtype)->name);
	else
	{
		printf("#D[%s", (d->gen==generation?d->type:d->xtype)->name);
		arcs = DARCS(d);
		for(i=0;i<d->narcs;i++)
		{
			printf(" %s: ", fnames[d->label[i]]);
			flat_print_dg(arcs[i]);
		}
		if(d->gen==generation && d->ncarcs)for(i=0;i<d->ncarcs;i++)
		{
			printf(" /%s: ", fnames[d->carcs[i].label]);
			flat_print_dg(d->carcs[i].dest);
		}
		printf("]");
	}
}

print_within_generation(struct dg	*d) { flat_print_dg(d); }

int	dag_print_style = 0;
int	quoted_number_types = 0;

static int	snrprint_dg(char	*str, int	maxlen, struct dg	*d)
{
	int	i, len = 0, tmp;
	struct dg	**arcs;

	d = p_dereference_dg(d);

	if(dag_print_style == 0)
	{
		if(d->copy)
			return snprintf(str, maxlen, "<%lld>", (long long)d->copy);

		// multi-visited, give it a tag.
		if(d->ncarcs>1)
		{
			d->copy = (struct dg*)(marker++);
			tmp = snprintf(str, maxlen, "<%lld>= ", (long long)d->copy);
			if(str)str += tmp; maxlen -= tmp; len += tmp;
			if(maxlen<0)maxlen=0;
		}
	}

	char	*tname_prefix="", *tname_suffix="";
	char	*tname = (d->gen==generation?d->type:d->xtype)->name;
	char	cl;
	if(tname[0]=='"' && (cl = tname[strlen(tname)-1])!='"')
	{
		if(cl!='$')
		{
			// funny types 'foo get internally stored as "foo
			tname_prefix="'";
			tname++;
		}
		else
		{
			// regex types ^foo$ get internally stored as "foo$
			tname_prefix = "^";
			tname++;
		}
	}
	else
	{
		if(quoted_number_types)
		{
			char	*p = tname;
			while(*p && isdigit(*p))p++;
			if(!*p)
			{
				tname_prefix = "\"";
				tname_suffix = "\"";
			}
		}
	}


	if(!d->narcs)
	{
		if(dag_print_style==0) tmp = snprintf(str, maxlen, "#D[%s%s%s]", tname_prefix, tname, tname_suffix);
		else tmp = snprintf(str, maxlen, "%s%s%s", tname_prefix, tname, tname_suffix);
		if(str)str += tmp; maxlen -= tmp; len += tmp;
		if(maxlen<0)maxlen=0;
	}
	else
	{
		if(dag_print_style==0)
			tmp = snprintf(str, maxlen, "#D[%s%s%s", tname_prefix, tname, tname_suffix);
		else tmp = snprintf(str, maxlen, "%s%s%s [", tname_prefix, tname, tname_suffix);
		if(str)str += tmp; maxlen -= tmp; len += tmp;
		if(maxlen<0)maxlen=0;
		arcs = DARCS(d);
		for(i=0;i<d->narcs;i++)
		{
			if(dag_print_style==0)
				tmp = snprintf(str, maxlen, " %s: ", fnames[d->label[i]]);
			else tmp = snprintf(str, maxlen, " %s ", fnames[d->label[i]]);
			if(str)str += tmp; maxlen -= tmp; len += tmp;
			if(maxlen<0)maxlen=0;
			tmp = snrprint_dg(str, maxlen, arcs[i]);
			if(str)str += tmp; maxlen -= tmp; len += tmp;
			if(maxlen<0)maxlen=0;
		}
		tmp = snprintf(str, maxlen, " ]");
		if(str)str += tmp; maxlen -= tmp; len += tmp;
		if(maxlen<0)maxlen=0;
	}
	return len;
}

int	snprint_dg(char	*str, int	maxlen, struct dg	*d)
{
	if(generation>=(MAX_GEN-15))
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}
	generation++;
	dgreset_r(d);
	generation++;
	dgmark(d);
	marker = 1;
	int	len = snrprint_dg(str, maxlen, d);
	generation++;
	dgreset_r(d);
	generation++;
	return len;
}

void	fprint_dg(FILE	*f, struct dg	*d)
{
	int	len = snprint_dg(NULL, 0, d);
	char	*p = malloc(len+1);
	snprint_dg(p, len+1, d);
	fwrite(p, len, 1, f);
}

void	print_dg(struct dg	*d)
{
	fprint_dg(stdout, d);
}

int	dg_size1(struct dg	*d)
{
	if(d->gen == generation)return 0;
	d->gen = generation;
	struct dg	**arcs = DARCS(d);
	int	i, count = 1;
	for(i=0;i<d->narcs;i++)
		count += dg_size1(arcs[i]);
	return count;
}

int	dg_size(struct dg	*d)
{
	bump_generation();
	return dg_size1(d);
}
