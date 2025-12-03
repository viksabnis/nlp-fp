#include	<stdlib.h>
#include	<stdio.h>

#include	"chart.h"
#include	"type.h"

int	glb_ncollis, glb_nhit, glb_nmiss;

#define	HSIZE		32768
#define	ROLLOVER	6

extern int	glb_ncollis, glb_nhit, glb_nmiss;
static struct type	*calc_glb(struct type	*a, struct type	*b);

static struct glb_hashent
{
	struct type	*glb, *a, *b;
	int		use;
}	*htab;

void	init_glb_cache()
{
	if(!htab)htab = calloc(sizeof(struct glb_hashent), HSIZE+ROLLOVER);
}

struct type	*glb(struct type	*a, struct type	*b)
{
	unsigned long	h;
	int		i, j, min = 0x3fff0000;
	register struct glb_hashent	*ht, *mh;

	if(a==b)return a;
	if(a>b)
	{
		struct type *tmp;
		tmp = a;
		a = b;
		b = tmp;
	}

	h = (((unsigned long)a>>6) ^ ((unsigned long)b>>0)) & (HSIZE-1);
	ht = htab + h;
	__builtin_prefetch(ht, 0, 0);

	// check for a,b in 
	for(j=0;j<ROLLOVER;j++)
	{
		if(ht->a==a && ht->b==b)
			return ht->glb;
		if(!ht->use)	// this automatically wins
			goto grab;
		if(ht->use < min)
		{
			mh = ht;
			min = ht->use;
		}
		ht++;
	}
	ht = mh;

grab:
	glb_nmiss++;
	ht->a = a;
	ht->b = b;
	ht->use = 1;
	ht->glb = calc_glb(a, b);

	ret:
	return ht->glb;
}

/*struct type_hierarchy	*type_hierarchy_of(struct type	*a)
{
	extern struct type_hierarchy	*semi_th, *main_th;
	if(!semi_th)return main_th;
	if(a->name[0]=='"')
	{
		if(a->tnum < main_th->nstrings && main_th->strings[a->tnum]==a)
			return main_th;
		if(a->tnum < semi_th->nstrings && semi_th->strings[a->tnum]==a)
			return semi_th;
		return NULL;
	}
	if(a->tnum < main_th->ntypes && main_th->types[a->tnum]==a)
		return main_th;
	if(a->tnum < semi_th->ntypes && semi_th->types[a->tnum]==a)
		return semi_th;
	assert(!"no such type hierarchy");
}*/

// static because it doesn't work when a==b, and we don't want someone
// calling it from outside without realizing that...
static struct type	*calc_glb(struct type	*a, struct type	*b)
{
	struct type_hierarchy	*th = default_type_hierarchy();
	int	ia, ib;

	if(a->name[0]=='"')
	{
		if(b->name[0]=='"')
		{
			// both string types.
			// if they are both *temporary* string types,
			// then they could be distinct pointers and still equivalent.
			if(a->tnum==-1 && b->tnum==-1 && !strcmp(a->name, b->name))
				return a;
			// otherwise, they have to be identical pointers to be equivalent,
			// and that case has already been tested beefore calc_glb() is called.
			return NULL;
		}
		else if(th->strtype && descendent_of(th->strtype->tnum, b))return a;
		else return NULL;
	}
	if(b->name[0]=='"')
	{
		if(th->strtype && descendent_of(th->strtype->tnum, a))return b;
		else return NULL;
	}

	//fprintf(stderr, "glb %s, %s?\n", a->name, b->name);
	ia = ib = 0;
	while(ia < a->ndescendents && ib < b->ndescendents)
	{
		if(a->descendents[ia] == b->descendents[ib])
		{
			// must be the glb, since types are in descending order
			return th->types[a->descendents[ia]];
		}
		else if(a->descendents[ia] < b->descendents[ib])ia++;
		else ib++;
	}
	//fprintf(stderr, "no glb for %s, %s\n", a->name, b->name);
	return NULL;
}

void	print_glb_stats()
{
	extern unsigned long long glb_clock, glb_count;
	extern unsigned long long extract_clock, extract_count;
	extern unsigned long long unify_clock, unify_count;
	fprintf(stderr, "NOTE: glb hash: %d direct hits, %d collisions, %d misses\n", glb_nhit, glb_ncollis, glb_nmiss);
#ifdef	CLOCKCOUNT
	fprintf(stderr, "avg qc-glb %e over %lld glbs\n", (double)glb_clock/glb_count, glb_count);
	fprintf(stderr, "avg qc-ext %e over %lld exts\n", (double)extract_clock/extract_count, extract_count);
	fprintf(stderr, "avg unify  %e over %lld unis\n", (double)unify_clock/unify_count, unify_count);
#endif
}
