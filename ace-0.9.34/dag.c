#include	<stdarg.h>
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>
#include	<sys/types.h>
#include	<unistd.h>
#include	<sys/mman.h>
#include	"dag.h"
#include	"conf.h"
//#include	<asm/mman.h>

#define	MAX_FEATURES	(256*256-1)

extern int	debug_level;
extern int	loud_noises;

// monotonic allocator for dags, can be rolled back to cancel a failed unification
#define	SLAB_SIZE	(1024*1024)	// 1MB per slab
//#define	SLAB_SIZE	(4*1024*1024)	// 4MB per slab -- more likely to get a hugetlb entry

void		**oldslabs;
int		noldslabs, aoldslabs;
long long		currslabsize;

void	*slab, *last;
long long		slabu;

int	nmegaslabs;
long long	megaslab_usage;
void	**megaslabs;

extern void	*freeze_point, *freeze_next;
extern int	freeze_fd;

long long	accum_ram_usage = 0;

#ifdef	UNIFY_PATHS
int	upath[1024];
int	upathl, upathgl;
struct type	*uglb;
struct type	*ut1, *ut2;
#endif

long long slab_usage() { return (long long)(noldslabs-1)*SLAB_SIZE + slabu + megaslab_usage; }

int	slab_size_in_bytes()
{
	return (noldslabs-1)*SLAB_SIZE + slabu + megaslab_usage;
}

void	print_slab_stats()
{
	fprintf(stderr, "RAM: %lldk\n", ((long long)noldslabs-1)*1024 + slabu/1024 + megaslab_usage/1024);
}

void	next_slab();

void	commit_slab()
{
	assert(!nmegaslabs);
	if(freeze_next)
	{
		printf("freezing %.1fM to file map %p\n", (float)slabu/1024/1024, freeze_point);
		if(ftruncate(freeze_fd, slabu)) { perror("ftruncate to final length"); exit(-1); }
		if(msync(freeze_point, slabu, MS_ASYNC)) { perror("msync"); exit(-1); }
		close(freeze_fd);
		freeze_next = NULL;
	}
	else if(debug_level) { fprintf(stderr, "permanent "); print_slab_stats(); fprintf(stderr, "\n"); }
	currslabsize = SLAB_SIZE;
	noldslabs = 0;
	aoldslabs = 0;
	next_slab();
}

void	clear_slab()
{
	int	i;

	if(freeze_next)
	{
		noldslabs = 0;
		last = slab = freeze_next;
		slabu = 0;
		assert(!nmegaslabs);
	}
	else
	{
		if(noldslabs)
		{
			unsigned long long	ram = (unsigned long long)SLAB_SIZE*(noldslabs-1) + slabu;
			accum_ram_usage += ram;
		}
		// leave up to 64 allocated slabs around for next parse!
		if(aoldslabs>64)
		{
			for(i=64;i<aoldslabs;i++)
			{
				//free(oldslabs[i]);
				munmap(oldslabs[i], SLAB_SIZE);
				oldslabs[i] = NULL;
			}
			aoldslabs = 64;
		}
		noldslabs = 0;
		next_slab();
		currslabsize = SLAB_SIZE;
		for(i=0;i<nmegaslabs;i++)
			free(megaslabs[i]);
		nmegaslabs = 0;
		megaslab_usage = 0;
	}
}

#ifndef MAP_ANONYMOUS
#define	MAP_ANONYMOUS	MAP_ANON
#endif

void	next_slab()
{
	if(freeze_next)
	{
		fprintf(stderr, "ran out of room in the freezer; try a larger `freezer-megabytes' value.\n");
		exit(-1);
	}
	noldslabs++;
	if(noldslabs > aoldslabs)
	{
		aoldslabs++;
		if(debug_level>1 && noldslabs>1)fprintf(stderr, "slab: moving to next slab with old at %lldkbytes\n", slabu/1024);
		oldslabs = realloc(oldslabs, sizeof(void*)*aoldslabs);
		//oldslabs[aoldslabs-1] = malloc(SLAB_SIZE);
		/*void	*ptr = mmap(NULL, SLAB_SIZE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_HUGETLB, -1, 0);
		if(!ptr)
		{
			perror("mmap hugetlb failed");
			ptr = mmap(NULL, SLAB_SIZE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
		}*/
		void	*ptr = mmap(NULL, SLAB_SIZE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
		oldslabs[aoldslabs-1] = ptr;
	}
	slab = oldslabs[noldslabs-1];
	slabu = 0;
	last = slab;
}

void	*mega_slab(long long	size, int	maxmb)
{
	if((slab_usage() + size) / (1024*1024) > maxmb)return NULL;
	nmegaslabs++;
	megaslab_usage += size;
	megaslabs = realloc(megaslabs, sizeof(void*)*nmegaslabs);
	megaslabs[nmegaslabs-1] = malloc(size);
	return megaslabs[nmegaslabs-1];
}

void	*slab_realloc(void	*ptr, int	oldlen, int	newlen)
{
	if(oldlen > newlen)
	{
		if(ptr == last)
			slabu -= oldlen - newlen;
		return ptr;
	}
	else /*if(ptr == last && slabu -oldlen +newlen < currslabsize)
	{
		slabu += newlen - oldlen;
		return ptr;
	}
	else*/
	{
		void *to = slab_alloc(newlen);
		memcpy(to, ptr, oldlen);
		return to;
	}
}

void	*slab_alloc_unaligned(int	len)
{
	if(len%4)len = len + 4 - (len%4);
	return slab_alloc(len);
}

struct dg	*walk_dg(struct dg	*dg, int *save, ...)
{
	va_list	va;
	int		i = 0;
	char	*fname;

	va_start(va, save);
	if(save[0]==-1)
	{
		while((fname = va_arg(va, char*)) != NULL)
		{
			save[i] = lookup_fname(fname);
			if(dg)dg = dg_hop(dg, save[i]);
			i++;
		}
	}
	else while((fname = va_arg(va, char*)) != NULL)
	{
		if(dg)dg = dg_hop(dg, save[i++]);
	}
	va_end(va);
	return dg;
}

struct dg	*atomic_dg(char	*name)
{
	struct type	*type = lookup_type(name);
	struct dg	*dg;

	if(!type)
	{
		fprintf(stderr, "atomic_dg: no such type as `%s'\n", name);
		exit(-1);
		return NULL;
	}

	dg = slab_alloc(sizeof(struct dg));
	bzero(dg, sizeof(struct dg));
	dg->gen = 10;
	dg->type = dg->xtype = type;
	return dg;
}

struct dg	*add_dg_hop(struct dg	*d, int	label, struct dg	*value)
{
	int	i, olen, nlen;
	struct dg	*dn;
	struct dg	**arcs;

	//printf("add hop [%d -> %p], current arcs:\n", label, value);
	//for(i=0;i<d->narcs;i++)printf("   %d -> %p\n", d->label[i], DARCS(d)[i]);

	d = dereference_dg(d);
	// find in sorted order
	for(i=0;i<d->narcs;i++)if(d->label[i]>=label)break;

	if(i==d->narcs || d->label[i]>label)
	{
		// need to grow list of arcs
		int	oab = DAG_EXTRA_LABELS_SIZE(d);
		d->narcs++;
		int	ab = DAG_EXTRA_LABELS_SIZE(d);
		olen = sizeof(struct dg) + oab + sizeof(struct dg*) * (d->narcs-1);
		nlen = sizeof(struct dg) + ab + sizeof(struct dg*) * d->narcs;
		dn = slab_realloc(d, olen, nlen);
		if(dn != d)
		{
			// oops! we left the old dg behind, forward it along
			permanent_forward_dg(d, dn);
			d = dn;
		}
		// arcs go directly after the `struct dg'
		struct dg	**oarcs;
		arcs = (struct dg**)((void*)d + sizeof(*d) + ab);
		oarcs = (struct dg**)((void*)d + sizeof(*d) + oab);
		memmove(arcs, oarcs, sizeof(struct dg*)*(d->narcs-1));

		memmove(arcs+i+1, arcs+i, sizeof(struct dg*)*(d->narcs-1-i));
		memmove(d->label+i+1, d->label+i, 2*(d->narcs-1-i));
	}
	else arcs = DARCS(d);

	d->label[i] = label;
	arcs[i] = value;

	//printf("now arcs:\n", label, value);
	//for(i=0;i<d->narcs;i++)printf("   %d -> %p\n", d->label[i], DARCS(d)[i]);

	return d;
}

int		nfnames;
char		**fnames;

int	subsume_forward, subsume_backward;

int	gsubsume_forward, gsubsume_backward;

//#define	GEN_SUBSUMPTION_QC
#ifndef	GEN_SUBSUMPTION_QC
#define	ss_backtrace(a,b,k)  do {} while(0)
#else
#define ss_backtrace	real_ss_backtrace
#endif

real_ss_backtrace(struct dg	*a, struct dg	*b, char	*code)
{
	int i;
	printf("%s -- `%s'#%d vs `%s'#%d flags %d %d\n", code, a->xtype->name, a->narcs, b->xtype->name, b->narcs, subsume_forward, subsume_backward);
	for(i=0;i<a->narcs;i++)printf(" %s", fnames[a->label[i]]); printf("\n");
	for(i=0;i<b->narcs;i++)printf(" %s", fnames[b->label[i]]); printf("\n");
	printf("subsumption failure at path:  "); unify_backtrace();
}

//#define	SS_GET_SCRATCH(d)	FORWARD(d)
//#define	SS_SET_SCRATCH(d,v)	_set_forward(d, v)

#define	SS_GET_SCRATCH(d)	((struct dg*)((d)->carcs))
#define	SS_SET_SCRATCH(d,v)	do { (d)->carcs = (struct darc*)(v); } while(0)

// due to subgraph sharing, a node 'a' can appear in both inputs to subsume_dg1(a,b).
// it is not automatically equivalent; different reentrancies can appear from the (nonidentical) rest of the dags into 'a'
// e.g.:   x = [ A: #1=moo B: #2=moo C: #2=moo ]   and y = [ A: #2=moo B: #2=moo C: #3=moo ]
// we would use subsume_same_dg(#2) and notice that #2 is reentrant with #1 on the left and #3 on the right.
// make sure 'copy' is either null or self-referential all the way through 'a's arcs
int	subsume_same_dg(struct dg	*a)
{
	int	i;
	extern unsigned int	generation;
	struct dg	**arcs;

	//return 0;
	//printf("sssd %p?\n", a);
	a = p_dereference_dg(a);

	if(a->gen!=generation)
	{
		a->copy = 0;
		a->carcs = 0; a->ncarcs = 0;
		SS_SET_SCRATCH(a, NULL);
		a->gen = generation;
		a->type = a->xtype;
		a->forwarded = 0;
	}

	if(a->copy==a && SS_GET_SCRATCH(a)==a)return 1;
	if(a->copy) { if(subsume_forward)ss_backtrace(a,a, "same-dag: can't subsume forward"); subsume_forward = 0; gsubsume_forward = 0; }
	if(SS_GET_SCRATCH(a)) { if(subsume_backward)ss_backtrace(a,a, "same-dag: can't subsume backward"); subsume_backward = 0; gsubsume_backward = 0; }
	if(!gsubsume_forward && !gsubsume_backward)
	{
		ss_backtrace(a, a, "same-dag: had been here from one side but not both");
		return 0;
	}

	a->copy = a;
	SS_SET_SCRATCH(a, a);

	arcs = DARCS(a);
	for(i=0;i<a->narcs;i++)
	{
		upath[upathl++] = a->label[i];
		if(!subsume_same_dg(arcs[i]))return 0;
		upathl--;
	}
	return 1;
}

int	uindifflist = 0;

static inline int	is_difflist(struct type	*t)
{
	static struct type	*difflist = NULL;
	static struct type_hierarchy	*th;
	static char	*type_difflist_cache = NULL;
	static int	type_difflist_cache_size;
	if(!difflist)
	{
		th = default_type_hierarchy();
		difflist = lookup_type(g_diff_list_type);
		type_difflist_cache_size = th->ntypes;
		type_difflist_cache = calloc(1,type_difflist_cache_size);
	}
	if(t->name[0]=='"')return 0;
	assert(t->tnum>=0 && t->tnum < th->ntypes);
	assert(th->ntypes == type_difflist_cache_size);
	if(!type_difflist_cache[t->tnum])
		type_difflist_cache[t->tnum] = descendent_of(t->tnum, difflist)?2:1;
	int	answer = type_difflist_cache[t->tnum] - 1;
	//assert(answer == (descendent_of(t->tnum, difflist)?1:0));
	return answer;
}

// on input, assume a and b both have noncurrent generation
// on output, 'copy' pointers are used, so don't try to copy them until next generation
int	subsume_dg1(struct dg	*a, struct dg	*b)
{
	int	i, j;
	extern unsigned int	generation;
	struct dg	**aarcs, **barcs;

	//printf("ssdg1 %p %s [%d] %p %s [%d]?\n", a, a->xtype->name, a->xtype->tnum, b, b->xtype->name, b->xtype->tnum);

	a = p_dereference_dg(a);
	b = p_dereference_dg(b);

	if(a==b)
	{
		int	sssd = subsume_same_dg(a);
		//printf("sssd = %d\n", sssd);
		return sssd;
	}
	if(a->gen!=generation)
	{
		//printf("reset lhs\n");
		a->copy = 0;
		a->carcs = 0; a->ncarcs = 0;
		SS_SET_SCRATCH(a, NULL);
		a->gen = generation;
		a->type = a->xtype;
		a->forwarded = 0;
	}
	if(b->gen!=generation)
	{
		//printf("reset rhs\n");
		b->copy = 0;
		b->carcs = 0; b->ncarcs = 0;
		SS_SET_SCRATCH(b, NULL);
		b->gen = generation;
		b->type = b->xtype;
		b->forwarded = 0;
	}

	int	dont_generalize_at_all = 0;
	// if a has been used as part of b or b has been used as part of a, refuse to generalize.
	if(SS_GET_SCRATCH(a) || b->copy)
		dont_generalize_at_all = 1;

	/*
	// XXX experiment to see whether refusing to generalize "GENRE" and "HEAD"
	// can significantly reduce unpacking workload.
	// root-cell edges can look like they meet a root condition but their unpackings don't actually...
	static int	genre_feat = -1, head_feat = -1;
	if(genre_feat == -1)
	{
		if(feature_exists("GENRE"))genre_feat = lookup_fname("GENRE");
		else genre_feat = -2;
		if(feature_exists("HEAD"))head_feat = lookup_fname("HEAD");
		else head_feat = -2;
	}
	if(upathl && (upath[upathl-1]==genre_feat || upath[upathl-1]==head_feat))
	{
		//printf("declining to consider generalizing %s + %s\n", a->xtype->name, b->xtype->name);
		dont_generalize_at_all = 1;
	}*/

	int	types_identical = (a->xtype == b->xtype) || (a->xtype->tnum==-1 && b->xtype->tnum==-1 && !strcmp(a->xtype->name, b->xtype->name));

	struct type	*lower = a->xtype;

	if(!types_identical)
	{
		lower = glb(a->xtype, b->xtype);

		struct type_hierarchy	*th = default_type_hierarchy();
		int	old_subsume_forward = subsume_forward;
		int	old_subsume_backward = subsume_backward;
		int	local_ss = 0;
		/*if(b->xtype->name[0]=='"')
		{
			if(!descendent_of(th->strtype->tnum, a->xtype))subsume_forward = 0;
			else local_ss = 1;
		}
		else
		{
			if(!descendent_of(b->xtype->tnum, a->xtype))subsume_forward = 0;
			else local_ss = 1;
		}
		if(a->xtype->name[0]=='"')
		{
			if(!descendent_of(th->strtype->tnum, b->xtype))subsume_backward = 0;
			else local_ss = 1;
		}
		else
		{
			if(!descendent_of(a->xtype->tnum, b->xtype))subsume_backward = 0;
			else local_ss = 1;
		}*/
		if(b->xtype == lower)local_ss = 1;
		else subsume_forward = 0;
		if(a->xtype == lower)local_ss = 1;
		else subsume_backward = 0;
		if(dont_generalize_at_all)
		{
			if(b->xtype == lower)gsubsume_backward = 0;
			if(a->xtype == lower)gsubsume_forward = 0;
		}
		if(!local_ss)
		{
			/*if(1)//a->narcs==0 && b->narcs==0)
			{
				// this code is for generalizing to a type more general than either a or b,
				// in controlled conditions.  it finds some interesting ideas,
				// but it seems that when you have to do this, other parts of the dag are
				// overwhelmingly uncooperative and we just can't make
				// the generalization edge very often.
				// see if we can pick a type that tightly generalizes them
				struct type	*upper = lub(a->xtype, b->xtype);
				if(upper->ndaughters==2 &&
					((a->xtype == upper->daughters[0] && b->xtype == upper->daughters[1])
					|| (a->xtype == upper->daughters[1] && b->xtype == upper->daughters[0]))
					&& a->narcs == b->narcs && a->narcs == upper->dg->narcs)
				{
					if(gsubsume_forward)a->type = upper;
					if(gsubsume_backward)b->type = upper;
					ut1 = a->xtype;
					ut2 = b->xtype;
					ss_backtrace(a, b, "tentatively extra-generalized");
					printf("generalized %s and %s to %s\n", a->xtype->name, b->xtype->name, upper->name);
				}
				else gsubsume_backward = gsubsume_forward = 0;
			}
			else */gsubsume_backward = gsubsume_forward = 0;
		}
		else
		{
			assert(a->xtype==lower || b->xtype==lower);
			struct type	*upper = (lower==a->xtype)?b->xtype:a->xtype;
			if(gsubsume_forward)a->type = upper;
			if(gsubsume_backward)b->type = upper;
			//fprintf(stderr, "generalized %p and %p to %s\n", a, b, upper->name);
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, "tentatively generalized");
		}

		if(!subsume_forward && !subsume_backward)
		{
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, (old_subsume_forward && old_subsume_backward)?"multi-dag: incompatible types":( old_subsume_forward?"multi-dag: needed forward but failed":"multi-dag: needed backward but failed" ));
			if(!gsubsume_forward && !gsubsume_backward)
				return 0;
		}
		else if(old_subsume_forward && !subsume_forward)
		{
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, "multi-dag: ruled out forward subsumption");
		}
		else if(old_subsume_backward && !subsume_backward)
		{
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, "multi-dag: ruled out backward subsumption");
		}
	}

	if(a->copy == b && SS_GET_SCRATCH(b) == a)return 1;

	if(!a->copy)a->copy = b;
	else if(a->copy != b)
	{
		if(subsume_forward || gsubsume_forward)
		{
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, "multi-dag: ruled out forward subsumption due to reentrancies");
		}
		subsume_forward = 0;
		gsubsume_forward = 0;
		//printf("not forward... (lhs = %p)\n", a->copy);
	}

	if(!SS_GET_SCRATCH(b))SS_SET_SCRATCH(b, a);
	else if(SS_GET_SCRATCH(b) != a)
	{
		if(subsume_backward || gsubsume_backward)
		{
			ut1 = a->xtype;
			ut2 = b->xtype;
			ss_backtrace(a, b, "multi-dag: ruled out backward subsumption due to reentrancies");
		}
		subsume_backward = 0;
		gsubsume_backward = 0;
		//printf("not backward... (rhs = %p)\n", SS_GET_SCRATCH(b));
	}

	if(!gsubsume_forward && !gsubsume_backward)
	{
		ut1 = a->xtype;
		ut2 = b->xtype;
		ss_backtrace(a, b, "multi-dag: bad reentrancies");
		return 0;
	}

	//printf("maybe %p [%s] <=> %p [%s]\n", a, a->xtype->name, b, b->xtype->name);

	int	local_indifflist = 0;
	if(is_difflist(a->xtype) || is_difflist(b->xtype))local_indifflist = 1;
	if(local_indifflist)uindifflist++;

	// there are certain cases where we don't want to apply generalization packing with different arc sets, even if we could.
	// 1. the toppath, since copying an edge generalized to 'sign' with the appropriateness restrictor will kill off too much
	// 2. difflists, since generalizing turns out to be capable of washing out the difference between empty and nonempty SLASHes
	int	dont_generalize_arcs = dont_generalize_at_all;
	if(upathl == 0)dont_generalize_arcs = 1;
	else if(uindifflist)dont_generalize_arcs = 1;
	// uncomment this line to never generalize over different arc sets:
	//dont_generalize_arcs = 1;

	aarcs = DARCS(a);
	barcs = DARCS(b);
	if(types_identical && a->narcs==b->narcs)
	{
		// well-formedness and sortedness conditions guarantee that since
		// types match exactly, arc labels match exactly...
		for(i=0;i<a->narcs;i++)
		{
			assert(a->label[i] == b->label[i]);
			upath[upathl++] = a->label[i];
			if(!subsume_dg1(aarcs[i], barcs[i]))return 0;
			upathl--;
		}
	}
	else if(b->xtype==lower && a->narcs<=b->narcs) // b is subtype of a, so has strict superset of features
	{
		if(subsume_backward)ss_backtrace(a, b, "ruled out backward due to lower type/feature set");
		subsume_backward = 0;
		if(a->narcs < b->narcs && dont_generalize_arcs)gsubsume_backward = 0;
		for(i=j=0;i<b->narcs;i++)
		{
			if(j>=a->narcs)break;
			if(a->label[j] == b->label[i])
			{
				upath[upathl++] = a->label[j];
				if(!subsume_dg1(aarcs[j], barcs[i]))return 0;
				upathl--;
				j++;
			}
		}
	}
	else if(a->xtype==lower && b->narcs<=a->narcs) // a is subtype of b, so has strict superset of features
	{
		if(subsume_forward)ss_backtrace(a, b, "ruled out forward due to lower type/feature set");
		subsume_forward = 0;
		if(b->narcs < a->narcs && dont_generalize_arcs)gsubsume_forward = 0;
		for(i=j=0;i<a->narcs;i++)
		{
			if(j>=b->narcs)break;
			if(a->label[i] == b->label[j])
			{
				upath[upathl++] = a->label[i];
				if(!subsume_dg1(aarcs[i], barcs[j]))return 0;
				upathl--;
				j++;
			}
		}
	}
	else
	{
		subsume_forward = 0;
		subsume_backward = 0;
		gsubsume_forward = 0;
		gsubsume_backward = 0;
		ss_backtrace(a, b, "multi-dag: incompatible arc set");
		return 0;
	}
	if(local_indifflist)uindifflist--;
	return 1;
}

int	equivalent_dg(struct dg	*a, struct dg	*b, int Fw, int Bk, int	leave_marks)
{
	int	res;
	extern unsigned int	generation;

	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "generation counter overflowed!\n");
		exit(-1);
	}

	upathl = 0;
	uindifflist = 0;
	ut1 = ut2 = NULL;
	subsume_forward = Fw;
	subsume_backward = Bk;
	gsubsume_forward = 1;
	gsubsume_backward = 1;
	res = subsume_dg1(a, b);
	if(!leave_marks)
	{
		generation++;
		if(generation==MAX_GEN)
		{
			fprintf(stderr, "generation counter overflowed!\n");
			exit(-1);
		}
	}
	upathl = 0;

	//fprintf(stderr, "subs %p %p = %d %d %d\n", a, b, res, subsume_forward, subsume_backward);

	//if(res && subsume_forward && !subsume_backward)printf("would have subsumed forward\n");
	//else if(res && subsume_backward && !subsume_forward)printf("would have subsumed backward\n");
	/*if(res && subsume_backward && !subsume_forward)
			fprintf(stderr, "NOTE: back-subsumption\n");
	if(res && subsume_forward)
			fprintf(stderr, "NOTE: >= subsumption\n");*/

	//if(res)
	{
		//if(subsume_forward && subsume_backward)return 1;
		//else return 0;
		//printf("subs-forward = %d, subs-backward = %d\n", subsume_forward, subsume_backward);
		if(subsume_forward && subsume_backward)return 2;
		if(subsume_forward)return 1;
		if(subsume_backward)return -1;
		if(gsubsume_forward)return 3;
		if(gsubsume_backward)return -3;
	}
	return 0;
	//return res;
}

int		*introduce;	// what type introduced this fname?

struct dg	*wellform_dg(struct dg	*dg)
{
	struct dg	*wfee;
	// slight trick: wellform() only applies to stuff inside its argument, not to the top level.
	wfee = atomic_dg(top_type); wfee = add_dg_hop(wfee, 1, dg);
	int result = wellform(wfee, "mrs variable");
	if(result == 0)return dg_hop(wfee, 1);
	else return NULL;
}

struct type	*most_general_type_for_feat(struct type_hierarchy	*th, int	feat)
{
	if(feat<0 || feat>=nfnames)return 0;
	if(introduce[feat] == -1)
	{
		fprintf(stderr, "ERROR: no type is appropriate for feature `%s' yet\n", fnames[feat]);
		exit(-1);
	}
	struct dg	*tdg = th->types[introduce[feat]]->dg, *h = dg_hop(tdg, feat);
	return h->xtype;
}

struct type	*most_general_type_for_dg(struct dg	*d)
{
	struct type_hierarchy	*th = default_type_hierarchy();
	int	i, intro = -1, k;
	struct type	*up = 0, *ty;

	for(i=0;i<d->narcs;i++)
	{
		k = introduce[d->label[i]];
		if(k==-1)
		{
			fprintf(stderr, "ERROR: tried to wellform a dag containing feature `%s', "
					"which was never introduced in the type hierarchy\n", fnames[d->label[i]]);
			return NULL;
		}
		ty = th->types[k];
		/*if(k>intro)
		{
			//printf("dag `%s' uses `%s', introduced by %s\n",
					//d->xtype->name, fnames[d->label[i]],
					//th->types[introduce[d->label[i]]]->name);
			intro = k;
		}*/
		if(!up)up = ty;
		else
		{
			struct type *nup;
			nup = glb(up, ty);
			if(!nup)
			{
				fprintf(stderr, "type inference:  no glb for `%s' and `%s'\n", up->name, ty->name);
				for(i=0;i<d->narcs;i++)fprintf(stderr, "  %s	appropriate to %s\n", fnames[d->label[i]], th->types[introduce[d->label[i]]]->name);
				return NULL;
			}
			up = nup;
		}
	}
	//if(intro==-1)return d->xtype;
	if(!up)
	{
		//if(d->narcs)printf("type inferred for %d features [%s ...] = null\n", d->narcs, fnames[d->label[0]]);
		return d->xtype;
	}
	else
	{
		//printf("type inferred for %d features = %s\n", d->narcs, up->name);
		return glb(d->xtype, up);
		//return glb(d->xtype, types[intro]);
		//if(descendent_of(d->xtype->tnum, types[intro]))return d->xtype;
		//return types[intro];
	}
}

void	introduce_feature(int	label, int	type)
{
	if(introduce[label]==-1 || introduce[label] > type)
	{
		introduce[label] = type;
		//printf("type %s introduces feature %s\n", default_type_hierarchy()->types[type]->name, fnames[label]);
	}
}

int reload_restrictors = 1, restrictor_size = 0;

int	feature_exists(char	*label)
{
	int i;
	for(i=0;i<nfnames;i++)
		if(!strcasecmp(fnames[i], label))return 1;
	return 0;
}

int	lookup_fname(char	*label)
{
	int	i;
	extern int g_mode, g_transfer;

	for(i=0;i<nfnames;i++)
		if(!strcasecmp(fnames[i], label))return i;
	nfnames++;
	fnames = realloc(fnames, sizeof(char*) * nfnames);
	fnames[i] = strdup(label);
	introduce = realloc(introduce, sizeof(int) * nfnames);
	introduce[i] = -1;
	//if(!g_transfer)
	{
		reload_restrictors = 1;
		if(nfnames >= MAX_FEATURES) { fprintf(stderr, "ERROR: new feature '%s' is %d'th\n", label, MAX_FEATURES); exit(-1); }
		if(g_mode != -1) { fprintf(stderr, "WARNING: added new feature `%s' at runtime\n", label); }
	}
	return i;
}

#ifdef	UNIFY_PATHS
void	funify_backtrace(FILE	*f)
{
	int	i;

	fflush(f);
	fprintf(f, "unify failed at path: ");
	for(i=0;i<upathl;i++)fprintf(f, "%s ", fnames[upath[i]]);
	fprintf(f, "\n");
	fflush(f);
	if(uglb) fprintf(f, "    inside glb constraint for `%s' depth %d\n", uglb->name, upathgl);
	if(ut1 && ut2)
		fprintf(f, "  might have been trying to unify types %s + %s\n", ut1->name, ut2->name);
}

void	unify_backtrace() { funify_backtrace(stdout); }

char	*stringify_unify_failure_path()
{
	int	i, l = 0;
	for(i=0;i<upathl;i++)l += strlen(fnames[upath[i]]) + 5;
	char	*path = malloc(l);
	*path = 0;
	for(i=0;i<upathl;i++)
	{
		if(i)strcat(path, " ");
		strcat(path, fnames[upath[i]]);
	}
	return path;
}

void	subsume_backtrace()
{
	int	i;

	fflush(stdout);
	fprintf(stdout, "subsumption failed at path: ");
	for(i=0;i<upathl;i++)fprintf(stdout, "%s ", fnames[upath[i]]);
	fprintf(stdout, "\n");
	fflush(stdout);
	if(ut1 && ut2)
		fprintf(stdout, "  types %s + %s\n", ut1->name, ut2->name);
}

struct path	unify_backtrace_path()
{
	struct path p = {.count = upathl, .fnums = upath};
	return p;
}
#endif

struct dg	*add_dg_feature(struct dg	*d, char	*label, struct dg	*value)
{
	return add_dg_hop(d, lookup_fname(label), value);
}

int	init_fnames()
{
	nfnames = 3;
	fnames = malloc(sizeof(char*)*nfnames);
	introduce = malloc(sizeof(int)*nfnames);
	memset(introduce, -1, sizeof(int)*nfnames);

	fnames[0] = strdup("ARGS");
	fnames[1] = strdup("FIRST");
	fnames[2] = strdup("REST");

	return 0;
}

// array saying for each feature whether to drop it during unification / copying
char	*copy_restrictor;
char	*unify_restrictor;

char	*deleted_daughters, *parsing_packing, *generating_packing, *ep_drop;

void print_restrictor(char *name, char *restr)
{
	int i;

	printf("%s:", name);
	for(i=0;i<nfnames;i++)
		if(restr[i])printf(" %s", fnames[i]);
	printf("\n");
}

void load_restrictors()
{
	int		i;
	extern int g_mode, g_transfer;
	//if(g_transfer)return;
	assert(g_mode == -1);

	if(deleted_daughters)free(deleted_daughters);
	if(parsing_packing)free(parsing_packing);
	if(generating_packing)free(generating_packing);
	if(ep_drop)free(ep_drop);
	deleted_daughters = calloc(nfnames, 1);
	parsing_packing = calloc(nfnames, 1);
	generating_packing = calloc(nfnames, 1);
	ep_drop = calloc(nfnames, 1);
	for(i=0;i<nfnames;i++)
	{
		deleted_daughters[i] = check_conf_list("deleted-daughters", fnames[i]);
		parsing_packing[i] = check_conf_list("parsing-packing-restrictor", fnames[i]);
		generating_packing[i] = check_conf_list("generation-packing-restrictor", fnames[i]);
		ep_drop[i] = check_conf_list("mrs-deleted-roles", fnames[i]);
	}

	restrictor_size = nfnames;
	reload_restrictors = 0;
}

void	load_ep_drop()
{
	if(reload_restrictors)load_restrictors();
}

void enable_trim(int trim)
{
	if(reload_restrictors)load_restrictors();
	if(trim)copy_restrictor = deleted_daughters;
	else copy_restrictor = 0;
}

void enable_packing(int how)
{
	if(reload_restrictors)load_restrictors();
	if(how==0)unify_restrictor = 0;
	else if(how==1)unify_restrictor = parsing_packing;
	else if(how==2)unify_restrictor = generating_packing;
}

struct dg	*noninline_dg_hop(struct dg	*d, int	f)
{
	return dg_hop(d, f);
}
