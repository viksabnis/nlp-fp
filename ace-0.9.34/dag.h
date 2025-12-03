#ifndef	_DAG_H
#define	_DAG_H

//#define	GEN_SUBSUMPTION_QC

#include	<stdio.h>
#include	<assert.h>
#include	"type.h"

//#define COPY_COUNTS

#define COPY_PATHS
#define	UNIFY_PATHS

// tomabechi dgs

#define	MAX_GEN	0xffffffff
#define	MAX_GEN_RESET 4000000000UL

//#define	MAX_GEN	0xffff
//#define	MAX_GEN_RESET 55000

struct darc
{
	int			label;
	struct dg	*dest;
};

// note: this tries to align to a 32-bit boundary.
// shouldn't we be trying to align to 64-bit boundaries these days?
#define	DAG_EXTRA_LABELS_SIZE_FOR_COUNT(n)	(((n-1)*2+3)/4 * 4)
#define	DAG_EXTRA_LABELS_SIZE(dg1)	DAG_EXTRA_LABELS_SIZE_FOR_COUNT(dg1->narcs)

struct dg
{
	struct type	*type;
	struct type	*xtype;
//#define	DARCS(dg1)	((struct dg**)((void*)dg1+sizeof(struct dg) + (dg1->narcs-2+3)/4 * 4))
#define	DARCS(dg1)	((struct dg**)((void*)dg1+sizeof(struct dg) + DAG_EXTRA_LABELS_SIZE(dg1)))
	//struct dg	*forward;
#define	FORWARD(dg1)	((struct dg*)(dg1->type))
	struct darc	*carcs;
	struct dg	*copy;
	unsigned int	gen;
	unsigned char	narcs, ncarcs:7;
	unsigned char	forwarded:1;
	//unsigned char	label[2];
	unsigned short	label[1];
} __attribute__((packed));

/* idea... threadsafe 8-byte dg nodes
struct dg8
{
	int	type:16;
	int	temp:16;	// dgtmp style; generation and verification pointer lives in dgtmp.
	int	narcs:16;
	int	label[1]:16;
} __attribute__((packed));

// multithreaded access... need a separate dgtmp structure per thread. allocate temp id once, stays allocated until all threads are done with it, then recycled.
// so: array of NxM dgtmp's ; N is max # of IDs needed; M is number of threads.
// say, each thread might be using 1000 at a time (unifying a rule with 2 dtrs could be 300 nodes each easily)
// if 48 threads, = 48k dg nodes in use, so need 48k IDs, so need 48k*48 ~ 2.5m dgtmp structures, each of which is ~32 bytes = 75mb or so. not unreasonable at all. for lower thread counts like 8, only need 8k IDs -> 64k dgtmp structures -> ~2MB  or so.
// temp ids need to be refcounted...
// temp ID management is a potential bottleneck
// each thread gets its own range that it controls allocation from
// but: when arriving at a dg, need to atomically verify no valid temp exists and allocate a new one, and verifying temp is invalid is nontrivial.
// lazy concurrancy?  read 'temp', perform check; if appears to be invalid, allocate a new one and atomically install it provided the invalid one is still there. -> didn't overwrite anyone else's valid ID and now have a valid one to use -- unless another thread just installed a valid tmp with the same ID as the old one. solution to that corner case: prohibit reallocating same temp ID to same node without another temp ID between.
// generations? each thread gets its own.
// generation resets? easier than current: iterate down dgtmp arrays.
// recycling temp IDs? that's hard. have to guarantee no other thread is currently using this ID.
// also hard to know whether an ID is valid (for some other thread) or can safely be replaced
*/

// basic dag operations
int		unify_dg_infrom(struct dg	*dg1, struct dg	*dg2);
struct dg	*unify_dg(struct dg	*a, struct dg	*b, int	arg);
struct dg	*unify_dg_noss(struct dg	*dg1, struct dg	*dg2, int	arg);
struct dg	*atomic_dg(char	*name);
struct dg	*copy_dg(struct dg	*d);
struct dg	*trim_copy(struct dg	*d);
int		lookup_fname(char	*label);
void		null_generation();
void		print_dg(struct dg	*d);
void		fprint_dg(FILE	*f, struct dg	*d);
int			snprint_dg(char	*str, int	maxlen, struct dg	*d);
void		unify_backtrace();
void		funify_backtrace(FILE	*F);
char	*stringify_unify_failure_path();
void		introduce_feature(int	label, int	type);
struct dg	*add_dg_hop(struct dg	*d, int	label, struct dg	*value);
struct dg	*add_dg_feature(struct dg	*d, char	*label, struct dg	*value);
struct dg	*add_dg_path(struct dg	*d, int	*path, int	len, struct dg	*target);
int		init_fnames();
int		equivalent_dg(struct dg	*a, struct dg	*b, int Fw, int Bk, int	leave_marks);
void		setup_extra_type_dgs();
void		setup_carcs_stack();
struct dg	*wellform_dg(struct dg	*dg);
struct dg	*walk_dg(struct dg	*dg, int *save, ...);
void		output_lui_dg(struct dg	*dg, char *wtitle);

struct dg	*generalize(struct dg	*a, struct dg	*b);

// internal operations
int			unify1(struct dg	*dg1, struct dg	*dg2);
struct dg	*copy_dg_with_comp_arcs(struct dg	*dg);

// for hyperactive parsing
struct dg	*daughter_position(struct dg	*mother, int	arg);
int		unify_dg_tmp(struct dg	*dg1, struct dg	*dg2, int	arg);
int		unify_dg_defaults(struct dg	*indef, struct dg	*def);
struct dg	*finalize_tmp(struct dg	*d, int trim);
struct dg	*finalize_tmp_noss(struct dg	*d, int trim);
int		check_cycles(struct dg	*dg);
void		forget_tmp();
long long slab_usage();

// quickcheck operations
#include	"qc.h"

// slab operations
void	clear_slab();
void	commit_slab();
void	*slab_realloc(void	*ptr, int	oldlen, int	newlen);
void	print_slab_stats();

struct slab_state
{
	int	noldslabs;
	void	*slab, *last;
	long long	slabu;
};

static inline void	get_slabstate(struct slab_state	*s)
{
	extern void	*slab, *last;
	extern long long	slabu;
	extern int	noldslabs;
	s->noldslabs = noldslabs;
	s->slab = slab;
	s->last = last;
	s->slabu = slabu;
}

static inline void	set_slabstate(struct slab_state	*s)
{
	extern void	*slab, *last;
	extern long long	slabu;
	extern int	noldslabs;
	noldslabs = s->noldslabs;
	slab = s->slab;
	last = s->last;
	slabu = s->slabu;
}

static inline	void	*slab_alloc(int	len) __attribute__ ((malloc));
void	*mega_slab(long long	size, int	maxmb);
void	*slab_alloc_unaligned(int	len);

static inline void	slab_warm_cache()
{
	extern void	*last, *slab;
	extern long long	slabu, currslabsize;
	// pull the next cacheline that will be allocated from the slab into cache,
	// to avoid taking a cache miss when we allocate it and immediately start writing to it
	__builtin_prefetch(slab+slabu, 1);
}

//#define	DAG_ALIGNMENT	48
#define	DAG_ALIGNMENT	40
static inline	void	*slab_alloc(int	len)
{
	extern void	*last, *slab;
	extern long long	slabu, currslabsize;
	extern void	next_slab();

	assert(len>=0);
	assert((len%4)==0);

	// align these special cases
	//if(len>=48 && len <=64)
	if(len == sizeof(struct dg))	// dag node with no arcs
	{
		if((unsigned long)last % DAG_ALIGNMENT)
		{
			slabu += DAG_ALIGNMENT - ((unsigned long)last % DAG_ALIGNMENT);
			last += DAG_ALIGNMENT - ((unsigned long)last % DAG_ALIGNMENT);
		}
	}
	/*else if(!(len&7))
	{
		if((unsigned int)last & 7)
		{
			slabu += 8 - ((unsigned int)last & 7);
			last += 8 - ((unsigned int)last & 7);
		}
	}*/

	if(len>currslabsize)
	{
		fprintf(stderr, "allocation request %d too big for slab\n", len);
		exit(-1);
	}
	if(slabu+len > currslabsize)next_slab();
	last = slab + slabu;
	slabu += len;
	return last;
}

static inline _set_forward(struct dg	*dg, struct dg	*dest)
{
	dg->forwarded = 1;
	dg->type = (struct type*)dest;
}

static inline struct dg	*p_dereference_dg(struct dg	*dg)
{
	while(dg && dg->gen==9 && dg->forwarded)dg = FORWARD(dg);
	return dg;
}

#ifdef	DEREFERENCE_CHECK_CYCLES
static inline struct dg	*dereference_dg(struct dg	*dg)
{
	struct dg	*fw = dg;
	extern unsigned int	generation;

	while(1)
	{
		// step 'fw' twice
		if(fw->gen==generation || fw->gen==9) { if(fw->forwarded)fw = FORWARD(fw); else return fw; }
		if(fw->gen==generation || fw->gen==9) { if(fw->forwarded)fw = FORWARD(fw); else return fw; }
		else return fw;
		
		// step 'dg' once
		dg = FORWARD(dg);
		if(dg == fw)
		{
			fprintf(stderr, "XXX deref cycle\n");
			return 0;
		}
	}
}
#else
static inline struct dg	*dereference_dg(struct dg	*dg)
{
	extern unsigned int	generation;
	while(dg && (dg->gen==9 || dg->gen==generation) && dg->forwarded)dg = FORWARD(dg);
	return dg;
}
#endif

static inline struct dg	*dg_hop(struct dg	*d, int	label)
{
	int	i, j, k, l;
	extern unsigned int	generation;
	struct dg	**arcs;

	if(d->forwarded)d = dereference_dg(d);
	if(!d)return 0;
	arcs = DARCS(d);

	for(i=0,j=d->narcs;i<j;)
	{
		k = (i+j)>>1;
		//printf("guess %d: %d\n", k, arcs[k].label);
		l = d->label[k];
		if(l==label){d=arcs[k];goto ret;}
		else if(l>label)j = k;
		else i = k+1;
	}
	if(d->gen==generation)
	{
		for(i=0,j=d->ncarcs;i<j;)
		{
			k = (i+j)>>1;
			l = d->carcs[k].label;
			if(l==label){d=d->carcs[k].dest;goto ret;}
			else if(l>label)j = k;
			else i = k+1;
		}
	}
	return 0;
ret:
	if(d->forwarded)return dereference_dg(d);
	else return d;
}

#endif
