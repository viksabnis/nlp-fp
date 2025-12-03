#include	<stdlib.h>
#include	<assert.h>
#include	<string.h>
#include	<time.h>

#include	"conf.h"
#include	"chart.h"
#include	"dag.h"
#include	"tdl.h"

#include	"timer.h"

//#define	HIDEOUS_HACK
#undef	HIDEOUS_HACK

/* essentially, QC extracts a skeleton type tree from a dag
 * and performs *tree*-unification on that skeleton before
 * the full dag-unifier is allowed to run */

int	qc_size;

struct qc
{
	struct type	*entries[1];
};

int	__qc_use_heap = 0;

#ifdef HIDEOUS_HACK
static struct type	*olist, *minus, *_0dlist;
static struct type	*no_punct, *no_punctuation_min;
#endif

extern int gen_qc;

int	eqc_timer = -1;

qc_extractor_function	qc_extractor = NULL;

struct type	*dg_type(struct dg	*d)
{
	extern unsigned int	generation;
	// this is called on the results of dg_hop... safe to assume it is dereferenced.
	if(d->gen == generation)return d->type;
	return d->xtype;
}

struct qc	*extract_qc(struct dg	*d)
{
	struct qc	*q;
	long		i, iter, sp = 0, dst, fn, onf;
	int			*lp;

	if(gen_qc)return NULL;

	static int init = 0;
	if(!init)
	{
		init = 1;
		qc_extractor = dynamically_link_qc_extractor();
#ifdef	HIDEOUS_HACK
		olist = lookup_type("*olist*");
		assert(olist);
		minus = lookup_type("-");
		assert(minus);
		_0dlist = lookup_type("0-dlist");
		assert(_0dlist);

		no_punct = lookup_type("no_punct");
		assert(no_punct);
		no_punctuation_min = lookup_type("no_punctuation_min");
		assert(no_punctuation_min);
#endif
		eqc_timer = new_timer("extract QC");
	}

	if(!__qc_use_heap)
		q = slab_alloc(sizeof(struct type*)*qc_size);
	else q = malloc(sizeof(struct type*)*qc_size);

//static int hop_timer = -1;
//if(hop_timer==-1)hop_timer = new_timer("qc hop");
//start_timer(hop_timer);

IFCLOCK( start_timer(eqc_timer);)
//IFCLOCK(	clock_t	T = clock();for(iter=0;iter<100;iter++)	)
	assert(qc_extractor != NULL);
	qc_extractor(q->entries, d);
//IFCLOCK(	extract_clock += clock() - T; )
IFCLOCK(	stop_timer(eqc_timer, 1); )

//stop_timer(hop_timer, qc_size * iter);

	return q;
}

struct qc	*extract_qc_arg(struct dg	*d, int	arg)
{
	struct dg	*to;
	int		i = 0;

	if(arg>=0)
	{
		to = dg_hop(d, 0);	// 0 is guaranteed to be ARGS
		while(to && i<arg)
		{
			to = dg_hop(to, 2);	// REST
			i++;
		}
		if(to)to = dg_hop(to, 1);	// FIRST
		if(!to)
		{
			fprintf(stderr, "extract_qc_arg: couldn't get arg %d position in %s\n", arg, d->xtype->name);
			exit(-1);
		}
	}
	else to = d;

	return extract_qc(to);
}

IFCLOCK(unsigned long long glb_clock;)
IFCLOCK(unsigned long long glb_count;)

int	quickcheck(struct qc	*a, struct qc	*b)
{
	int	i, qcs = qc_size;
	struct type	**ae = a->entries, **be = b->entries;

//static int glb_timer = -1;
//if(glb_timer==-1)glb_timer =new_timer("qc-glb");
//start_timer(glb_timer);
//int J;
//for(J=0;J<10;J++)
	for(i=0;i<qcs;i++)
	{
		if(ae[i] && be[i] && (ae[i] != be[i]) &&
			!glb(ae[i], be[i]))
		{
			//printf("QC reject %d\n", i);
			break;
		}
	}
//stop_timer(glb_timer, J * ((i==qcs)?qcs:(i+1)));

	if(i<qcs)return -1;

#ifdef	HIDEOUS_HACK
	// following are relative to erg qc as of aug 12th 2013...
	struct dlist_hack { int dlist, list, last; }	hacks[1] = { {28,24,19} };
	struct olist_hack { int list, opt; }			ohacks[3] = { {26,12}, {11, 16}, {4, 47} };
	int punct_slot = 30, lpunct_slot = 31, rpunct_slot = 14;
	int					nhacks=1, nohacks=3;
//	if(a->entries[20] == olist && b->entries[9]==minus)return -1;
//	if(b->entries[20] == olist && a->entries[9]==minus)return -1;
	for(i=0;i<nhacks;i++)
	{
		struct dlist_hack	*h = hacks+i;
		if(b->entries[h->dlist]==_0dlist)
			if(a->entries[h->list] && a->entries[h->last] && !glb(a->entries[h->list], a->entries[h->last]))
				return -1;
		if(a->entries[h->dlist]==_0dlist)
			if(b->entries[h->list] && b->entries[h->last] && !glb(b->entries[h->list], b->entries[h->last]))
				return -1;
	}
	for(i=0;i<nohacks;i++)
	{
		struct olist_hack	*h = ohacks+i;
		if(a->entries[h->list] == olist && b->entries[h->opt]==minus)return -1;
		if(b->entries[h->list] == olist && a->entries[h->opt]==minus)return -1;
	}
//	if(a->entries[10] == olist && b->entries[11]==minus)return -1;
//	if(b->entries[10] == olist && a->entries[11]==minus)return -1;
	/*if(a->entries[punct_slot] == no_punctuation_min && b->entries[lpunct_slot] && !glb(b->entries[lpunct_slot], no_punct))return -1;
	if(a->entries[punct_slot] == no_punctuation_min && b->entries[rpunct_slot] && !glb(b->entries[rpunct_slot], no_punct))return -1;
	if(b->entries[punct_slot] == no_punctuation_min && a->entries[lpunct_slot] && !glb(a->entries[lpunct_slot], no_punct))return -1;
	if(b->entries[punct_slot] == no_punctuation_min && a->entries[rpunct_slot] && !glb(a->entries[rpunct_slot], no_punct))return -1;*/
#endif

	return 0;
}

/*
int	equiv_quickcheck(struct qc	*a, struct qc	*b, int *Fw, int *Bk)
{
	int	i;
	struct type	*ta, *tb, *g;
	int	fw = 1, bw = 1;

	for(i=0;i<qc_size;i++)
	{
		ta = a->entries[i];
		tb = b->entries[i];

		if(ta && tb && (ta!=tb))
		{
			g = glb(ta, tb);
			if(g!=tb)fw = 0;
			if(g!=ta)bw = 0;
		}
		if(ta && !tb)fw = 0;
		if(tb && !ta)bw = 0;
		if(!fw && !bw) { *Fw = fw; *Bk = bw; return -1; }
	}
	*Fw = fw; *Bk = bw;
	return 0;
}*/

int	equiv_quickcheck(struct qc	*a, struct qc	*b, int *Fw, int *Bk, int	*Gz)
{
	int	i;
	struct type	*ta, *tb, *g;
	int	fw = 1, bw = 1, gz = 1;

	for(i=0;i<qc_size;i++)
	{
		ta = a->entries[i];
		tb = b->entries[i];

		int	eqtypes = (ta==tb) || (ta && tb && ta->tnum==-1 && tb->tnum==-1 && !strcmp(ta->name, tb->name));
		if(ta && tb && !eqtypes)
		{
			g = glb(ta, tb);
			if(g!=tb)fw = 0;
			if(g!=ta)bw = 0;
			if(g!=ta && g!=tb)gz = 0;
		}
		if(ta && !tb)fw = 0;
		if(tb && !ta)bw = 0;
		if(!fw && !bw && !gz)
			break;
	}
	*Fw = fw; *Bk = bw;
	*Gz = gz;
	return (!fw && !bw && !gz)?1:0;
}

struct qc	*copy_qc(struct qc	*in)
{
	if(!in)return 0;
	struct qc	*out = slab_alloc(sizeof(struct type*)*qc_size);
	return memcpy(out, in, sizeof(struct type*)*qc_size);
}

struct type	*qc_type_n(struct qc	*in, int	n)
{
	if(n <0 || n >=qc_size)return NULL;
	return in->entries[n];
}

// qc generator

static struct qc_path
{
	struct path			path;
	unsigned long long	failures;
	int					rank;
}			*paths;
static int	npaths;

extern int			upathgl;
extern struct type	*uglb;

void	gqc_count_failure(struct path	path)
{
	int	i;

	for(i=0;i<npaths;i++)
		if(!pathcmp(&path, &paths[i].path))
		{
			paths[i].failures++;
			return;
		}
	npaths++;
	paths = realloc(paths, sizeof(struct qc_path)*npaths);
	paths[npaths-1].path = pathdup(path);
	paths[npaths-1].failures = 1;
}

extern unsigned long long unify_attempts_total, unify_attempts_pass_rf, unify_attempts_pass_qc, unify_attempts_success, unify_attempts_bad_orth;

//const double	k_glb = 0.0000022, k_unify = 0.0011, k_hop = 0.0000024;

/* measured feb-24 erg-1004 on 'sh.titan' */
//const double	k_glb = 1.02e-8 /*25.745 / 2533382030*/, k_unify = 6.54394e-6 /*0.00000654394*/, k_hop = 8.66e-9 /*7.078 / 817753160*/;

//const double	k_glb = 1.02e-7 /*25.745 / 2533382030*/, k_unify = 6.54394e-6 /*0.00000654394*/, k_hop = 8.66e-8 /*7.078 / 817753160*/;

/* measured jul-25-2011 erg-trunk on 'octopus' */
const double	k_glb = 0 /* not measured this time */, k_unify = 0.000005, k_hop = 0.0000016 / 45;

void	gqc_treeify(int	count, int *hops)
{
	struct qc_path	pth[count];
	int				i;

	memcpy(pth, paths, sizeof(struct qc_path)*count);
	int	lexcmp(const struct qc_path	*a, const struct qc_path	*b)
	{
		int i;
		for(i=0;i<a->path.count && i<b->path.count;i++)
			if(a->path.fnums[i] != b->path.fnums[i])
				return a->path.fnums[i] - b->path.fnums[i];
		return a->path.count - b->path.count;
	}
	qsort(pth, count, sizeof(struct qc_path), (int(*)(const void*,const void*))lexcmp);

	if(hops)
	{
		int i, hc = pth[0].path.count;
		// just count hops
		for(i=1;i<count;i++)
		{
			// find common prefix
			int j;
			for(j=0;j<pth[i].path.count && j<pth[i-1].path.count;j++)
				if(pth[i].path.fnums[j] != pth[i-1].path.fnums[j])break;
			hc += pth[i].path.count - j;
		}
		*hops = hc;
	}
	else
	{
		// actually build program
		extern char	**fnames;
		int i, hc = pth[0].path.count;
		for(i=0;i<pth[0].path.count;i++)
			printf(" PUSH(%s)", fnames[pth[0].path.fnums[i]]);
		printf(" REC(%d)", pth[0].rank);
		for(i=1;i<count;i++)
		{
			// find common prefix
			int j, k;
			for(j=0;j<pth[i].path.count && j<pth[i-1].path.count;j++)
				if(pth[i].path.fnums[j] != pth[i-1].path.fnums[j])break;
			for(k=j;k<pth[i-1].path.count;k++)printf(" POP");
			printf("\n"); for(k=0;k<j;k++)printf("    ");
			for(k=j;k<pth[i].path.count;k++)printf(" PUSH(%s)", fnames[pth[i].path.fnums[k]]);
			printf(" REC(%d)", pth[i].rank);
		}
		printf("\n");
	}
}

void	gqc_result()
{
	int i, nhops[npaths], cnh = 0, cheapest = 0;
	unsigned long long total = 0, cum = 0;
	double	filtration[npaths], least_cost;
	int	qcpcmp(const struct qc_path	*a, const struct qc_path	*b) { return b->failures - a->failures; }
	qsort(paths, npaths, sizeof(struct qc_path), (int(*)(const void*,const void*))qcpcmp);

	for(i=0;i<npaths;i++)
	{
		total += paths[i].failures;
		paths[i].rank = i;
	}

	for(i=0;i<npaths;i++)
	{
		cnh += paths[i].path.count;
		cum += paths[i].failures;

		filtration[i] = (double)cum / unify_attempts_pass_rf;//total;
		gqc_treeify(i+1, &nhops[i]);
	}

	for(i=0;i<=npaths;i++)
	{
		int j;
		double	cost, c_check = 0, c_unify, c_extract;
		for(j=0;j<i;j++)
			c_check += k_glb * unify_attempts_pass_rf * ((j>0)?(1-filtration[j-1]):1.0);
		c_unify = k_unify * unify_attempts_pass_rf * ((i>0)?(1-filtration[i-1]):1.0);
		c_extract = k_hop * ((i>0)?nhops[i-1]:0) * (unify_attempts_success - unify_attempts_bad_orth);
		cost = c_check + c_unify + c_extract;
		/*printf("%3d paths:	%10f = %10f + %10f + %10f\n", i, cost, c_check, c_unify, c_extract);
		if(i<npaths)
		{
			printf("%16lld (%.1f%%, %d hops): ", paths[i].failures, 100*filtration[i], nhops[i]);
			print_path(paths[i].path);
			printf("\n");
		}*/
		if(i==0)least_cost = cost;
		else if(cost<least_cost) { least_cost = cost; cheapest = i; }
	}

	printf("QC_SIZE(%d)\n", cheapest);
	printf("/* GQC: using %d paths, %.1f%% of failures, %d extraction hops, expected cost %f */\n",
		cheapest, 100 * (filtration[cheapest-1] / filtration[npaths-1]), nhops[cheapest-1], least_cost);
	gqc_treeify(cheapest, 0);
}

// code to take a PET quickcheck instance and build a compiled QC extractor
// we expect this instance to be a tree (no reentrancies), with number strings at the leaves
// each leaf is a QC location
// the numbers represent the rank of that path within the QC vector
// there's an artificial first feature "ARGS" that we need to jump over before starting

int	qc_count_strings(struct dg	*qc)
{
	int	i, n=0;
	qc = p_dereference_dg(qc);
	struct dg	**arcs = DARCS(qc);
	if(qc->xtype->name[0]=='"')n++;
	for(i=0;i<qc->narcs;i++)
		n += qc_count_strings(arcs[i]);
	return n;
}

void	recursive_write_qccode(struct dg	*qc, FILE	*f, int	count)
{
	qc = p_dereference_dg(qc);
	if(qc->xtype->name[0]=='"')
	{
		int	k = atoi(qc->xtype->name+1);
		if(k >= count)
		{
			fprintf(stderr, "quickcheck instance compiler: find path %d but only thought there were %d paths\n", k, count);
			exit(-1);
		}
		fprintf(f, "REC(%d)\n", k);
	}
	int i;
	struct dg	**arcs = DARCS(qc);
	for(i=0;i<qc->narcs;i++)
	{
		extern char	**fnames;
		fprintf(f, "PUSH(%s) ", fnames[qc->label[i]]);
		recursive_write_qccode(arcs[i], f, count);
		fprintf(f, "POP ");
	}
}

void	write_qccode_from_pet_instance(struct dg	*petqc, FILE	*f)
{
	struct dg	*mainqc = dg_hop(petqc, lookup_fname("ARGS"));
	assert(mainqc != NULL || !"Quickcheck instance had no ARGS feature");
	int	n = qc_count_strings(mainqc);
	fprintf(f, "QC_SIZE(%d)\n", n);
	recursive_write_qccode(mainqc, f, n);
}
