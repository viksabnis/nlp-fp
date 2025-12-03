#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>

#include	"hash.h"
#include	"type.h"
#include	"dag.h"

#include	"bitvec.h"

int		glb_type_count;

int	glb_noisy = 0;

int	shortcomp(const void	*a, const void	*b) { return *(unsigned short*)a - *(unsigned short*)b; }

#define	BITVEC_GLB		1
#define	ORIGINAL_GLB	0

#if ORIGINAL_GLB

#define	CSTSIZE	(16384*8-1)
//static char	csthashres[CSTSIZE];
static struct type	*csthasha[CSTSIZE];
static struct type	*csthashb[CSTSIZE];
int					ncsthash_collisions = 0, ncsthash_requests = 0;

int	find_common_subtypes(struct type	*a, struct type	*b, unsigned short	*_glb_common)
{
	int	_glb_ncommon = 0, ia, ib, and, bnd;
	unsigned short *ad, *bd;
	unsigned long	h = (((unsigned long)a<<5) ^ ((unsigned long)b>>5)) % (CSTSIZE);

	ncsthash_requests++;
	for(ia=0;ia<4;ia++)
		if(csthasha[(h+17*ia)%CSTSIZE]==a && csthashb[(h+17*ia)%CSTSIZE]==b)return 0;// && !csthashres[h])return 0;

	ia = ib = 0;
	and = a->ndescendents;
	bnd = b->ndescendents;
	ad = a->descendents;
	bd = b->descendents;
	while(ia < and && ib < bnd)
	{
		if(*ad == *bd)
		{
			//if(ia==0 || ib==0)return -1;	// one type is a descendent of the other
			if((_glb_ncommon+1) >= 10000)
			{
				fprintf(stderr, "too many common types for our buffer!\n");
				exit(-1);
			}
			_glb_common[_glb_ncommon++] = *ad;
			ia++;ad++;
			ib++;bd++;
		}
		else if(*ad < *bd){ia++;ad++;}
		else {ib++;bd++;}
	}

	// try to find a free hash slot
	for(ia=0;ia<4;ia++)
		if(!csthasha[(h+17*ia)%CSTSIZE])break;
	if(ia==4)ia=0;
	h = (h+17*ia)%CSTSIZE;
	if(csthasha[h])ncsthash_collisions++;
	csthasha[h] = a;
	csthashb[h] = b;
	//csthashres[h] = _glb_ncommon?1:0;
	return _glb_ncommon;
}

static struct glb_fix
{
	struct type	*para, *parb, *glb;
}		*fixes;
static int	nfixes;

int	constrain_glb_type(struct type	*g)
{
	int		i;
	struct glb_fix	*f;

	if(g->dg)return 0;
	for(i=0;i<nfixes;i++)
		if(fixes[i].glb==g)break;
	if(i>=nfixes)
	{
		fprintf(stderr, "glb-fix: no glb type `%p' (%s) was recorded\n", g, g->name);
		exit(-1);
	}
	f = fixes+i;

	if(!f->para->dg)constrain_glb_type(f->para);
	if(!f->parb->dg)constrain_glb_type(f->parb);
	g->dg = unify_dg(f->para->dg, f->parb->dg, -1);
	if(!g->dg)
	{
		fprintf(stderr, "glb-fix: unexpected error! glb type `%s' is inconsistent.\n", g->name);
#ifdef	UNIFY_PATHS
		unify_backtrace();
#endif
		exit(-1);
	}
	return 0;
}

void	fix_glbs()
{
	int	i;

	for(i=0;i<nfixes;i++)
		constrain_glb_type(fixes[i].glb);
	nfixes = 0;
	if(fixes)free(fixes);
}

int	check_for_glb(struct type	*a, struct type	*b)
{
	unsigned short	_glb_common[10000];
	int				_glb_ncommon;
	int	ia, i, j, mi, resort, resort_key=-1;
	struct type	*ar[2] = {a, b};
	char	name[1024];
	struct type	*g;

	_glb_ncommon = find_common_subtypes(a, b, _glb_common);
	//if(_glb_ncommon==-1)return 0;	// one type is a descendent of the other

	if(_glb_ncommon==0)return 0;	// no types in common, no glb
	if(_glb_ncommon==1)return 0;	// one type in common, it must be the glb

	// check first common descendent to see if it's the glb
	g = types[_glb_common[0]];
	if(g->ndescendents == _glb_ncommon)
	{
		return 0;	// this is the glb. don't need to check that the descendents match.
		//for(j=0;j<_glb_ncommon;j++)
		//	if(g->descendents[j] != _glb_common[j])
		//		break;
		//if(j==_glb_ncommon)return 0;	// this is the glb
		//assert(!"not reached");
	}

	// no glb existed; make one!
	sprintf(name, "g(%s,%s)", a->name, b->name);
	add_type_only(name, 2, ar, 0);
	//printf("add `%s'\n", name);

	_glb_common[_glb_ncommon++] = ntypes-1;	// a,b have a new common descendent

	g = types[ntypes-1];
	g->ndescendents = _glb_ncommon;
	g->descendents = realloc(g->descendents, sizeof(short)*_glb_ncommon);
	memcpy(g->descendents, _glb_common, sizeof(short)*_glb_ncommon);

	// fix up the ->parents[] arrays of all the descendents
	for(i=0;i<g->ndescendents-1;i++)
	{
		struct type	*d = types[g->descendents[i]];
		// delete appearances of 'a' and 'b' from d->parents[].
		// if no parents are descendents of 'g', add 'g' as a parent.
		int j, have_g = 0;
		for(j=0;j<d->nparents;j++)
			if(descendent_of(d->parents[j]->tnum, g))have_g = 1;
		for(j=0;j<d->nparents;j++)
		{
			if(d->parents[j] == a || d->parents[j] == b)
			{
				if(!have_g)
				{
					d->parents[j] = g;
					have_g = 1;
				}
				else
				{
					// delete d->parents[j]
					d->nparents--;
					memmove(d->parents+j, d->parents+j+1, sizeof(struct type*)*(d->nparents - j));
					j--;
				}
			}
		}
		if(!have_g)
		{
			d->nparents++;
			d->parents = realloc(d->parents, sizeof(struct type*) * d->nparents);
			d->parents[d->nparents-1] = g;
		}
	}

	nfixes++;
	fixes = realloc(fixes, sizeof(struct glb_fix)*nfixes);
	fixes[nfixes-1].glb = g;
	fixes[nfixes-1].para = a;
	fixes[nfixes-1].parb = b;

	// compute where to put the new type wrt the partial order 'descendent_of'
	mi=0;
	for(i=0;i<ntypes-1;i++)
		if(descendent_of(ntypes-1, types[i]))mi = i;
	mi++;

	//printf("  *** goes at %d / %d\n", mi, ntypes-1);
	//printf("  after which: ");
	//for(i=mi;i<ntypes-1;i++)printf("%s ", types[i]->name);
	//printf("\n");

	if(mi != ntypes-1)
	{
		g = types[ntypes-1];
		memmove(types+mi+1, types+mi, sizeof(struct type*)*(ntypes-1-mi));
		types[mi] = g;
		g->tnum = mi;
		// relocate 'descendents' of everybody who pointed at someone who got moved
		for(i=0;i<ntypes;i++)
		{
			unsigned short ndesc, ntm1, *desc;
			g = types[i];
			if(i>mi)g->tnum++;
			resort = 0;
			desc = g->descendents;
			ndesc = g->ndescendents;
			ntm1 = ntypes-1;
			for(ia=0;ia<ndesc;ia++,desc++)
			{
				if(*desc==ntm1){resort=1;resort_key = ia;*desc=mi;}
				else if(*desc>=mi)(*desc)++;
			}
			if(resort && g->ndescendents>1)
			{
				// item "resort_key" is in the wrong place; fix it!
				if(resort_key != g->ndescendents-1)
				{
					fprintf(stderr, "WRONG: resort_key = %d / %d\n", resort_key, g->ndescendents);
					qsort(g->descendents, g->ndescendents, sizeof(short), shortcomp);
				}
				else
				{
					// find out where 'mi' belongs and put it there
					for(ia=0;ia<g->ndescendents-1;ia++)
						if(mi < g->descendents[ia])break;
					memmove(g->descendents+ia+1, g->descendents+ia, sizeof(short)*(g->ndescendents-1-ia));
					g->descendents[ia] = mi;
				}
			}
		}
	}
	glb_type_count++;
	return 1;
}

// old fashioned version
int make_glbs()
{
	int	i, j;
	// don't do 0; finding glb's of *top* with things is a big waste of time!
	for(i=ntypes-1;i>0;i--)
	{
		more:
		if(types[i]->ndescendents == 1)continue;
		for(j=ntypes-1;j>i;j--)
		{
			if(types[j]->ndescendents == 1)continue;
			if(check_for_glb(types[i], types[j]))
			{
				// check the newly created type against everything
				//i = ntypes-1;
				i++;
				//printf(" +%d\n", ntypes);
				goto more;
			}
		}
	}
	rebuild_hierarchy();// to make sure daughters[] and parents[] lists are OK
	//printf("%d cst hash collisions / %d R  ", ncsthash_collisions, ncsthash_requests);
	return 0;
}

#endif	// ORIGINAL_GLB

#if BITVEC_GLB

// new-fangled version
int	fix_glbs()
{
	struct type_hierarchy	*th = default_type_hierarchy();
	int	i, j;
	for(i=0;i<th->ntypes;i++)
	{
		struct type	*t = th->types[i];
		if(t->dg)continue;
		//printf("fixing up %s\n", t->name);
		struct dg	*d = t->parents[0]->dg;
		assert(d != NULL);
		assert(t->nparents > 1);
		for(j=1;j<t->nparents;j++)
		{
			struct dg	*d2 = unify_dg_noss(d, t->parents[j]->dg, -1);
			if(!d2)
			{
				fprintf(stderr, "glb-fix: unexpected error! glb type `%s' is inconsistent.\n", t->name);
		#ifdef	UNIFY_PATHS
				unify_backtrace();
		#endif
				fprintf(stderr, " parents: ");
				for(i=0;i<t->nparents;i++)
				{
					fprintf(stderr, " %s[%c]", t->parents[i]->name, (i==j)?'X':' ');
					output_lui_dg(t->parents[i]->dg, t->parents[i]->name);
				}
				fprintf(stderr, "\n");
				wait_for_lui();
				exit(-1);
			}
			d = d2;
		}
		t->dg = d;
	}
	return 0;
}


struct partition
{
	int	psize;
	struct type	**part;
}	*parts;
int	nparts;

int	npartitions = 0;
int	biggest_partition = 0;

print_subhierarchy(struct type_hierarchy	*th, struct partition	*part)
{
	int	i, j, k;
	for(i=0;i<part->psize;i++)
	{
		struct type	*T = part->part[i];
		printf("type %3d = %s ... descendents are:\n", T->tnum, T->name);
		for(j=1;j<T->ndescendents;j++)
		{
			struct type	*d = th->types[T->descendents[j]];
			for(k=0;k<part->psize;k++)
				if(part->part[k] == d)break;
			if(k<=part->psize)
				printf(" %3d = %s\n", T->descendents[j], d->name);
		}
		printf("\n");
	}
}

// partition algorithm from the LKB [AAC-1998 apparently]
// we're trying to split the type hierarchy up into as many little chunks as possible
void	compute_partitions(struct type_hierarchy	*th, struct type	*top, char	*visitmap, char	*collectmap)
{
	// first see if we can split off some partitions among this node's daughters
	int	i, j;
	if(collectmap[top->tnum])return;
	if(visitmap[top->tnum])return;
	visitmap[top->tnum] = 1;
	if(!top->ndaughters)return;
	for(i=0;i<top->ndaughters;i++)
		compute_partitions(th, top->daughters[i], visitmap, collectmap);

	// my descendents can be a partition if every descendent satisfies at least one of these criteria:
	// 1. it's already been put in a partition, so I don't have to worry about it
	// 2. its immediate parents are a subset of my descendents
	// 3. it only has a single immediate parent (special case of 2)

	int	psize = 0;
	for(i=0;i<top->ndescendents;i++)
	{
		struct type	*d = th->types[top->descendents[i]];
		if(collectmap[d->tnum])continue;
		psize++;
		if(d->nparents == 1)continue;
		for(j=0;j<d->nparents;j++)
		{
			if(!descendent_of(d->parents[j]->tnum, top))
				break;
		}
		if(j < d->nparents)
		{
			// this node has a parent that is not a descendent of our local top.
			// that means we can't have a partition dominated by this top.
			//printf("%s can't dominate a partition because %s has an outside parent\n", top->name, d->name);
			return;
		}
	}

	// make a partition dominated by this node,
	// it should contain all this node's descendents that haven't been seen,
	// and we should mark them all as seen.
	struct type	**part = calloc(sizeof(struct type*), psize);
	psize = 0;
	for(i=0;i<top->ndescendents;i++)
	{
		struct type	*d = th->types[top->descendents[i]];
		if(collectmap[d->tnum])continue;
		if(d->nparents==1 && d->ndaughters==0)continue;	// skip single-parent leaves, as they cannot give rise to GLBs
		part[psize++] = d;
		collectmap[d->tnum] = 1;
	}
	npartitions++;
	if(psize > biggest_partition)biggest_partition = psize;

	nparts++;
	parts = realloc(parts, sizeof(struct partition) * nparts);
	parts[nparts-1].psize = psize;
	parts[nparts-1].part = part;
	//printf("%s dominates a partition of %d\n", top->name, psize);
}

void	count_nonleaf_nodes(struct type_hierarchy	*th)
{
	int	i, n=0;
	for(i=0;i<th->ntypes;i++)
		if(th->types[i]->ndescendents > 1)n++;
	printf("%d non-leaf types\n", n);
}

static struct profiler	*code_profiler, *insert_profiler, *partition_profiler, *rebuild_profiler;

int	make_glbs()
{
	int	i, j;

	struct type_hierarchy	*th = default_type_hierarchy();

	start_and_alloc_profiler(&partition_profiler, "partitioning the hierarchy", NULL, NULL);
	char	*vmap = calloc(1, th->ntypes), *cmap = calloc(1, th->ntypes);
	parts = NULL;
	nparts = 0;
	npartitions = 0;
	biggest_partition = 0;
	compute_partitions(th, th->top, vmap, cmap);
	//printf("%d partitions ; biggest was %d types\n", npartitions, biggest_partition);
	free(vmap); free(cmap);
	stop_profiler(partition_profiler, 1);

	for(i=0;i<nparts;i++)
	{
		//printf("partition of %d types\n", parts[i].psize);
		make_glbs_part(th, parts+i);
		free(parts[i].part);
	}
	free(parts);

	start_and_alloc_profiler(&rebuild_profiler, "rebuilding the hierarchy", NULL, NULL);
	rebuild_hierarchy(0, th);
	stop_profiler(rebuild_profiler, 1);

	if(glb_noisy)
	{
		report_profiler(partition_profiler);
		report_profiler(code_profiler);
		report_profiler(insert_profiler);
		report_profiler(rebuild_profiler);
	}

	return 0;
}

struct code_record
{
	struct type	*t;	// authored type
	unsigned long long	*code;
};

struct hash	*bchash;
int	nglbtypes;
struct code_record	**glbtypes;

long long cp_zeros = 0, cp_nonzeros = 0;

void	check_pair(unsigned long long	*x, unsigned long long	*y, unsigned long long	*result, int	bcsize)
{
	int	nonzero = bitvec_and_ss(x, y, result, bcsize);
	if(!nonzero)
	{
		cp_zeros++;
		return;
	}
	cp_nonzeros++;
	// glb(a,b) = result
	// see if we can find it.
	if(!memcmp(x, result, bcsize*sizeof(unsigned long long)))return;
	if(!memcmp(y, result, bcsize*sizeof(unsigned long long)))return;
	struct code_record	*cr = hash_find(bchash, (char*)result);
	if(!cr)
	{
		//printf("glb(%s,%s) doesn't exist\n", part->part[i]->name, part->part[j]->name);
		cr = malloc(sizeof(*cr));
		cr->t = NULL;
		cr->code = malloc(sizeof(unsigned long long)*bcsize);
		memcpy(cr->code, result, sizeof(unsigned long long)*bcsize);
		hash_add(bchash, (char*)cr->code, cr);
		nglbtypes++;
		glbtypes = realloc(glbtypes, sizeof(struct code_record*)*nglbtypes);
		glbtypes[nglbtypes-1] = cr;
	}
	else
	{
		//printf("glb(%s,%s) = %s\n", part->part[i]->name, part->part[j]->name, part->part[tn]->name);
	}
}

struct type	*new_glb_type()
{
	char	name[1024];
	static int glbtypecounter;
	sprintf(name, "g(%d)", glbtypecounter++);
	add_type_only(name, -1, NULL, 0);
	glb_type_count++;
	struct type_hierarchy	*th = default_type_hierarchy();
	return th->types[th->ntypes-1];
}

static struct profiler	*ancestor_profiler, *decendant_profiler, *lineage_profiler;

// same algorithm as LKB function of similar name
insert_glb_type(struct partition	*part, unsigned long long	**vectors, struct code_record	*cr, int	bcsize)
{
	int	i;
	int	nanc = 0;
	struct code_record	*anc = NULL;

	// building a set of immediate parents
	// no need to add an ancestor that subsumes another already-present ancestor
	// if we find a parent that is subsumed by several existing parents,
	// replace one and delete the rest.
	void add_anc(struct type	*t, unsigned long long	*v)
	{
		int	i, is_in = 0;
		int	di = -1;
		//printf("add_anc %s\n", t->name);
		for(i=0;i<nanc;i++)
		{
			struct type	*at = anc[i].t;
			unsigned long long	*av = anc[i].code;
			if(!at){di = i;continue;}	// deleted ancestor
			if(at == t)return;
			if(bitvec_subsume(v, av, bcsize))return;
			if(bitvec_subsume(av, v, bcsize))
			{
				// type we're trying to add is subsumed by current ancestor type
				if(!is_in)
				{
					anc[i].t = t;
					anc[i].code = v;
					is_in = 1;
				}
				else
				{
					anc[i].t = NULL;
					anc[i].code = NULL;
				}
			}
		}
		if(!is_in)
		{
			if(di != -1)
			{
				anc[di].t = t;
				anc[di].code = v;
			}
			else
			{
				nanc++;
				anc = realloc(anc, sizeof(struct code_record)*nanc);
				anc[nanc-1].t = t;
				anc[nanc-1].code = v;
			}
		}
	}

	start_and_alloc_profiler(&ancestor_profiler, "GLB ancestors", insert_profiler, NULL);
	// see what authored types subsume 'cr'
	for(i=0;i<part->psize;i++)
	{
		unsigned long long	*v = vectors[i];
		if(bitvec_subsume(v, cr->code, bcsize))add_anc(part->part[i], v);
	}
	// see what new glb types subsume 'cr'
	for(i=0;i<nglbtypes;i++)
	{
		unsigned long long	*v = glbtypes[i]->code;
		if(glbtypes[i] == cr)continue;
		if(bitvec_subsume(v, cr->code, bcsize))add_anc(glbtypes[i]->t, v);
	}

	// collapse deleted slots
	int j;
	for(i=j=0;i<nanc;i++)
		if(anc[i].t)anc[j++] = anc[i];
	nanc = j;
	stop_profiler(ancestor_profiler, nanc);

	// we now have a set of immediate parent types for this glb type
	//printf("%s with parents: ", cr->t->name);
	//for(i=0;i<nanc;i++)printf(" %s", anc[i].t->name);
	//printf("\n");

	start_and_alloc_profiler(&lineage_profiler, "GLB lineage", insert_profiler, NULL);

	struct type	**par = malloc(sizeof(struct type*)*nanc);
	for(i=0;i<nanc;i++)par[i] = anc[i].t;
	setup_type_lineage(cr->t, nanc, par);

	stop_profiler(lineage_profiler, 1);


	// next, figure out this glb type's immediate daughters so we can
	// add it to their ->parents[] arrays
	int	ndec = 0, adec = 0, add_dec_calls = 0;
	struct code_record	*dec = NULL;

	int do_print = 0;

	// building a set of immediate daughters
	// no need to add a descendent that is subsumed by another already-present daughter
	// if we find a descendent that subsumes several existing daughters,
	// replace one and delete the rest.
	void add_dec(struct type	*t, unsigned long long	*v)
	{
		int	i, is_in = 0;
		int	di = -1;
		if(do_print)printf("add_dec %s\n", t->name);
		add_dec_calls++;
		for(i=0;i<ndec;i++)
		{
			struct type	*dt = dec[i].t;
			unsigned long long	*dv = dec[i].code;
			if(!dt){di = i;continue;}	// deleted slot
			if(dt == t)return;
			if(bitvec_subsume(dv, v, bcsize))return;
			if(bitvec_subsume(v, dv, bcsize))
			{
				// type we're trying to add subsumes current daughter type
				if(!is_in)
				{
					dec[i].t = t;
					dec[i].code = v;
					is_in = 1;
				}
				else
				{
					dec[i].t = NULL;
					dec[i].code = NULL;
				}
			}
		}
		if(!is_in)
		{
			if(di != -1)
			{
				dec[di].t = t;
				dec[di].code = v;
			}
			else
			{
				ndec++;
				if(ndec>adec)
				{
					adec = ndec*2;
					dec = realloc(dec, sizeof(struct code_record)*adec);
				}
				dec[ndec-1].t = t;
				dec[ndec-1].code = v;
			}
		}
	}

	start_and_alloc_profiler(&decendant_profiler, "GLB decendants", insert_profiler, NULL);

	// see what authored types 'cr' subsumes
	for(i=0;i<part->psize;i++)
	{
		unsigned long long	*v = vectors[i];
		//int	subsumed = bitvec_subsume(cr->code, v, bcsize)?1:0;
		int	subsumed2 = bitvec_test(cr->code, i)?1:0;
		//assert(subsumed == subsumed2);
		if(subsumed2)add_dec(part->part[i], v);
	}
	// see what new glb types 'cr' subsumes
	for(i=0;i<nglbtypes;i++)
	{
		unsigned long long	*v = glbtypes[i]->code;
		if(glbtypes[i] == cr)continue;
		if(bitvec_subsume(cr->code, v, bcsize))add_dec(glbtypes[i]->t, v);
	}

	if(do_print)
	{
		for(i=0;i<part->psize;i++)
			if(bitvec_test(cr->code, i))
			{
				printf("should subsume '%s'\n", part->part[i]->name);
				printf("bvss = %d\n", bitvec_subsume(cr->code, vectors[i], bcsize));
				for(j=0;j<part->psize;j++)
					printf("c=%d ; v=%d ; %s\n", bitvec_test(cr->code, j), bitvec_test(vectors[i], j), part->part[j]->name);
			}
	}

	// collapse deleted slots
	for(i=j=0;i<ndec;i++)
		if(dec[i].t)dec[j++] = dec[i];
	ndec = j;
	//printf("%16s	%d decendents (%d add_dec calls)\n", cr->t->name, ndec, add_dec_calls);

	// we now have a set of immediate daughter types for this glb type
	if(do_print)
	{
		printf("%s with daughters: ", cr->t->name);
		for(i=0;i<ndec;i++)printf(" %s", dec[i].t->name);
		printf("\n");
	}
	for(i=0;i<ndec;i++)
	{
		// add this glb type to this daughter's parents[] list
		struct type	*d = dec[i].t;
		d->nparents++;
		d->parents = realloc(d->parents, sizeof(struct type*) * d->nparents);
		d->parents[d->nparents-1] = cr->t;
	}

	free(dec);

	stop_profiler(decendant_profiler, ndec);
}

sanity_check_1_bitvector(struct partition	*part, struct type	*t, unsigned long long	*vector)
{
	int	j;
	for(j=0;j<part->psize;j++)
	{
		if(bitvec_test(vector, j) != descendent_of(part->part[j]->tnum, t))
		{
			printf("sanity check error:\n");
			printf("bit for '%s' of vector for '%s' = %d\n", part->part[j]->name, t->name, bitvec_test(vector, j));
			printf("descendent_of = %d\n", descendent_of(part->part[j]->tnum, t));
			exit(-1);
		}
	}
}

sanity_check_bitvectors(struct partition	*part, unsigned long long	**vectors)
{
	int	i, j;
	for(i=0;i<part->psize;i++)
		sanity_check_1_bitvector(part, part->part[i], vectors[i]);
}

int make_glbs_part(struct type_hierarchy	*th, struct partition	*part)
{
	//if(part->psize > 30000)part->psize = 30000;
	start_and_alloc_profiler(&code_profiler, "bitcode creation and finding new glbs", NULL, NULL);
	int		bcsize = bitvec_n(part->psize);
	unsigned long long	**vectors = calloc(sizeof(unsigned long long*), part->psize);
	int		i, j, k;
	int		nnonleaves = 0;
	struct hash	*ptnumhash = hash_new("ptnum");
	bchash = hash_new("bc");
	bchash->has_flk = bcsize * sizeof(unsigned long long);
	extern long long hash_collisions;
	hash_collisions = 0;
	char	key[32];
	for(i=0;i<part->psize;i++)
	{
		sprintf(key, "%d", part->part[i]->tnum);
		hash_add(ptnumhash, strdup(key), (void*)(unsigned long long)(i+1));
	}
	for(i=0;i<part->psize;i++)
	{
		struct type	*t = part->part[i];
		vectors[i] = calloc(sizeof(unsigned long long), bcsize);
	}
	for(i=0;i<part->psize;i++)
	{
		struct type	*t = part->part[i];
		if(t->ndaughters)nnonleaves++;
		for(j=0;j<t->ndescendents;j++)
		{
			sprintf(key, "%d", t->descendents[j]);
			int	tn = ((signed int)(unsigned long long)hash_find(ptnumhash, key))-1;
			if(tn == -1)
			{
				// this descendent is not in this partition.
				continue;
			}
			assert(tn >= 0 && tn < part->psize);
			// in theory: part->part[tn] is types[t->descendents[j]]
			assert(part->part[tn] == th->types[t->descendents[j]]);
			bitvec_set(vectors[i], tn);
		}
		struct code_record *cr = malloc(sizeof(*cr));
		cr->t = part->part[i];
		cr->code = vectors[i];
		hash_add(bchash, (char*)cr->code, cr);
	}

	hash_free(ptnumhash);
	//printf("after encoding, hash_collisions = %lld\n", hash_collisions);
	hash_collisions = 0;

	unsigned long long	*result = calloc(sizeof(unsigned long long), bcsize);
	nglbtypes = 0;
	glbtypes = NULL;

	//print_subhierarchy(th, part);
	if(glb_noisy && part->psize > 1000)printf("glb-ifying a partition of %d types\n", part->psize);

	cp_zeros = cp_nonzeros = 0;

	long long	steps = ((long long)nnonleaves) * nnonleaves / 2, step = 0;

	for(i=0;i<part->psize;i++)
	{
		if(!part->part[i]->ndaughters)continue;
		for(j=0;j<i;j++)
		{
			if(!part->part[j]->ndaughters)continue;
			step++;
			if(glb_noisy && part->psize > 1000 && (step%1000000)==0)
			{
				printf("\r[ %lld / %lld ] ...  ", step / 1000000, steps / 1000000);
				fflush(stdout);
			}
			check_pair(vectors[i], vectors[j], result, bcsize);
		}
	}
	if(glb_noisy && part->psize > 1000)printf(" ... found %d new glbs, continuing (%lld zeros, %lld nonzeros)\n", nglbtypes, cp_zeros, cp_nonzeros);

	cp_zeros = cp_nonzeros = 0;
	int	firstnewglbtype = 0, lastnewglbtype = nglbtypes;
	do
	{
		steps = (lastnewglbtype-firstnewglbtype) * ((lastnewglbtype-firstnewglbtype)/2/* + part->psize*/);
		step = 0;
		for(i=firstnewglbtype;i<lastnewglbtype;i++)
		{
			/*for(j=0;j<part->psize;j++)
			{
				check_pair(glbtypes[i]->code, vectors[j], result, bcsize);
				step++;
				if((step%10000)==0)
				{
					steps = nglbtypes * (nglbtypes/2 + part->psize);
					printf("\r[ %lld / %lld ] ...  ", step / 10000, steps / 10000);
					fflush(stdout);
				}
			}*/
			for(j=firstnewglbtype;j<i;j++)
			{
				check_pair(glbtypes[i]->code, glbtypes[j]->code, result, bcsize);
				step++;
				if(glb_noisy && part->psize > 1000 && (step%10000)==0)
				{
					printf("\r[ %lld / %lld ] ...  ", step / 10000, steps / 10000);
					fflush(stdout);
				}
			}
		}
		if(glb_noisy && part->psize > 1000)printf(" ... now %d new glb types; %d new this iteration (%lld zeros, %lld nonzeros)\n", nglbtypes, nglbtypes - lastnewglbtype, cp_zeros, cp_nonzeros);
		firstnewglbtype = lastnewglbtype;
		lastnewglbtype = nglbtypes;
	} while(firstnewglbtype < lastnewglbtype);

	//printf("%lld more collisions from adding glb types\n", hash_collisions);

	start_and_alloc_profiler(&insert_profiler, "building the new glb types", NULL, code_profiler);
	if(nglbtypes)
	{
		//printf("discovered %d new GLB types that we need.\n", nglbtypes);
		for(i=0;i<nglbtypes;i++)
			glbtypes[i]->t = new_glb_type();
		steps = nglbtypes;
		step = 0;
		for(i=0;i<nglbtypes;i++)
		{
			step++;
			if(glb_noisy && part->psize > 1000 && (step%100)==0)
			{
				printf("\r[ %lld / %lld ] ...  ", step, steps);
				fflush(stdout);
			}
			insert_glb_type(part, vectors, glbtypes[i], bcsize);
		}
	}
	stop_profiler(insert_profiler, nglbtypes);

	hash_free(bchash);	// also frees vectors[] contents
	free(vectors);
	free(glbtypes);
	//if(part->psize >= 30000)exit(0);
}
#endif	// BITVEC_GLB

#if 0
// set based version
int make_glbs_part(struct partition	*part)//int	part_ntypes, struct type	**part_types)
{
	int	i, j;
	int	do_printing = (part->psize==1196)?1:0;
	again:
	printf("looking for glbs in hierarchy of %d types\n", part->psize);
	//if(do_printing)print_subhierarchy(part);
	for(i=1;i<part->psize;i++)
	{
		struct type	*a = part->part[i];
		if(a->ndescendents == 1)continue;
		for(j=i+1;j<part->psize;j++)
		{
			struct type	*b = part->part[j];
			if(b->ndescendents == 1)continue;
			// compute the GLB
			unsigned short	_glb_common[10000];
			int				_glb_ncommon;

			_glb_ncommon = find_common_subtypes(a, b, _glb_common);
			//if(_glb_ncommon==-1)return 0;	// one type is a descendent of the other
			if(_glb_ncommon==0)continue;	// no types in common, no glb
			if(_glb_ncommon==1)continue;	// one type in common, it must be the glb

			// check first common descendent to see if it's the glb
			struct type	*g = types[_glb_common[0]];
			if(g->ndescendents == _glb_ncommon)
				continue;

			// nope. there's at least one type in _glb_common that's not a descendent of g.
			struct type	*glb_set[10000] = {g};
			int			nglb_set = 1;
			int			k, l;
			for(k=1;k<_glb_ncommon;k++)
			{
				for(l=0;l<nglb_set;l++)
					if(descendent_of(_glb_common[k], glb_set[l]))
						break;
				if(l<nglb_set)continue;
				glb_set[nglb_set++] = types[_glb_common[k]];
			}

			// we've got a set representing all the possible immediate lower bounds.
			record_glb_to_add(glb_set, nglb_set, a, b);
		}
	}

	printf("need to add %d GLBs\n", nglbs_to_add);
	// go about adding the new types, disregarding the
	// convention that the type array be sorted
	for(i=0;i<nglbs_to_add;i++)
	{
		struct glb_to_add	*A = glbs_to_add[i];
		if(do_printing)
		{
			printf("discovered a new missing GLB type.\n");
			printf("  OR: ");for(j=0;j<A->nset;j++)printf(" %s", A->set[j]->name);
			printf("\n");
			printf("  AND: ");for(j=0;j<A->npar;j++)printf(" %s", A->par[j]->name);
			printf("\n");
		}

		char	name[1024];
		static int nglbtypes = 0;
		sprintf(name, "glbtype%d", ++nglbtypes);
		add_type_only(name, A->npar, A->par);
		struct type	*g = types[ntypes-1];

		// add 'g' to 'part' so we see it when we iterate
		// note: I don't think we care about keeping 'part' in sorted order
//		part->psize++;
//		part->part = realloc(part->part, sizeof(struct type*)*part->psize);
//		part->part[part->psize-1] = g;

		// record what types 'g' is a descendent of
		int	k;
		for(j=0;j<ntypes;j++)
		{
			for(k=0;k<A->npar;k++)
				if(A->par[k] != types[j] && descendent_of(A->par[k]->tnum, types[j]))
				{
					add_descendent(types[j], g->tnum);
					break;	// no need to add it twice
				}
		}

		// record what types are descendents of 'g'
		for(j=0;j<A->nset;j++)
		{
			struct type	*gs = A->set[j];
			add_descendent(g, gs->tnum);
			for(k=0;k<gs->ndescendents;k++)
				add_descendent(g, gs->descendents[k]);
		}
	}
	if(nglbs_to_add)
	{
		// now we need to recompute everybody's descendents list and tnum
		printf("rebuilding type hierarchy\n");
		recompute_tnums();
		nglbs_to_add = 0;
		goto again;
	}
	nglbs_to_add = 0;

	return 0;
}
#endif	// SET_GLB
