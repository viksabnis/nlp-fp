#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<signal.h>
#include	<time.h>

#include	"dag.h"
#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"lexical-parse.h"
#include	"lattice-mapping.h"
#include	"timer.h"

#include	"profiler.h"

struct qcaddr
{
	signed dtr:6;
	unsigned slot:10;
};

struct qcformula
{
	int	naddrs;
	struct qcaddr	*addrs;
	struct type		*base;
};

struct qcrule
{
	struct rule	*rule;
	struct qcformula	**daughters;
	struct qcformula	*mother;
}	**qcrules;

int	marker;
extern int qc_size;

void	mark_dg_nodes(struct dg	*d)
{
	long	mark = (long)d->type;
	if(mark > 0 && mark < marker)return;
	d->xtype = d->type = (struct type*)(long)marker++;
	struct dg	**a = DARCS(d);
	int i;
	for(i=0;i<d->narcs;i++)mark_dg_nodes(a[i]);
}

struct qcrule	*prepare_qc_rule(struct rule	*R)
{
	struct qcrule	*r = calloc(sizeof(*r),1);
	int i, j;
	r->rule = R;
	struct dg	*d = copy_dg(R->dg);
	struct qc	*mqc_base = extract_qc(d);
	struct qc	*dqc_base[R->ndaughters];
	for(i=0;i<R->ndaughters;i++)dqc_base[i] = extract_qc_arg(d, i);
	marker = 1;
	mark_dg_nodes(d);
	struct qc	*mqc = extract_qc(d);
	struct qc	*dqc[R->ndaughters];
	for(i=0;i<R->ndaughters;i++)dqc[i] = extract_qc_arg(d, i);

	int				*naddrs = calloc(sizeof(int), marker);
	struct qcaddr	**addrs = calloc(sizeof(struct qcaddr*), marker);
	void record_mark(int mark, int d, int s)
	{
		assert(mark > 0 && mark < marker);
		naddrs[mark]++;
		addrs[mark] = realloc(addrs[mark], sizeof(struct qcaddr)*naddrs[mark]);
		addrs[mark][naddrs[mark]-1].dtr = d;
		addrs[mark][naddrs[mark]-1].slot = s;
	}
	for(i=0;i<qc_size;i++)
	{
		struct type	*T = qc_type_n(mqc, i);
		if(T)
		{
			int	mark = (int)(long)T;
			record_mark(mark, -1, i);
		}
		for(j=0;j<R->ndaughters;j++)
		{
			struct type	*T = qc_type_n(dqc[j], i);
			if(T)
			{
				int mark = (int)(long)T;
				record_mark(mark, j, i);
			}
		}
	}

	struct qcformula	*extract_formula(struct qc	*q, struct qc	*qbase, int	except)
	{
		int k, l;
		struct qcformula	*F = calloc(sizeof(struct qcformula), qc_size);
		for(k=0;k<qc_size;k++)
		{
			struct type	*T = qc_type_n(q, k);
			if(!T)
			{
				// this slot is *missing*; if there is a slot [z] whose paths *contain* [k]
				// and whose values are copied from [z] in another portion of the rule,
				// then [k] can be inferred to be copied too.
				int z;
				for(z=k-1;z>=0;z--)
					if(qc_contains(z, k))
					{
						T = qc_type_n(q, z);
						if(!T)continue;
						int	mark = (int)(long)T;
						for(l=0;l<naddrs[mark];l++)
							if(addrs[mark][l].dtr != except && addrs[mark][l].dtr != -1 && addrs[mark][l].slot == z)
							{
								// all of [z] is copied from this daughter;
								// copy [k] from slot [k] on this daughter
								F[k].base = lookup_type(top_type);
								F[k].addrs = malloc(sizeof(struct qcaddr));
								F[k].addrs[0].dtr = addrs[mark][l].dtr;
								F[k].addrs[0].slot = k;
								F[k].naddrs = 1;
								break;
							}
						if(l<naddrs[mark])break;
					}
			}
			else
			{
				int	mark = (int)(long)T;
				assert(mark > 0 && mark < marker);
				F[k].base = qc_type_n(qbase, k);
				F[k].addrs = malloc(sizeof(struct qcaddr)*naddrs[mark]);
				for(l=0;l<naddrs[mark];l++)
					if(addrs[mark][l].dtr != except && addrs[mark][l].dtr != -1)
						F[k].addrs[F[k].naddrs++] = addrs[mark][l];
			}
		}
		return F;
	}

	r->mother = extract_formula(mqc, mqc_base, -1);
	r->daughters = malloc(sizeof(struct qcformula*) * R->ndaughters);
	for(i=0;i<R->ndaughters;i++)
		r->daughters[i] = extract_formula(dqc[i], dqc_base[i], i);

	return r;
}

print_qc_rule(struct qcrule	*r)
{
	printf("QC rule for `%s'\n", r->rule->name);
	int i, j;
	for(i=0;i<qc_size;i++)
	{
		struct qcformula	F = r->mother[i];
		printf("mother.qc[%3d] = %s", i, F.base?F.base->name:"MISSING");
		for(j=0;j<F.naddrs;j++)
			printf(" & dtr[%d].qc[%d]", F.addrs[j].dtr, F.addrs[j].slot);
		printf("\n");
	}
}

void prepare_qc_rules()
{
	int i;
	if(qcrules)return;
	qcrules = calloc(sizeof(struct qcrule*),nrules);
	for(i=0;i<nrules;i++)
	{
		qcrules[i] = prepare_qc_rule(rules[i]);
		//print_qc_rule(qcrules[i]);
	}
}

struct type	*infer_qcformula(struct qcformula	F, struct qc	**dtrqc)
{
	struct type	*t = F.base;
	int i;
	for(i=0;i<F.naddrs;i++)
	{
		if(!dtrqc[F.addrs[i].dtr])continue;	// that daughter is not present yet
		struct type	**typelist = (struct type**)dtrqc[F.addrs[i].dtr];	// faster to access it directly... shame on us.
		struct type	*x = typelist[F.addrs[i].slot];
		if(!x)continue;	// that slot was not filled on the daughter, so it contributes no constraint
		if(!t)t = x;
		else t = glb(t, x);
	}
	return t;
}

struct qcedge
{
	int	id;
	int	from, to;
	struct qcrule	*rule;
	struct lexeme	*lex;
	struct qc		*qc;

	int	frosted, frozen;

	int	have, need;
	struct qcedge	**dtrs;
	int	npack, apack;
	struct qcedge	**pack;

	int	reachable;
};

infer_qcarg(struct qcedge	*e)
{
	struct qc	*argqc[e->need];
	int i;
	bzero(argqc, sizeof(argqc));
	if(!e->rule->rule->rtl)
		for(i=0;i<e->have;i++)
			argqc[i] = e->dtrs[i]->qc;
	else for(i=0;i<e->have;i++)
		argqc[e->need-e->have + i] = e->dtrs[i]->qc;

	struct type	**typelist = calloc(sizeof(struct type*),qc_size);
	e->qc = (struct qc*)typelist;
	if(e->have == e->need)
		for(i=0;i<qc_size;i++)
			typelist[i] = infer_qcformula(e->rule->mother[i], argqc);
	else
	{
		int	next_dtr = e->rule->rule->rtl?(e->need-e->have-1):e->have;
		for(i=0;i<qc_size;i++)
			typelist[i] = infer_qcformula(e->rule->daughters[next_dtr][i], argqc);
	}
}

struct pq
{
	int	prio;
	void	*elem;
	struct pq	*left, *right;
};

struct pq	*qc_agenda;

pq_insert(struct pq	**Q, struct pq	*p)
{
	struct pq	*q = *Q;
	p->left = p->right = NULL;
	if(!q) *Q = p;
	else if(p->prio < q->prio)
	{
		p->left = q->left;
		p->right = q->right;
		*Q = p;
		pq_insert(Q, q);
	}
	else
	{
		if(rand()%2)pq_insert(&q->left, p);
		else pq_insert(&q->right, p);
	}
}

struct pq	*pq_pop(struct pq	**Q)
{
	struct pq	*q = *Q;
	if(!q)return NULL;
	if(!q->left && !q->right)*Q = NULL;
	else if(q->left && !q->right)*Q = pq_pop(&q->left);
	else if(q->right && !q->left)*Q = pq_pop(&q->right);
	else if(q->left->prio < q->right->prio)*Q = pq_pop(&q->left);
	else if(q->left->prio > q->right->prio)*Q = pq_pop(&q->right);
	else if(rand()%2)*Q = pq_pop(&q->left);
	else *Q = pq_pop(&q->right);
	if(*Q)
	{
		(*Q)->left = q->left;
		(*Q)->right = q->right;
	}
	return q;
}

void	print_pq(struct pq	*q, int	t)
{
	if(!q)return;
	printf("%*d\n", t, q->prio);
	print_pq(q->left, t+2);
	print_pq(q->right, t+2);
}

add_qc_agenda(struct qcedge	*e, int	special_prio)
{
	//printf("qc agenda add: %p\n", e);
	if(e->pack)
		if(!e->pack[0])printf("agenda: edge #%d had bad properties\n", e->id);
	struct pq	*p = calloc(sizeof(*p),1);
	p->elem = e;
	p->prio = e->to-e->from;
	if(special_prio)p->prio = special_prio;
	pq_insert(&qc_agenda, p);
	//printf("after insert, qc agenda is:\n");
	//print_pq(qc_agenda, 0);
}

struct qcedge	*qcagenda_next()
{
	struct pq	*p = pq_pop(&qc_agenda);
	if(!p)return NULL;
	struct qcedge	*e = p->elem;
	free(p);
	//printf("after pop, qc agenda is:\n");
	//print_pq(qc_agenda, 0);
	return e;
}

struct qccc
{
	int	nedges;
	struct qcedge	**edges;
};

struct qccc	*qcchart;
int			qcchartsize;
int	qceidgen = 1;
int	nqcpassive, nqcactive;

clear_qc_chart(int	cs)
{
	free(qcchart);
	qcchart = malloc(sizeof(struct qccc)*cs*cs);
	bzero(qcchart, sizeof(struct qccc)*cs*cs);
	qcchartsize = cs;
	qceidgen = 1;
}

add_qc_chart(struct qcedge	*e)
{
	struct qccc	*c = &qcchart[e->from * qcchartsize + e->to];
	c->nedges++;
	c->edges = realloc(c->edges, sizeof(struct qcedge*)*c->nedges);
	c->edges[c->nedges-1] = e;
}

void	qccombine(struct qcedge	*passive, struct qcedge	*active, int	rtl)
{
	if(passive->frosted || active->frosted)return;
	//printf("can I combine #%d with #%d '%s'?\n", passive->id, active->id, active->rule->rule->name);
	int	next_dtr = rtl?(active->need-active->have-1):active->have;
	/*if(passive->rule && !check_rf(active->rule->rule, passive->rule->rule, next_dtr))
		return;*/
		// the rule filter built on full signs is not actually admissible for predicting whether QC will fail... applying it could lead to incorrect packing behavior: we could assume a parallel bunch of edges will crop up from a more general edge, when the RF will block them.
		// the RF behavior is *better*, since what we want is a fast precise grammar, but need to figure out how to make packing play correctly with it.

	int	rfrom = active->from, rto = active->to;
	if(passive->from < rfrom)rfrom = passive->from;
	if(passive->to > rto)rto = passive->to;
	if(active->have == active->need-1)
	{
		// building a passive dge
		if(rfrom == 0 && rto == qcchartsize-1)
		{
			extern char	*rule_root_utc;
			if(!rule_root_utc[active->rule->rule->rnum])
				return;
		}
		else
		{
			if(active->rule->rule->span_only)return;
		}
	}
	else
	{
		// building an active edge
		if(active->rule->rule->rtl && rfrom == 0)return;	// would have no room to grow left
		if(!active->rule->rule->rtl && rto == qcchartsize - 1)return;	// would have no room to grow right
	}

	if(quickcheck(active->qc, passive->qc))return;

	struct qcedge	*e = slab_alloc(sizeof(*e));
	bzero(e, sizeof(*e));
	e->id = qceidgen++;
	e->from = passive->from;
	if(active->from < e->from)e->from = active->from;
	e->to = passive->to;
	if(active->to > e->to)e->to = active->to;
	e->rule = active->rule;
	e->have = active->have+1;
	e->need = active->need;
	e->dtrs = malloc(sizeof(struct qcedge*)*e->have);
	if(rtl)
	{
		memcpy(e->dtrs+1, active->dtrs, sizeof(struct qcedge*)*active->have);
		e->dtrs[0] = passive;
	}
	else
	{
		memcpy(e->dtrs, active->dtrs, sizeof(struct qcedge*)*active->have);
		e->dtrs[e->have-1] = passive;
	}
	infer_qcarg(e);
	add_qc_agenda(e, 0);
}

void	qc_frost_parents(struct qccc	*c, struct qcedge	*e)
{
	int i;
	if(e->frosted)return;
	e->frosted = 1;
	for(i=0;i<c->nedges;i++)
		if(c->edges[i]->have == 1 && c->edges[i]->dtrs[0] == e)
			qc_frost_parents(c, c->edges[i]);
}

int	qc_has_frosted_daughter(struct qcedge	*e)
{
	int i;
	for(i=0;i<e->have;i++)
		if(e->dtrs[i]->frosted)return 1;
	return 0;
}

void	qcpack(struct qcedge	*h, struct qcedge	*p)
{
	if(!h->pack && p->pack && p->npack < p->apack)
	{
		// quick common case for retroactive packing
		h->pack = p->pack;
		h->npack = p->npack;
		h->apack = p->apack;
		h->pack[h->npack++] = p;
		p->pack = NULL;
		p->npack = 0;
		p->apack = 0;
		return;
	}
	if(!p->pack && h->npack < h->apack)
	{
		// quick common case for proactive packing
		h->pack[h->npack++] = p;
		return;
	}
	//printf("host has %d npack; p has %d npack\n", h->npack, p->npack);
	int	need = h->npack + p->npack + 1;
	if(need > h->apack)
	{
		int	olda = h->apack;
		h->apack = need*2;
		h->pack = slab_realloc(h->pack, sizeof(struct qcedge*)*olda, sizeof(struct qcedge*)*h->apack);
	}
	memcpy(h->pack+h->npack, p->pack, sizeof(struct qcedge*)*p->npack);
	h->npack += p->npack;
	h->pack[h->npack++] = p;
	assert(h->npack == need);
	p->pack = NULL;
	p->npack = 0;
	p->apack = 0;
}

int	qcpacked(struct qcedge	*e)
{
	struct qccc	*c = &qcchart[e->from * qcchartsize + e->to];
	int i;
	if(e->have != e->need)return 0;
	//printf("check packability...\n");
	for(i=0;i<c->nedges;i++)
	{
		struct qcedge	*h = c->edges[i];
		if(h->have != h->need)continue;
		//if(h->have!=e->have || h->need!=e->need)continue;
		// need to have the same remaining arity
		//if((h->need - h->have) != (e->need - e->have))continue;
		// active edges need to be looking the same way
		//if(h->have != h->need && h->rule->rule->rtl != e->rule->rule->rtl)continue;
		int	fw = 1, bw = 1, gz = 1;
		equiv_quickcheck(e->qc, h->qc, &fw, &bw, &gz);
		if(fw)
		{
			//printf("forward\n");
			qcpack(h, e);
			return 1;
		}
		if(bw)
		{
			// retroactive packing: expunge the old edge from the chart.
			// should also look for stuff built on this edge and frost it...
			// but we'll come back and get that stuff eventually.
			h->frozen = 1;
			qc_frost_parents(c, h);
			c->nedges--;
			qcpack(e, h);
			memmove(c->edges+i,c->edges+i+1,sizeof(struct qcedge*)*(c->nedges-i));
			//if(e->have==e->need)printf("  reverse\n");
			if(h->have == h->need)nqcpassive--;
			else nqcactive--;
		}
	}
	return 0;
}

qc_show_yield(struct qcedge	*e)
{
	int i;
	if(e->have != e->need && e->rule->rule->rtl)
		for(i=e->have;i<e->need;i++)
			printf(" [_]");
	for(i=0;i<e->have;i++)qc_show_yield(e->dtrs[i]);
	if(e->have != e->need && !e->rule->rule->rtl)
		for(i=e->have;i<e->need;i++)
			printf(" [_]");
	if(!e->have)
	{
		assert(e->lex);
		printf(" %s", e->lex->word);
	}
}

void print_qc_vector(struct qc	*q)
{
	int i;
	for(i=0;i<qc_size;i++)
	{
		struct type	*t = qc_type_n(q, i);
		printf("   QC[%d] = %s\n", i, t?t->name:"(MISSING)");
	}
}

struct profiler	*qc_profiler = NULL;

void	generalize_qcpack(struct qcedge	*e)
{
	struct qccc *cell = &qcchart[e->from * qcchartsize + e->to];
	// e is not subsumed by anything in 'cell'.
	// pick an edge minimally different from e and produce a generalized edge
	int	i, mindiff = 100000, mindiffi = 0;
	for(i=0;i<cell->nedges;i++)
	{
		struct qcedge	*p = cell->edges[i];
	}
}

void	qcprocess(struct qcedge	*e)
{
	if(qc_has_frosted_daughter(e))return;
	static struct profiler	*qpackp = NULL, *qprocp = NULL;
	start_and_alloc_profiler(&qpackp, "qcp-packing", qc_profiler, NULL);
	int p = qcpacked(e);
	stop_profiler(qpackp, 1);
	if(p)
	{
		//printf(" ... packed\n");
		return;
	}

	/*struct qccc *cell = &qcchart[e->from * qcchartsize + e->to];
	if(cell->nedges >= QC_EDGE_LIMIT)
	{
		generalize_qcpack(e);
		return;
	}*/

	/*printf("QC %s edge #%d", (e->have==e->need)?"passive":((e->have==0)?"epsilon":"active"), e->id);
	if(e->rule)
	{
		printf(" rule %s ", e->rule->rule->name);
		if(e->have)printf(" = #%d", e->dtrs[0]->id);
		else printf(" <from lexical parsing>");
		int j;
		for(j=1;j<e->have;j++)
			printf(" + #%d", e->dtrs[j]->id);
	}
	else printf(" <from lexical parsing>");
	qc_show_yield(e);
	printf("\n");*/

	/*print_qc_vector(e->qc);*/

	start_and_alloc_profiler(&qprocp, "qcp-combining", qc_profiler, NULL);
	if(e->have == e->need)nqcpassive++;
	else nqcactive++;

	add_qc_chart(e);

	// look for things to combine with
	if(e->have == e->need)
	{
		// passive looking for actives
		// look right
		int i;
		for(i=e->to;i<qcchartsize;i++)
		{
			struct qccc *c = &qcchart[e->to * qcchartsize + i];
			int j;
			for(j=0;j<c->nedges;j++)
			{
				struct qcedge	*a = c->edges[j];
				if(a->rule && a->rule->rule->rtl && a->have < a->need)qccombine(e,a,1);
			}
		}
		// look left
		for(i=0;i<=e->from;i++)
		{
			struct qccc *c = &qcchart[i * qcchartsize + e->from];
			int j;
			for(j=0;j<c->nedges;j++)
			{
				struct qcedge	*a = c->edges[j];
				if(!(a->rule && a->rule->rule->rtl) && a->have < a->need)qccombine(e,a,0);
			}
		}
	}
	else
	{
		// active looking for passives
		int i;
		if(!(e->rule && e->rule->rule->rtl))
		{
			// look right
			for(i=e->to;i<qcchartsize;i++)
			{
				struct qccc *c = &qcchart[e->to * qcchartsize + i];
				int j;
				for(j=0;j<c->nedges;j++)
				{
					struct qcedge	*p = c->edges[j];
					if(p->have == p->need)qccombine(p,e,0);
				}
			}
		}
		else
		{
			// look left
			for(i=0;i<=e->from;i++)
			{
				struct qccc *c = &qcchart[i * qcchartsize + e->from];
				int j;
				for(j=0;j<c->nedges;j++)
				{
					struct qcedge	*p = c->edges[j];
					if(p->have == p->need)qccombine(p,e,1);
				}
			}
		}
	}
	stop_profiler(qprocp, 1);
}

int	qcmark(struct qcedge	*p, int	was_packed)
{
	if(p->reachable)return 0;
	int n = was_packed?0:1, i;
	p->reachable = 1;
	for(i=0;i<p->npack;i++)n += qcmark(p->pack[i], 1);
	for(i=0;i<p->have;i++)n += qcmark(p->dtrs[i], 0);
	return n;
}

qcprune()
{
	int	from = 0, to = qcchartsize-1;
	struct qccc	*rc = &qcchart[from * qcchartsize + to];
	int i, nroots = 0, nspan = 0, nreach = 0;
	for(i=0;i<rc->nedges;i++)
	{
		struct qcedge	*e = rc->edges[i];
		if(e->have != e->need)continue;
		if(e->frozen || e->frosted)continue;
		nspan += 1 + e->npack;
		if(!qc_is_root(e->qc))continue;
		nroots += 1 + e->npack;
		nreach += qcmark(e, 0);
	}
	printf("%d spanning edges ; %d are root ; %d reachable passives in chart\n", nspan, nroots, nreach);
}

int	first_pass_parse(struct lattice	*lexical_chart)
{
	start_and_alloc_profiler(&qc_profiler, "qc-parsing", parse_profiler, NULL);
	nqcactive = nqcpassive = 0;
	prepare_qc_rules();
	// it should probably already be sorted, but just in case
	sort_lattice(lexical_chart);

	int	nwords = lexical_chart->lattice_vertex_id_gen - 1;
	// setup the chart
	clear_qc_chart(nwords+1);

	// put lexical edges into agenda
	int i, j;
	// note: edges need to be process_edge()'d into the chart in the same order they were discovered in lexical parsing,
	// which should be the same order they appear in the lexical_chart->edges list.
	// if we dont do it in the right order, we can violate some assumptions of the retroactive packing system
	// and end up with spurious readings.
	for(i=0;i<lexical_chart->nedges;i++)
	{
		struct lattice_edge	*le = lexical_chart->edges[i];
		assert(le->edge != NULL);
		le->edge->from = le->from->id;
		le->edge->to = le->to->id;
		struct qcedge	*qe = slab_alloc(sizeof(*qe));
		bzero(qe, sizeof(*qe));
		if(!le->edge->rule)
			qe->rule = NULL;	// call these spontaneous
		else qe->rule = qcrules[le->edge->rule->rnum];
		qe->dtrs = NULL;
		qe->have = 0;
		qe->need = 0;
		qe->lex = le->edge->lex;
		qe->from = le->edge->from;
		qe->to = le->edge->to;
		qe->qc = le->edge->qc;
		qe->id = qceidgen++;
		add_qc_agenda(qe, i - (lexical_chart->nedges + 100));	// FIFO ordering of lexical edges is important for retroactive packing to work correctly
	}

	// put syntax rules into agenda
	for(i=0;i<nrules;i++)
	{
		if(!qcrules[i])continue;
		if(rules[i]->lexical)continue;
		if(!strcasecmp(rules[i]->name, "xp_brck-pr_c"))continue;	/// XXX for now.
		if(!strcasecmp(rules[i]->name, "w-w_fw-seq-t_c"))continue;	/// XXX for now.
		for(j=0;j<=nwords;j++)
		{
			/*if(j==0 && rules[i]->rtl)continue;
			if(j==nwords && !rules[i]->rtl)continue;*/
			int rtl = rules[i]->rtl;
			if(	(!rtl && j+rules[i]->ndaughters <= nwords) ||
				(rtl && j-rules[i]->ndaughters >= 0)	)
			{
				struct qcedge	*qe = slab_alloc(sizeof(*qe));
				bzero(qe, sizeof(*qe));
				qe->id = qceidgen++;
				qe->rule = qcrules[i];
				qe->lex = NULL;
				qe->dtrs = NULL;
				qe->have = 0;
				qe->need = qe->rule->rule->ndaughters;
				qe->from = j;
				qe->to = j;
			//printf("adding epsila for '%s' in position %d with need = %d ; rtl = %d\n", qe->rule->rule->name, j, qe->need, qe->rule->rule->rtl);
				infer_qcarg(qe);
				add_qc_chart(qe);
			}
		}
	}

	struct qcedge	*next;
	while( (next = qcagenda_next()) != NULL)
		qcprocess(next);
	qcprune();
	printf("QC edge count: %d [ not packed: %d active, %d passive ]\n", qceidgen, nqcactive, nqcpassive);
	stop_profiler(qc_profiler, 1);
}
