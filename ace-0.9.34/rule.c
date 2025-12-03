#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>

#include	"tdl.h"
#include	"dag.h"
#include	"type.h"
#include	"rule.h"
#include	"chart.h"
#include	"conf.h"
#include	"freeze.h"
#include	"lexicon.h"

struct dg	*constrain_rule_rels(struct dg *dg, struct dg *rels);
char	*compute_nosplexrftc();

struct rule	**rules;
int		nrules;

char	*rule_filter, *rule_sfilter;
char	*nosplexrftc;
int	*nhactive, *nactive, *npassive, *nrecomb, *nused, *nptries, *natries;
int	used_total = 0, pused_total = 0;
extern int nfinal, trace, inhibit_pack;

extern unsigned int generation;
extern int gen_qc;

int	lexrulefilt_l(int	x, int	rule);
int	lexrulefilt_f(int	x, int	rule);

struct qc	**ruleqc;

void	rule_stats()
{
	int	i;
	int	nact = 0, npass = 0, nrec = 0, nhact = 0, natry=0, nptry=0;

	if(!nactive || !npassive || !nrecomb || !nhactive || !nused)return;
	for(i=0;i<nrules;i++)
	{
		if(nactive[i])printf("%4d %.3f %d %s\n", nactive[i], (float)nrecomb[i] / nactive[i], i, rules[i]->name);
		//printf("%32s %6d %6d %6d %.1f\n", rules[i]->name, nused[i], npassive[i], nactive[i], 100*(float)nused[i]/npassive[i]);
		nact+=nactive[i];
		npass+=npassive[i];
		nrec+=nrecomb[i];
		nhact+=nhactive[i];
		natry+=natries[i];
		nptry+=nptries[i];
	}
	//nptry += nptries[nrules];
//	fprintf(stderr, "NOTE: %d active (%d hyper) / %d passive edges total (%d actives used, %d passives used, %d reformed) ; %d final edges\n", nact, nhact, npass, used_total, pused_total, nrec, nfinal);
//	fprintf(stderr, "NOTE: %d a-tries = %.1f%%, %d p-tries = %.1f%%\n", natry, 100*(float)natry / nact, nptry, 100*(float)nptry / npass);
	free(nactive);
	free(npassive);
	free(nhactive);
	free(nrecomb);
	free(nused);
	free(natries);
	free(nptries);
}

int	rule_is_rtl_key(struct rule	*r)
{
	//struct dg	*hd = dg_hop(r->dg, lookup_fname("HEAD-DTR"));
	struct type	*plus = lookup_type("+");
	struct dg	*args, *asec, *afkey;

	if(!plus)return 0;
	//if(!hd)return 0;
	args = dg_hop(r->dg, lookup_fname("ARGS"));
	if(!args)return 0;
	args = dg_hop(args, lookup_fname("REST"));
	if(!args)return 0;
	asec = dg_hop(args, lookup_fname("FIRST"));
	if(!asec)return 0;
	afkey = dg_hop(asec, lookup_fname("KEY-ARG"));
	// ARGS REST FIRST KEY-ARG

	if(afkey && afkey->xtype == plus)
	//if(asec==hd)
	{
		//fprintf(stderr, "rule `%s' is right-to-left\n", r->name);
		return 1;
	}
	else
	{
		//fprintf(stderr, "rule `%s' is left-to-right\n", r->name);
		return 0;
	}
}

struct rule	*lookup_rule(char	*name) { return get_rule_by_name(name); }
/*{
	int	i;
	for(i=0;i<nrules;i++)
		if(!strcmp(rules[i]->name, name))return rules[i];
	return NULL;
}*/

int	rule_is_rtl_head(struct rule	*r)
{
	struct dg	*args, *asec, *hddtr;

	args = dg_hop(r->dg, lookup_fname("ARGS"));
	if(!args)return 0;
	args = dg_hop(args, lookup_fname("REST"));
	if(!args)return 0;
	asec = dg_hop(args, lookup_fname("FIRST"));
	if(!asec)return 0;
	hddtr = dg_hop(r->dg, lookup_fname("HD-DTR"));
	// ARGS REST FIRST =? HD-DTR

	if(hddtr == asec)
	//if(asec==hd)
	{
		//fprintf(stderr, "rule `%s' is right-to-left\n", r->name);
		return 1;
	}
	else
	{
		//fprintf(stderr, "rule `%s' is left-to-right\n", r->name);
		return 0;
	}
}

struct edge	*epsilon_edge(struct rule	*r, int	x, int	rtl, struct dg	*rels)
{
	struct edge	*e = slab_alloc(sizeof(struct edge));
	extern int	__qc_use_heap;

	bzero(e, sizeof(struct edge));
	e->from = e->to = x;
	e->id = next_eid();
	e->rule = r;
	e->need = r->ndaughters;
	e->dg = inhibit_pack?r->dg:((g_mode==PARSING)?r->packdg:r->gpackdg);
	if(!e->dg)
	{
		fprintf(stderr, "epsilon_edge: bad frozen grammar! rule `%s' has no dg!\n", r->name);
		exit(-1);
	}
	if(rels)
	{
		e->dg = constrain_rule_rels(r->dg, rels);
		if(!e->dg)
		{
			//printf("failed to constrain rule %s; ", r->name); unify_backtrace();
			return 0;
		}
	}
	e->rtl = rtl;

	if(!ruleqc)ruleqc = calloc(sizeof(struct qc*), nrules);

	if(!ruleqc[r->rnum] && !gen_qc)
	{
		__qc_use_heap = 1;
		if(rtl)ruleqc[r->rnum] = extract_qc_arg(r->dg, r->ndaughters-1);
		else ruleqc[r->rnum] = extract_qc_arg(r->dg, 0);
		__qc_use_heap = 0;
	}
	e->qc = ruleqc[r->rnum];
	if(g_mode == GENERATING)
	{
		e->ep_span_bv = bitvec_slab_alloc(n_epsbv);
		bitvec_clear_all(e->ep_span_bv, n_epsbv);
	}

	if(trace>1)
	{
		printf("epsilon [%d] of %s is #%d\n", x, r->name, e->id);
		print_dg(e->dg); printf("\n\n");
	}

	return e;
}

// return a copy of 'dg' with 'rels' unified into the C-CONT RELS slot
struct dg	*constrain_rule_rels(struct dg *dg, struct dg *rels)
{
	extern long top_copies;
	extern int	upathl;
	struct slab_state	slab;
	struct dg			*target;
	get_slabstate(&slab);

	target = dg_path(dg, rule_rels_path);

#ifdef UNIFY_PATHS
	upathl = 0;
#endif
	if(0 != unify1(target, rels))
	{ fail:
		set_slabstate(&slab);
		generation++;
		return 0;
	}
	// the unification succeeded; copy out the result, applying the packing restrictor
	enable_packing(inhibit_pack?0:2);
	dg = copy_dg_with_comp_arcs(dg);
	enable_packing(0);
	generation++;
	if(generation==MAX_GEN)
	{
		fprintf(stderr, "ERROR: generation overflowed!\n");
		exit(-1);
	}
	if(!dg)goto fail;
	top_copies++;
	return dg;
}

init_rstats()
{
#ifdef	RULE_STATS
	if(!nactive)
	{
		nactive = calloc(sizeof(int),nrules);
		nhactive = calloc(sizeof(int),nrules);
		npassive = calloc(sizeof(int),nrules);
		nrecomb = calloc(sizeof(int),nrules);
		nused = calloc(sizeof(int),nrules);
		natries = calloc(sizeof(int),nrules);
		nptries = calloc(sizeof(int),nrules+1);
	}
#endif
}

// this only adds syntax rules, not lexical rules
void	agenda_rules(int	count)
{
	int	i, j, rtl, nlf = 0;

	for(i=0;i<=count;i++)
	{
		for(j=0;j<nrules;j++)
		{
			if(!rules[j]->lexical)	// lex-rules have already been processed by lexical parsing
			{
				rtl = rules[j]->rtl;
				if(	(!rtl && i+rules[j]->ndaughters <= count) ||
					(rtl && i-rules[j]->ndaughters >= 0)	)
				{
					// these filters do occassionally fire,
					// but empirically they make so little difference to performance
					// that they aren't worthwhile.
					/*if(!rtl && lexrulefilt_f(i, j))
					{
						//printf(" rule %s F-filtered for position %d\n", rules[j]->name, i);
						nlf++;
						continue;
					}
					if(rtl && lexrulefilt_l(i, j))
					{
						//printf(" rule %s L-filtered for position %d\n", rules[j]->name, i);
						nlf++;
						continue;
					}*/
					add_agenda(epsilon_edge(rules[j], i, rtl, 0));
				}
			}
		}
	}
	//fprintf(stderr, "NOTE: lex-filtered %d epsilon-edges\n", nlf);
}

/*void	install_rule_name(struct dg	*dg, char *name)
{
	static int	rnamef = -1;
	struct dg	*rnamedg;

	if(rnamef==-1)rnamef = lookup_fname("RNAME");
	rnamedg = dg_hop(dg, rnamef);
	if(!rnamedg)
	{
		dg->xtype->dg = add_dg_hop(dg->xtype->dg, rnamef, rnamedg);
		//printf("added rule name `%s' to rule type `%s'\n", rnamedg->xtype->name, dg->xtype->name);
	}
}*/

void	add_rule(char	*name, struct dg	*dg, int	num, struct tdl_line	*tdl)
{
	struct rule	*r = calloc(sizeof(struct rule), 1);
	int			i;

	//install_rule_name(dg, name);

	nrules++;
	rules = realloc(rules, sizeof(struct rule*)*nrules);
	rules[nrules-1] = r;

	r->name = strdup(name);
	r->dg = dg;
	r->packdg = restrict_copy_dg(dg, 0);
	r->gpackdg = restrict_copy_dg(dg, 1);
	r->ndaughters = num;
	r->orth = 0;
	r->lexical = 0;
	r->rnum = nrules-1;
	r->rtl = rule_is_rtl_key(r);
	r->tdl = tdl;

	configure_rule(r);

	//printf("rule %s [%d]:  ", name, num);
	//print_dg(dg);
	//printf("\n");
}

int	study_rule(char	*name, struct dg	*dg, struct tdl_line	*tdl)
{
	int	num = 0;
	struct dg	*p;

	int wellform_result = wellform(dg, name);
	assert(wellform_result == 0);

	p = dg_hop(dg, 0);	// ARGS
	while(p)
	{
		if(dg_hop(p, 1))num++;
		p = dg_hop(p, 2);	// REST
	}
	add_rule(name, dg, num, tdl);
	rules[nrules-1]->lexical = 0;
	return 0;
}

struct rule	*get_rule_by_name(char	*name)
{
	int	i;

	for(i=0;i<nrules;i++)if(!strcasecmp(rules[i]->name, name))break;
	if(i>=nrules)return NULL;
	else return rules[i];
}

void	print_rule(char	*name)
{
	struct rule	*r = get_rule_by_name(name);
	if(!r) { fprintf(stderr, "no such rule '%s'\n", name); return; }
	printf("rule `%s':\n", name);
	print_dg(r->dg);printf("\n");
}

int	study_lrule(char	*name, struct dg	*dg, struct tdl_line	*tdl)
{
	int	num = 0;
	struct dg	*p;

	int wellform_result = wellform(dg, name);
	assert(wellform_result == 0);

	p = dg_hop(dg, 0);	// ARGS
	while(p)
	{
		if(dg_hop(p, 1))num++;
		p = dg_hop(p, 2);	// REST
	}
	add_rule(name, dg, num, tdl);
	rules[nrules-1]->lexical = 1;

	if(tdl->odef)add_orule(rules[nrules-1], tdl->odef);
	return 0;
}

int	load_rules()
{
	if(process_tdl_dgs_status("rule", study_rule))
	{
		fprintf(stderr, "rules: unable to load rules, bailing out.\n");
		exit(-1);
	}
	int	rule_does_not_exist(char	*name)
	{
		int	i;
		for(i=0;i<nrules;i++)
			if(!strcmp(rules[i]->name, name))return 0;
		fprintf(stderr, "warning: config refers to nonexistant rule '%s'\n", name);
		return 0;
	}
	iterate_conf_list("spanning-only-rules", rule_does_not_exist);
	iterate_conf_list("fragment-only-rules", rule_does_not_exist);
	iterate_conf_list("hyper-active-rules", rule_does_not_exist);
	return 0;
}

char	**rf_tc, **rl_tc;
char	**type_rf, **type_rl;
char	**type_rftc, **type_rltc;

char	*setup_rule_filter1(int pack)
{
	int	i, j, k;
	struct rule	*m, *d;
	struct dg	*mdg;
	int	yes = 0, count = 0, res, ssbl = 0;
	char	byte, *rule_filter;
	struct type *top = get_top();

	show_task_name("rule filter...");
	rule_filter = calloc(sizeof(char), nrules*nrules);
	rule_sfilter = calloc(sizeof(char), nrules*nrules);

	struct slab_state	ost;
	get_slabstate(&ost);

	struct type	*save_types[nrules];
	struct qc	***rqc = malloc(sizeof(struct qc**) * nrules);
	static struct type *signtype = 0;
	if(!signtype)signtype = lookup_type("sign");
	for(i=0;i<nrules;i++)
	{
		struct rule	*m = rules[i];
		mdg = pack?( (pack==1) ? m->packdg : m->gpackdg ) : m->dg;
		save_types[i] = mdg->xtype;
		if(enable_generalize_edge_top_types)
			mdg->xtype = signtype;
		rqc[i] = malloc(sizeof(struct qc*) * (m->ndaughters+1));
		rqc[i][0] = extract_qc(mdg);
		for(j=0;j<m->ndaughters;j++)
			rqc[i][j+1] = extract_qc_arg(mdg, j);
	}

	// copies of each rule's dag used to test whether subsumption is possible
	// subsumption between (specializations of) two rules is judged as possible when
	// the two rules dags unify.
	struct dg	**trim_copies = malloc(sizeof(struct dg*)*nrules);
	for(i=0;i<nrules;i++)
	{
		struct rule	*m = rules[i];
		struct dg	*dg = pack?( (pack==1) ? m->packdg : m->gpackdg ) : m->dg;
		trim_copies[i] = trim_copy(dg);
		trim_copies[i]->xtype = trim_copies[i]->type = top;
	}

	for(i=0;i<nrules;i++)
	{
		struct slab_state	st;
		get_slabstate(&st);
		m = rules[i];
		if(m->ndaughters>8)
		{
			fprintf(stderr, "ERROR: rule `%s' takes %d daughters!\n", m->name, m->ndaughters);
			exit(-1);
		}
		mdg = copy_dg(pack?( (pack==1) ? m->packdg : m->gpackdg ) : m->dg );	// necessary for the case when we try to unify a rule into itself!
		for(j=0;j<nrules;j++)
		{
			d = rules[j];
			struct dg *ddg = pack?( (pack==1) ? d->packdg : d->gpackdg ) : d->dg;
			byte = 0;
			for(k=0;k<m->ndaughters;k++)
			{
				struct qc	*mqc = rqc[i][k+1];
				struct qc	*dqc = rqc[j][0];
				if(quickcheck(mqc, dqc))continue;
				res = unify_dg_tmp(ddg, mdg, k);
				forget_tmp();
				if(res==0)
				{
					byte |= (1<<k);
					yes++;
				}
			}
			count += m->ndaughters;
			rule_filter[i*nrules + j] = byte;

			if(i < j)
			{
				//struct dg	*left = trim_copy(ddg), *right = trim_copy(mdg);
				//left->xtype = left->type = top;
				//right->xtype = right->type = top;
				struct qc	*left_qc = rqc[i][0], *right_qc = rqc[j][0];
				if(quickcheck(left_qc, right_qc))res = -1;
				//else res = unify_dg_tmp(left, right, -1);
				else
				{
					res = unify_dg_tmp(trim_copies[i], trim_copies[j], -1);
					forget_tmp();
				}
				if(res)
				{
					//printf("ssfilter[%d] `%s' + `%s': ", pack, rules[i]->name, rules[j]->name);
					//unify_backtrace();
					ssbl++;
				}
				//forget_tmp();
			}
			else if(i == j)res = 0;
			else res = !rule_sfilter[j*nrules+i];
			rule_sfilter[i*nrules+j] = res?0:1;
		}
		set_slabstate(&st);
	}
	set_slabstate(&ost);

	if(enable_generalize_edge_top_types)
	{
		for(i=0;i<nrules;i++)
		{
			struct rule	*m = rules[i];
			mdg = pack?( (pack==1) ? m->packdg : m->gpackdg ) : m->dg;
			mdg->xtype = save_types[i];
		}
	}

	printf("%.1f%% blocked (%.1f%% ss)\n", 100*(float)(count-yes)/count, 100*(float)ssbl/nrules/nrules);
	return rule_filter;
}

struct rule_filters
{
	char	*nopack, *nopacks;
	char	*pack, *packs;
	char	*gpack, *gpacks;
	char	**rftc, **rltc;
	char	**type_rf, **type_rl;
	char	**type_rftc, **type_rltc;
	char	*nopack_nosplexrftc;
	char	*pack_nosplexrftc;
}	*filters;

void setup_rule_filter()
{
	extern int g_loaded;
	g_loaded = 1;	// make unify shut up about failures
	filters = calloc(sizeof(*filters), 1);
	filters->nopack = setup_rule_filter1(0);
	filters->nopacks = rule_sfilter;
	filters->pack = setup_rule_filter1(1);
	filters->packs = rule_sfilter;
	filters->gpack = setup_rule_filter1(2);
	filters->gpacks = rule_sfilter;

	rule_filter = filters->nopack;
	filters->nopack_nosplexrftc = compute_nosplexrftc();
	rule_filter = filters->pack;
	filters->pack_nosplexrftc = compute_nosplexrftc();

	rule_filter = filters->nopack;	// type_rxtc is applied before packing starts
	rule_sfilter = filters->nopacks;
	lex_filter_rules();
	g_loaded = 0;
}

char	**freeze_rxtc(char	**ptr, int dim)
{
	if(!ptr)return NULL;
	char	**ref = slab_alloc(nrules * sizeof(char*));
	int	len;
	char	*data;
	int	i;

	len = (nrules*dim + 3) & ~3;
	data = slab_alloc(len);
	for(i=0;i<nrules;i++)
	{
		ref[i] = data;
		data += dim;
		memcpy(ref[i], ptr[i], dim);
	}
	return ref;
}

void	*freeze_rule_filter()
{
	if(!filters)return NULL;
	filters = freeze_block(filters, sizeof(*filters));
	filters->nopack = freeze_block(filters->nopack, sizeof(char) * nrules*nrules);
	filters->nopacks = freeze_block(filters->nopacks, sizeof(char) * nrules*nrules);
	filters->pack = freeze_block(filters->pack, sizeof(char) * nrules*nrules);
	filters->packs = freeze_block(filters->packs, sizeof(char) * nrules*nrules);
	filters->gpack = freeze_block(filters->gpack, sizeof(char) * nrules*nrules);
	filters->gpacks = freeze_block(filters->gpacks, sizeof(char) * nrules*nrules);
	filters->rftc = freeze_rxtc(rf_tc, nrules);
	filters->rltc = freeze_rxtc(rl_tc, nrules);
	struct type_hierarchy	*th = default_type_hierarchy();
	filters->type_rf = freeze_rxtc(type_rf, th->ntypes);
	filters->type_rl = freeze_rxtc(type_rl, th->ntypes);
	filters->type_rftc = freeze_rxtc(type_rftc, th->ntypes);
	filters->type_rltc = freeze_rxtc(type_rltc, th->ntypes);
	filters->nopack_nosplexrftc = freeze_block(filters->nopack_nosplexrftc, nrules*nrules);
	filters->pack_nosplexrftc = freeze_block(filters->pack_nosplexrftc, nrules*nrules);
	return filters;
}

void	recover_rule_filter(void *rf)
{
	filters = rf;
	if(!filters)return;
	rf_tc = filters->rftc;
	rl_tc = filters->rltc;
	type_rf = filters->type_rf;
	type_rl = filters->type_rl;
	type_rftc = filters->type_rftc;
	type_rltc = filters->type_rltc;
}

void	install_rf(int what)
{
	if(what==0)rule_filter = filters->nopack;
	else if(what==1)rule_filter = filters->pack;
	else if(what==2)rule_filter = filters->gpack;
	else assert(!"Not reached");

	if(what==0)rule_sfilter = filters->nopacks;
	else if(what==1)rule_sfilter = filters->packs;
	else if(what==2)rule_sfilter = filters->gpacks;
	else assert(!"Not reached");

	if(what==0)nosplexrftc = filters->nopack_nosplexrftc;
	else nosplexrftc = filters->pack_nosplexrftc;
}

// compute a table showing what chains are possible of non-spelling-change lexical rules
char	*compute_nosplexrftc()
{
	char	*table = calloc(nrules,nrules);
	char	*process = calloc(nrules,1);
	char	*reprocess = calloc(nrules,1);
	int	i, j, k, n;
	// initialize with a copy of the rule filter
	for(i=0;i<nrules;i++)
	{
		for(j=0;j<nrules;j++)
		{
			// rules[j] can be the immediate daughter of rules[i]
			table[i*nrules + j] = check_rf(rules[i], rules[j], 0);
			//if(rules[i]->lexical && rules[j]->lexical)
				//printf("check_rf for mother %s daughter %s = %d\n", rules[i]->name, rules[j]->name, table[i*nrules+j]);
		}
		reprocess[i] = 1;
	}
	do
	{
		n = 0;
		memcpy(process, reprocess, nrules);
		bzero(reprocess, nrules);
		for(i=0;i<nrules;i++)
		{
			if(!rules[i]->lexical)continue;
			for(j=0;j<nrules;j++)
			{
				if(!rules[j]->lexical)continue;
				if(table[i*nrules + j])continue;	// already know this is possible
				if(!(process[i]&1) && !(process[j]&2))
					continue; // nothing new known about either i or j
				// see if we can find an intermediary non-spelling-change lexical rule
				for(k=0;k<nrules;k++)
				{
					struct rule	*x = rules[k];
					if(!x->lexical || x->orth)continue;
					if(table[i*nrules + k] && table[k*nrules + j])
					{
						table[i*nrules + j] = 1;
						reprocess[i] |= 1;
						reprocess[j] |= 2;
						n++;
						break;
					}
				}
			}
		}
	} while(n);
	return table;
}

// compute the set of rules which can appear as the x'th constituent of this rule, somewhere down the left edge of the subtree
char	*compute_rxtc(int	rnum, int right)
{
	char	*table;
	int	i, j, n, tot = 1;

	table = calloc(sizeof(char), nrules);
	table[rnum] = 1;
	do
	{
		n = 0;
		for(i=0;i<nrules;i++) if(table[i])
		{
			for(j=0;j<nrules;j++) if(!table[j] && check_rf(rules[i], rules[j], right?rules[i]->ndaughters-1:0))
			{
				table[j] = 1;
				n++;
				tot++;
			}
		}
	} while(n);

	return table;
}

// figure out what types are compatible with 'r'[arg] and what types aren't.

char	*type_filter_rule(struct rule	*r, int arg, struct qc **typeqc)
{
	struct qc *rqc = extract_qc_arg(r->dg, arg);
	char	*table;
	int	i, j, count = 0, res;

	struct type_hierarchy	*th = default_type_hierarchy();

	table = calloc(sizeof(char), th->ntypes);

	// bottom up, since most types will succeed and we can check if subtypes did
	for(i=th->ntypes-1;i>=0;i--)
	{
		struct type *t = th->types[i];

		if(generation > MAX_GEN_RESET)generation = 11; // XXX hack

		if(!t->dg)continue;
		// check descendents to see if more-specific types than me have been shown compatible
		for(j=1;j<16 && j<t->ndescendents;j++)
			if(table[t->descendents[j]])
				goto yes;
		if(quickcheck(rqc, typeqc[i]) != 0)
			continue;
		res = unify_dg_tmp(t->dg, r->dg, arg);
		forget_tmp();
		if(res==0)
		{
			yes:
			table[i] = 1;
			count++;
		}
	}
	return table;
}

void	lex_filter_rules()
{
	char **type_rf_t, **type_rl_t;

	if(gen_qc)return;

	int build_rule_filter_transitive_closure()
	{
		int i;

		rf_tc = malloc(sizeof(char*) * nrules);
		rl_tc = malloc(sizeof(char*) * nrules);
		for(i=0;i<nrules;i++)
		{
			rf_tc[i] = compute_rxtc(i, 0);
			rl_tc[i] = compute_rxtc(i, 1);
		}
		return 0;
	}
	run_task("rf-transitive closure...", build_rule_filter_transitive_closure);

	struct type_hierarchy	*th = default_type_hierarchy();

	int build_type_rule_filter()
	{
		int i, j;
		struct qc *tqc[th->ntypes];

		type_rf = malloc(sizeof(char*) * nrules);
		type_rl = malloc(sizeof(char*) * nrules);
		type_rf_t = malloc(sizeof(char*) * th->ntypes);
		type_rl_t = malloc(sizeof(char*) * th->ntypes);
		for(i=0;i<th->ntypes;i++)
			tqc[i] = th->types[i]->dg?extract_qc(th->types[i]->dg):0;
		for(i=0;i<nrules;i++)
		{
			type_rf[i] = type_filter_rule(rules[i], 0, tqc);
			type_rl[i] = type_filter_rule(rules[i], rules[i]->ndaughters-1, tqc);
		}
		for(i=0;i<th->ntypes;i++)
		{
			type_rf_t[i] = malloc(nrules);
			for(j=0;j<nrules;j++)type_rf_t[i][j] = type_rf[j][i];
			type_rl_t[i] = malloc(nrules);
			for(j=0;j<nrules;j++)type_rl_t[i][j] = type_rl[j][i];
		}
		return 0;
	}
	//printf("there are %d rules and %d types\n", nrules, th->ntypes);
	//run_task("type-rule filter...", build_type_rule_filter);

	int compose_type_rule_closured_filter()
	{
		int	i, j, k;

		type_rftc = malloc(sizeof(char*) * nrules);
		type_rltc = malloc(sizeof(char*) * nrules);
		for(i=0;i<nrules;i++)
		{
			type_rftc[i] = calloc(sizeof(char), th->ntypes);
			type_rltc[i] = calloc(sizeof(char), th->ntypes);
			for(j=0;j<th->ntypes;j++)
			{
				char *fit_rule_f = type_rf_t[j];
				char *fit_rule_l = type_rl_t[j];
				char *accept_rule_f = rf_tc[i];
				char *accept_rule_l = rl_tc[i];

				if(type_rf[i][j])type_rftc[i][j] = 1;
				else for(k=0;k<nrules;k++)
					if(accept_rule_f[k] && fit_rule_f[k])
					{
						type_rftc[i][j] = 1;
						break;
					}
				if(type_rl[i][j])type_rltc[i][j] = 1;
				else for(k=0;k<nrules;k++)
					if(accept_rule_l[k] && fit_rule_l[k])
					{
						type_rltc[i][j] = 1;
						break;
					}
			}
		}
		return 0;
	}
	//run_task("type-rule-closed filter...", compose_type_rule_closured_filter);
}

configure_rules_key_driven()
{
	int	i;
	for(i=0;i<nrules;i++)
		rules[i]->rtl = rule_is_rtl_key(rules[i]);
}

/*
configure_rules_head_driven()
{
	FILE	*f = fopen("../erg/etc/rules.hds", "r");
	assert(f != NULL);
	char	rname[1024];
	int		arity, head;
	while(fscanf(f, "%[^ ] %d %d\n", rname, &arity, &head) == 3)
	{
		struct rule	*r = lookup_rule(rname);
		if(!r) { fprintf(stderr, "erg.hds: unable to find rule '%s'\n", rname); continue; }
		r->rtl = (head!=0)?1:0;
	}
//	int	i;
//	for(i=0;i<nrules;i++)
//		rules[i]->rtl = rule_is_rtl_head(rules[i]);
	
}*/

// output rule filter left daughter graph as a .dot file
void	dot_rf(char	*fname)
{
	int	i, j;
	FILE	*f = fopen(fname, "w");

	for(i=0;i<nrules;i++) if(rules[i]->ndaughters!=1)
	{
		for(j=0;j<nrules;j++) if(rules[j]->ndaughters!=1)
		{
			//if(check_rf(rules[i], rules[j], 0))
			if(rf_tc[i][j])
				fprintf(f, "\"%s\" -> \"%s\"\n", rules[i]->name, rules[j]->name);
		}
	}
	fclose(f);
}

/*
check_unary_chains()
{
	struct dg	**dags = 0;
	int			**chains = 0;
	int			nchains = 0, *len = 0, i, j;
	nchains = 1; len = calloc(sizeof(int), 1);
	chains = calloc(sizeof(int*), 1); chains[0] = calloc(sizeof(int), 1); chains[0][0] = -1;
	dags = calloc(sizeof(struct dg*), 1); dags[0] = atomic_dg(top_type);
	for(i=0;i<nchains;i++)
	{
		for(j=0;j<nrules;j++) if(rules[j]->ndaughters==1 && !strstr(rules[j]->name, "punct_"))
		{
			// try to extend chains[i] by rules[j]
			struct rule	*d = len[i]?rules[chains[i][len[i]-1]]:0;
			if(d && !check_rf(rules[j], d, 0))continue;
			struct dg	*ndg = unify_dg(dags[i], rules[j]->dg, 0);
			if(ndg)
			{
				int k;
				for(k=0;k<nchains;k++)
					if(equivalent_dg(ndg, dags[k], 1, 1) == 2)break;
				if(k<nchains)continue;
				nchains++;
				chains = realloc(chains, sizeof(int*)*nchains);
				chains[nchains-1] = malloc(sizeof(int)*(len[i]+1));
				memcpy(chains[nchains-1], chains[i], sizeof(int)*len[i]);
				chains[nchains-1][len[i]] = j;
				len = realloc(len, sizeof(int)*nchains);
				len[nchains-1] = len[i]+1;
				dags = realloc(dags, sizeof(struct dag*)*nchains);
				dags[nchains-1] = ndg;
				for(k=0;k<len[nchains-1];k++)
					printf(" %s", rules[chains[nchains-1][k]]->name);
				printf("\n");
			}
		}
	}
	clear_slab();
}*/

static int	path[64], pathl;

struct constraint
{
	int	*path, pathl;
	int	same_upto;

	struct consub
	{
		struct type	*type;

		int			nrules;
		struct rule	**rules;
		int			*rargs;
	}	*types;
	int	ntypes;
}	*constraints;
int	nconstraints;

// returns 1 if every subtype of `parent' is compatible with `sub'
int always_compatible(struct type	*parent, struct type	*sub)
{
	int i;
	struct type_hierarchy	*th = default_type_hierarchy();
	for(i=0;i<parent->ndescendents;i++)
		if(!glb(th->types[parent->descendents[i]], sub))
		{
			//printf("%s compatible with %s but not with %s\n", th->types[parent->descendents[i]]->name, parent->name, sub->name);
			return 0;
		}
	return 1;
}

decompose_dg(struct rule	*r, int	rarg, struct dg	*dg, int feat)
{
	struct dg	**arcs = DARCS(dg);
	struct type	*at;
	int			i;

	if(feat != -1)at = most_general_type_for_feat(default_type_hierarchy(), feat);
	else at = get_top();
	if(dg->xtype != at && !always_compatible(at, dg->xtype))
	{
		struct constraint	*c = 0;
		struct consub		*ct = 0;

		for(i=0;i<nconstraints;i++)
			if(constraints[i].pathl == pathl && !memcmp(constraints[i].path, path, pathl*sizeof(int)))
			{
				c = constraints+i;
				break;
			}
		if(!c)
		{
			constraints = realloc(constraints, sizeof(struct constraint)*++nconstraints);
			c = constraints+nconstraints-1;
			c->path = malloc(sizeof(int)*pathl); memcpy(c->path, path, sizeof(int) * (c->pathl = pathl));
			c->ntypes = 0; c->types = 0;
		}
		for(i=0;i<c->ntypes;i++)
			if(c->types[i].type == dg->xtype)
			{
				ct = c->types+i;
				break;
			}
		if(i==c->ntypes)
		{
			c->types = realloc(c->types, sizeof(struct consub)*++(c->ntypes));
			ct = c->types + c->ntypes-1;
			ct->type = dg->xtype;
			ct->nrules = 0; ct->rules = 0; ct->rargs = 0;
		}
		ct->rules = realloc(ct->rules, sizeof(struct rule*)*++(ct->nrules));
		ct->rules[ct->nrules-1] = r;
		ct->rargs = realloc(ct->rargs, sizeof(int)*ct->nrules);
		ct->rargs[ct->nrules-1] = rarg;
	}

	for(i=0;i<dg->narcs;i++)
	{
		path[pathl++] = dg->label[i];
		decompose_dg(r, rarg, arcs[i], dg->label[i]);
		pathl--;
	}
}

int conscmp(const void	*a, const void	*b)
{
	const struct constraint	*A=a, *B=b;
	int	i;
	for(i=0;i<A->pathl && i<B->pathl;i++)
		if(A->path[i] != B->path[i])return A->path[i] - B->path[i];
	if(A->pathl != B->pathl)return A->pathl - B->pathl;
	return 0;
}

decompose_rules()
{
	int i, j;

	for(i=0;i<nrules;i++)
	{
		pathl = 0;
		struct dg *child = dg_hop(rules[i]->packdg, lookup_fname("ARGS"));
		for(j=0;j<rules[i]->ndaughters;j++)
		{
			decompose_dg(rules[i], j, dg_hop(child, lookup_fname("FIRST")), -1);
			child = dg_hop(child, lookup_fname("REST"));
		}
	}

	qsort(constraints, nconstraints, sizeof(struct constraint), conscmp);

	constraints[0].same_upto = 0;
	for(i=1;i<nconstraints;i++)
	{
		struct constraint *c = constraints+i, *p = constraints+i-1;
		for(c->same_upto=0;c->same_upto<c->pathl && c->same_upto<p->pathl
			&& c->path[c->same_upto]==p->path[c->same_upto];c->same_upto++) {}
	}

/*
	printf("%d constraint paths\n", nconstraints);
	for(i=0;i<nconstraints;i++)
	{
		extern char **fnames;
		struct constraint	*c = constraints+i;
		int j, k;
		printf("C#%d	", i);
		for(j=0;j<c->pathl;j++)
			printf("%s ", fnames[c->path[j]]);
		printf("%d types\n", c->ntypes);
		for(k=0;k<c->ntypes;k++)
		{
			printf("    %s (%d rules) ", c->types[k].type->name, c->types[k].nrules);
			//for(j=0;j<c->types[k].nrules;j++)
			//	printf("  %s.%d", c->types[k].rules[j]->name, c->types[k].rargs[j]);
			//printf("\n");
		}
		printf("\n");
	}
	*/
}

int	constraint_rule_filter(struct lexeme	*lex, int id, struct dg	*dg, char	*fil)
{
	int i, j, k, nleft = 2*nrules, sp = 0;
//	char	fil[2*nrules];
	struct dg	*stack[128];


	bzero(fil, 2*nrules);

	for(i=0;i<nrules;i++)
	{
		if(!lex && rules[i]->lexical) { fil[2*i] = 1; nleft--; }
		if(rules[i]->ndaughters==1) { fil[2*i+1] = 1; nleft--; }
	}

	//printf("constraint filtering passive edge #%d dag %p lex `%s'\n", id, dg, lex?lex->word:"(none)");
	stack[sp = 0] = dg;
	for(i=0;i<nconstraints;i++)
	{
		struct constraint	*c = constraints+i;
		struct dg			*d;

		if(i)sp -= constraints[i-1].pathl - c->same_upto;
		assert(sp >= 0);
		d = stack[sp];
		for(j=c->same_upto;j<c->pathl && d;j++)
			d = stack[++sp] = dg_hop(d, c->path[j]);
		for(;j<c->pathl;j++)d = stack[++sp] = 0;

		if(d)for(j=0;j<c->ntypes;j++)
		{
			struct consub	*ct = c->types+j;
			if(!glb(d->xtype, ct->type))
				for(k=0;k<ct->nrules;k++) if(!fil[2*ct->rules[k]->rnum + ct->rargs[k]])
			{
				fil[2*ct->rules[k]->rnum + ct->rargs[k]] = 1;
				nleft--;
				if(nleft==0)return -1;
				//printf("  incompatible with rule `%s.%d' due to type %s at C#%d\n", ct->rules[k]->name, ct->rargs[k], d->xtype->name, i);
			}
		}
	}

	/*for(i=0;i<2*nrules;i++)
	{
		if(!fil[i])
			printf("  compatible with rule `%s.%d'\n", rules[i/2]->name, i%2);
	}*/

	return 0;
}
