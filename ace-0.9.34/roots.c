#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>

#include	"tdl.h"
#include	"dag.h"
#include	"freeze.h"
#include	"chart.h"
#include	"rule.h"
#include	"conf.h"

struct instance	*instances;
int	ninstances;

char	*use_roots = 0;

char	**rule_inst_filter, *rule_root, *rule_root_utc;//, *rule_left_filter, *rule_right_filter;
extern char	**rf_tc, **rl_tc;

extern struct path	label_path;
extern int g_transfer;

char	*type_to_string(struct type*);

void	build_rif()
{
	int	i, j, ryes=0, yes, tyes=0, nroot=0;
	extern int g_loaded;

	clear_slab();
	g_loaded = 1;	// make unify shut up about failures
	rule_inst_filter = malloc(sizeof(char*)*nrules);
	rule_root = malloc(nrules);
	rule_root_utc = malloc(nrules);
	for(i=0;i<nrules;i++)
	{
		rule_inst_filter[i] = malloc(ninstances);
		yes = 0;
		for(j=0;j<ninstances;j++)
		{
			rule_inst_filter[i][j] = unify_dg_tmp(rules[i]->dg, instances[j].dg, -1)?0:1;
			if(instances[j].root_flag && rule_inst_filter[i][j])yes++;
			forget_tmp();
		}
		if(yes)ryes++;
		rule_root_utc[i] = (rule_root[i] = yes?1:0) && (rules[i]->ndaughters==1);
		tyes += yes;
	}
	g_loaded = 0;
//	printf("rule-instance filter: %.1f%% total, %d / %d rules\n",
//		100*(double)tyes/(nrules*ninstances), ryes, nrules);
	clear_slab();

	install_rf(0);
	do
	{
		yes = 0;
		for(i=0;i<nrules;i++) if(/*!rules[i]->lexical && */rules[i]->ndaughters==1 && !rule_root_utc[i])
		{
			for(j=0;j<nrules;j++) if(rule_root_utc[j])
				if(check_rf(rules[j], rules[i], 0))
				{
					yes = 1;
					rule_root_utc[i] = 1;
					//printf(" ... `%s' is root via `%s'\n", rules[i]->name, rules[j]->name);
					break;
				}
		}
	} while(yes);
	for(i=0;i<nrules;i++)
	{
		if(rules[i]->ndaughters==1 && rule_root_utc[i])
		{
			//printf("	root unary `%s'\n", rules[i]->name);
			for(j=0;j<nrules;j++) if(/*!rules[j]->lexical && */check_rf(rules[i], rules[j], 0))
			{
				//printf("		permits `%s'\n", rules[j]->name);
				rule_root_utc[j] = 1;
			}
		}
		else if(rule_root[i])
		{
			//printf("	root multi `%s'\n", rules[i]->name);
			rule_root_utc[i] = 1;
		}
	}

	for(i=0;i<nrules;i++)if(rule_root_utc[i])nroot++;
	//printf("%d / %d rules may be root\n", nroot, nrules);

/*
	rule_left_filter = calloc(1, nrules);
	rule_right_filter = calloc(1, nrules);
	for(i=0;i<nrules;i++)
	{
		for(j=0;j<nrules;j++)
		{
			if(rule_root[j] && rf_tc[j][i])rule_left_filter[i] = 1;
			if(rule_root[j] && rl_tc[j][i])rule_right_filter[i] = 1;
		}
		if(!rule_left_filter[i])printf("`%s' may not be leftmost\n", rules[i]->name);
		if(!rule_right_filter[i])printf("`%s' may not be rightmost\n", rules[i]->name);
	}
*/
}

struct instances
{
	struct instance	*instances;
	int				ninstances;
};

void	*freeze_instances()
{
	struct instances	*in = slab_alloc(sizeof(struct instances));
	int					i;
	in->instances = slab_alloc(sizeof(struct instance)*ninstances);
	in->ninstances = ninstances;
	for(i=0;i<ninstances;i++)
	{
		in->instances[i].name = freeze_string(instances[i].name);
		in->instances[i].root_flag = instances[i].root_flag;
		in->instances[i].dg = freeze_dg(instances[i].dg);
	}
	return in;
}

void	disable_all_roots()
{
	int	i;
	for(i=0;i<ninstances;i++)instances[i].root_flag = 0;
}

void	enable_root(char	*name)
{
	int	i;
	for(i=0;i<ninstances;i++)
		if(!strcasecmp(name, instances[i].name))
			break;
	if(i<ninstances)instances[i].root_flag = (unsigned)-1;
	else
	{
		fprintf(stderr, "roots: no such instance as `%s' available\n", name);
		exit(-1);
	}
}

void	recover_instances(void	*ptr)
{
	struct instances	*in = ptr;
	instances = in->instances;
	ninstances = in->ninstances;

	if(use_roots)
	{
		int i;
		char *p;
		for(i=0;i<ninstances;i++)instances[i].root_flag = 0;
		disable_all_roots();
		for(p=strtok(use_roots, " ");p;p=strtok(0, " "))
			enable_root(p);
	}

	if(!g_transfer)
		build_rif();
}

extern int trace;

char	*is_root(struct dg	*dg)
{
	int		i, res, flag = (g_mode == PARSING)?1:2;

	for(i=0;i<ninstances;i++) if(instances[i].root_flag & flag)
	{
		res = unify_dg_tmp(dg, instances[i].dg, -1);
		forget_tmp();
		if(!res)
		{
			if(trace>2)printf("it was root! %s\n", instances[i].name);
			return instances[i].name;
		}
#ifdef UNIFY_PATHS
		else if(trace>2)
		{
			printf("not root: ");
			unify_backtrace();
		}
#endif
	}
	return NULL;
}

int	qc_is_root(struct qc	*q)
{
	struct qc	**rqc = NULL;
	int		i, flag = (g_mode == PARSING)?1:2;
	if(!rqc)
	{
		rqc = calloc(sizeof(struct qc*),ninstances);
		for(i=0;i<ninstances;i++) if(instances[i].root_flag & flag)
			rqc[i] = extract_qc(instances[i].dg);
	}
	for(i=0;i<ninstances;i++)
		if(rqc[i] && !quickcheck(rqc[i], q))return 1;
	return 0;
}

int	study_instance(char	*lhs, struct dg	*dg, struct tdl_line	*tdl)
{
	ninstances++;
	instances = realloc(instances, sizeof(struct instance) * ninstances);
	instances[ninstances-1].name = strdup(lhs);
	instances[ninstances-1].root_flag = 1*check_conf_list("parsing-roots", lhs)
									  | 2*check_conf_list("generation-roots", lhs);
	instances[ninstances-1].dg = dg;
	return 0;
}

int	load_instances()
{
	if(process_tdl_dgs_status("instance", study_instance))
	{
		fprintf(stderr, "instances: unable to load, bailing out.\n");
		exit(-1);
	}
	return 0;
}

struct dg	*find_instance(char	*name)
{
	int	i;
	for(i=0;i<ninstances;i++)
		if(!strcmp(name, instances[i].name))
			return instances[i].dg;
	return NULL;
}

struct label
{
	char 		*name;
	struct dg	*dg;
	int				is_meta;
};

static struct label_set
{
	struct label	*labels;
	int				nlabels;
}	*lset;

void	*freeze_labels()
{
	struct label_set	*ls = slab_alloc(sizeof(*ls));
	int					i;

	if(!lset)return NULL;
	ls->nlabels = lset->nlabels;
	ls->labels = slab_alloc(sizeof(struct label)*ls->nlabels);
	for(i=0;i<ls->nlabels;i++)
	{
		ls->labels[i].name = freeze_string(lset->labels[i].name);
		ls->labels[i].dg = freeze_dg(lset->labels[i].dg);
		ls->labels[i].is_meta = lset->labels[i].is_meta;
	}
	return ls;
}

void	recover_labels(void	*ls)
{
	lset = ls;
	//printf("recover labelset %p\n", ls);
}

char	*recursive_label_dag(struct dg	*indg)
{
	// XXX this may need to check that the diff-list is not empty explicitly.
	// this would ideally (?) cause unification to fail, but
	// I guess it results in a cycle, which we don't detect until we try to copy,
	// and we aren't going to try to copy here.
	// see LKB's diff-list-strangeness() check.
	assert(lset != NULL);
	struct dg	*dg = dg_path(indg, recursive_label_path_in_sign);
	if(!dg)return NULL;
	int i;
	//printf("trying to label:\n");
	//print_dg(dg);printf("\n");
	for(i=0;i<lset->nlabels;i++)
		if(!lset->labels[i].is_meta)
		{
			struct dg	*ldg = dg_path(lset->labels[i].dg, recursive_label_path_in_label);
			if(!ldg)continue;
			int res = unify_dg_tmp(dg, ldg, -1);
			/*if(!res)
			{
				// see if there is a cycle
				struct dg	*rdg = copy_dg_with_comp_arcs(ldg);
				if(!rdg)
				{
					printf("FOUND A CYCLE when labeling\n");
					res = -1;
				}
			}*/
			forget_tmp();
			if(!res)
			{
				/*printf("recursive label %s\n", lset->labels[i].name);
				print_dg(dg);
				printf("\n");*/
				return lset->labels[i].name;
			}
		}
	return "?";
}

char	*label_dag(struct dg	*dg, char *fallback)
{
	int i;

	if(!lset)
	{
		//printf("no labelset\n");
		return fallback;
	}

	char	*meta = NULL;
	char	metalabel[128];
	for(i=0;i<lset->nlabels;i++)
		if(lset->labels[i].is_meta)
		{
			int res = unify_dg_tmp(dg, lset->labels[i].dg, -1);
			/*if(!res)
			{
				struct dg	*rdg = copy_dg_with_comp_arcs(dg);
				if(!rdg)
				{
					printf("META didn't actually apply; CYCLE.\n");
					res = -1;
				}
			}*/
			forget_tmp();
			if(!res)
			{
				char	*meta_type = recursive_label_dag(dg);
				if(!meta_type)continue;
				struct dg	*meta_suffix = dg_hop(lset->labels[i].dg, lookup_fname("META-SUFFIX"));
				struct dg	*meta_prefix = dg_hop(lset->labels[i].dg, lookup_fname("META-PREFIX"));
				sprintf(metalabel, "%s%s%s", ((meta_prefix!=NULL)?type_to_string(meta_prefix->xtype):""), meta_type, ((meta_suffix!=NULL)?type_to_string(meta_suffix->xtype):""));
				meta = metalabel;
				//printf("meta = %s\n", meta);
				break;
			}
		}

	for(i=0;i<lset->nlabels;i++)
	{
		if(lset->labels[i].is_meta)continue;
		int res = unify_dg_tmp(dg, lset->labels[i].dg, -1);
		forget_tmp();
		if(!res)
		{
			//printf("label %s\n", lset->labels[i].name);
			if(!meta)return lset->labels[i].name;
			char	label[256];
			sprintf(label, "%s%s", lset->labels[i].name, meta);
			//printf("returning label = %s    of which meta = %s\n", label, meta);
			return freeze_string(label);
		}
	}

	//printf("fallback %s\n", fallback);
	return fallback;
}

int	study_label(char	*lhs, struct dg	*dg, struct tdl_line	*tdl)
{
	int	is_meta = 0;
	char	*name;
	lookup_fname("META-SUFFIX");	// just to make sure that feature exists at runtime...
	if(dg_hop(dg, lookup_fname("META-PREFIX")))
	{
		is_meta = 1;
		name = strdup(lhs);
	}
	else
	{
		//struct dg *lname = dg_hop(dg, lookup_fname("LNAME"));
		struct dg *lname = dg_path(dg, label_path);
		if(!lname)
		{
			fprintf(stderr, "label `%s': no label found at expected path!\n", lhs);
			return 0;
		}
		name = type_to_string(lname->xtype);
	}

	dg->xtype = dg->type = get_top();
	if(!lset)lset = calloc(sizeof(struct label_set), 1);
	lset->nlabels++;
	lset->labels = realloc(lset->labels, sizeof(struct label) * lset->nlabels);
	lset->labels[lset->nlabels-1].name = name;
	lset->labels[lset->nlabels-1].dg = dg;
	lset->labels[lset->nlabels-1].is_meta = is_meta;
	//printf("study label %s\n", name);
	return 0;
}

int	load_labels()
{
	printf("loading tree-node-labels\n");
	if(process_tdl_dgs_status("tree-node-label", study_label))
	{
		fprintf(stderr, "tree-node-labels: unable to load, bailing out.\n");
		exit(-1);
	}
	return 0;
}
