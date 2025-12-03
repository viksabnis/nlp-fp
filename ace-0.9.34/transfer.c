#define		_GNU_SOURCE
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>
#include	<signal.h>

extern int max_unpack_megabytes;
//#define	MAX_TRANSFER_CHUNKS	2560
#define	MAX_TRANSFER_CHUNKS	(max_unpack_megabytes)
//#define	DEBUG	printf
//#define	DEBUG(...)	do { } while(0)

#define	DEBUG(fmt...)	do { if(debug_transfer)printf(fmt); } while(0)

#include	"unicode.h"
#include	"transfer.h"
#include	"freeze.h"
#include	"chart.h"
#include	"dag.h"
#include	"type.h"
#include	"hash.h"
#include	"conf.h"
#include	"mrs.h"
#include	"profiler.h"
#include	"timeout.h"

extern struct type_hierarchy	*semi_th, *main_th;
extern int inhibit_vpm;

extern int	instloc_feature;
extern int reset_memorized_types;

int	debug_transfer = 0;

int	transfer_enable_qeq_bridge = 1;

char	*transfer_config_path = NULL;
struct profiler	*transfer_packing_profiler;

//int	saved_ntcopies = 0;
//struct tcopy	*saved_tcopies = NULL;

int	is_semarg_type(struct type	*x);
int equal_semarg_types(struct type	*x, struct type	*y);

void	check_pred_re(struct mrs_ep_desc	*ep, int	washout)
{
	struct dg	*pred = dg_hop(ep->dg, lookup_fname("PRED"));
	if(!pred)return;
	char	*tn = pred->xtype->name;
	if(tn[0] != '"')return;
	if(tn[1] != '~')return;
	// looks like we have a regular expression on our hands
	extern struct type	*strtype;
	if(washout)pred->type = pred->xtype = get_top();//strtype;
	char	*re = malloc(strlen(tn));
	strcpy(re, tn+2);
	re[strlen(tn+2)-1] = 0;
	ep->pred_re = towide(re);
	//printf("discovered pred RE '%S'\n", ep->pred_re);

	bzero(&ep->re,sizeof(ep->re));
	int	err = regcomp(&ep->re, ep->pred_re, REGEX_FLAGS);
	if(err)
	{
		wchar_t	buf[1024];
		regerror(err, &ep->re, buf, 1023);
		fprintf(stderr, "transfer-rule: while compiling `%S': %S\n", ep->pred_re, buf);
		exit(-1);
	}
}

// job: take all variable types in 'm' and map them forwards and then backwards through the VPM.
// without doing this, we will fail to unify against cases where that funky maneuver makes a rule variable type more general. yuck?
patch_variable_types(struct mrs	*m)
{
	int i;
	for(i=0;i<m->vlist.nvars;i++)
	{
		struct mrs_var	*v = m->vlist.vars[i];
		if(v->is_const)continue;
		char	*type = v->type;
		type = internal_to_external_var_type(type);
		type = external_to_internal_var_type(type);
		//printf("shifting '%s' to '%s'\n", v->type, type);
		v->type = type;
		if(v->dg)
		{
			struct type	*tp = lookup_type(type);
			v->dg->xtype = tp;
		}
	}
}

struct dg	*new_instloc(int onslab)
{
	struct type_hierarchy	*th = (semi_th && ALLOW_SEMI_MODE)?semi_th:main_th;
	if(onslab)
		return copy_dg(th->strtype->dg);
	else
	{
		struct dg	*d = calloc(sizeof(struct dg),1);
		d->xtype = d->type = th->strtype;
		return d;
	}
}

erase_instlocs(struct mrs	*m)
{
	int i;
	for(i=0;i<m->vlist.nvars;i++)
	{
		struct mrs_var	*v = m->vlist.vars[i];
		if(v->is_const)continue;
		if(v->dg)
		{
			struct dg	*il = dg_hop(v->dg, instloc_feature);
			//if(il)
			{
				// regardless of whether INSTLOC was present.
				// replace it with a brand-new *string* dg.
				add_dg_hop(v->dg, instloc_feature, new_instloc(1));
			}
		}
	}
}

int	process_transfer_rule_part(struct mrs_desc	*desc, struct transfer_rule	*tr, char	*feature)
{
	struct dg	*dg = dg_hop(tr->dg, lookup_fname(feature));
	if(!dg) { fprintf(stderr, "transfer rule '%s': no '%s' feature.\n", tr->name, feature); return -1; }
	desc->dg = dg;

	//printf("before processing rule '%s' part '%s' we have:\n", tr->name, feature);
	//print_dg(dg); printf("\n");

	if(semi_th && ALLOW_SEMI_MODE)
	{
		desc->mrs = cont_to_mrs(desc->dg);
		desc->mrs = slab_copy_mrs(desc->mrs, 0);
		// new-fangled system: convert our "internal" TFSes to SEMI-compliant TFSes
		semi_reformat_mrs(desc->mrs, 1);
	}
	else
	{
		extern int inhibit_vpm, invent_ltop;
		inhibit_vpm++;
		int old_invent_ltop = invent_ltop;
		invent_ltop = 0;
		desc->mrs = cont_to_mrs(desc->dg);
		desc->mrs = slab_copy_mrs(desc->mrs, 0);
		patch_variable_types(desc->mrs);
		invent_ltop = old_invent_ltop;
		inhibit_vpm--;
	}
	erase_instlocs(desc->mrs);	// kill off all reentrancies between INSTLOCs.
	// we assume rule writers won't try to make these. the 'qeq' grammar type
	// identifiers the hi INSTLOC with the lo INSTLOC as part of a conspiracy to make generation faster.
	// the INSTLOC hack field is reused in a different way in ACE's transfer rule implementation, and it is incompatible with that identification.

	// count and save pointers to the EPs
	struct dg	*list = dg_path(dg, rels_list_path);
	//struct dg	*rels = dg_hop(dg, lookup_fname("RELS"));
	//struct dg	*list = dg_hop(rels, lookup_fname("LIST"));
	while(list) { if(dg_hop(list, lookup_fname("FIRST")))desc->neps++; list = dg_hop(list, lookup_fname("REST")); }
	desc->eps = slab_alloc(sizeof(struct mrs_ep_desc)*desc->neps);
	desc->neps=0;
	//list = dg_hop(rels, lookup_fname("LIST"));
	list = dg_path(dg, rels_list_path);
	while(list)
	{
		struct dg	*epdg = dg_hop(list, lookup_fname("FIRST"));
		if(!epdg)break;
		desc->eps[desc->neps].pred_re = NULL;
		desc->eps[desc->neps].dg = epdg;
		check_pred_re(&desc->eps[desc->neps], 0);
		desc->neps++;
		list = dg_hop(list, lookup_fname("REST"));
		//printf("rule %s . %s %d = \n", tr->name, feature, desc->neps-1);
		//print_dg(epdg);printf("\n");
	}

	// count the HCONS
	list = dg_path(dg, hcons_list_path);
	while(list) { if(dg_hop(list, lookup_fname("FIRST")))desc->nhcons++; list = dg_hop(list, lookup_fname("REST")); }

	//printf("after processing rule '%s' part '%s' we have:\n", tr->name, feature);
	//print_dg(dg); printf("\n");

	return 0;
}

int	thaw_transfer_rule_part(struct mrs_desc	*desc, struct transfer_rule	*tr)
{
	int i;
	for(i=0;i<desc->neps;i++)
	{
		desc->eps[i].pred_re = NULL;
		check_pred_re(&desc->eps[i], 1);
	}
	return 0;
}

/*
void	process_saved_tcopy(struct transfer_rule	*r, struct tcopy	*c)
{
	int i;
	extern char	**fnames;
	printf("rule '%s' -- should record a copy from: ", r->name);
	for(i=0;i<c->frompathlen;i++)printf(" %s", fnames[c->frompath[i]]);
	printf("\n to: ");
	for(i=0;i<c->topathlen;i++)printf(" %s", fnames[c->topath[i]]);
	printf("\n");
	assert(!"not implemented yet");
	*/
	/*
	int minlen = 2 + rels_list_path.count;
	if(c->pathlen < minlen)goto badcopy;
	if(c->path[0] != lookup_fname("OUTPUT"))goto  badcopy;
	for(i=0;i<rels_list_path.count;i++)
		if(c->path[i+1] != rels_list_path.fnums[i])goto  badcopy;
	for(i=minlen-1;i<c->pathlen;i++)
		if(c->path[i] != lookup_fname("REST"))break;
	if(i != c->pathlen-1)goto badcopy;
	if(c->path[i] != lookup_fname("FIRST"))goto badcopy;

	int	argn = c->pathlen - minlen;
	//fprintf(stderr, "transfer rule `%s' has +copy+ on OUTPUT REL %d\n", r->name, argn);
	r->ncopy++;
	r->copy = realloc(r->copy, sizeof(int)*r->ncopy);
	r->copy[r->ncopy-1] = argn;

	return;
	badcopy:;
	fprintf(stderr, "transfer rule `%s': +copy+ can only appear at the top level of an EP structure in the OUTPUT.RELS list (see parameter `mrs-rels-list')\n", r->name);
	extern char	**fnames;
	for(i=0;i<c->pathlen;i++)
		fprintf(stderr, " %s", fnames[c->path[i]]);
	fprintf(stderr, "\n");
	exit(-1);*/
//}

void warn_about_equals(struct transfer_rule	*tr)
{
	static int	eqpath[5]={-1};
	struct dg	*eql = walk_dg(tr->dg, eqpath, "FLAGS", "EQUAL", 0);
	while(eql && dg_hop(eql, 1))
	{
		struct dg	*eq = dg_hop(eql, 1);
		eql = dg_hop(eql, 2);
		if(!is_semarg_type(eq->xtype))
		{
			fprintf(stderr, "WARNING: ACE only fully supports EQUAL constraints on `semarg' subtypes.\n");
			fprintf(stderr, "%s: EQUAL constraint on `%s' type\n", tr->name, eq->xtype->name);
		}
	}
}

struct transfer_rule	*dg_to_transfer_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	struct transfer_rule	*tr = calloc(sizeof(struct transfer_rule), 1);
	tr->name = strdup(name);
	static int flagspath[5] = {-1,-1};
	struct dg	*optdg = walk_dg(dg, flagspath, "FLAGS", "OPTIONAL", 0);
	tr->optional = optdg?(!strcmp(optdg->xtype->name, "+")):0;
	tr->dg = dg;
	tr->output_override = output_override;
	tr->disabled = 0;
	warn_about_equals(tr);
	/*int i;
	for(i=0;i<saved_ntcopies;i++)
	{
		process_saved_tcopy(tr, &saved_tcopies[i]);
		free(saved_tcopies[i].frompath);
		free(saved_tcopies[i].topath);
		saved_ntcopies = 0;
	}*/
	//printf("processing transfer rule '%s',  have:\n", name);
	//print_dg(dg);
	return tr;
}

struct transfer_rule	**transfer_rules;
int						ntransfer_rules;

struct transfer_rule	**trigger_rules;
int						ntrigger_rules;

struct transfer_rule	**fixup_rules;
int						nfixup_rules;

struct transfer_rule	**cleanup_rules;
int						ncleanup_rules;

int	study_trigger_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	//printf("loading trigger rule '%s'\n", name);
	//printf("	dg type '%s'\n", dg->xtype->name);
	int wellform_result = wellform(dg, "transfer rule");
	assert(wellform_result == 0);
	struct transfer_rule	*tr = dg_to_transfer_rule(name, dg, output_override);
	if(!tr)return -1;
	trigger_rules = realloc(trigger_rules, sizeof(struct transfer_rule*)*(ntrigger_rules+1));
	trigger_rules[ntrigger_rules++] = tr;
	return 0;
}

int	study_fixup_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	//printf("loading fixup rule '%s'\n", name);
	//printf("	dg type '%s'\n", dg->xtype->name);
	int wellform_result = wellform(dg, "transfer rule");
	assert(wellform_result == 0);
	struct transfer_rule	*tr = dg_to_transfer_rule(name, dg, output_override);
	if(!tr)return -1;
	fixup_rules = realloc(fixup_rules, sizeof(struct transfer_rule*)*(nfixup_rules+1));
	fixup_rules[nfixup_rules++] = tr;
	return 0;
}

int	study_cleanup_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	//printf("loading cleanup rule '%s'\n", name);
	//printf("	dg type '%s'\n", dg->xtype->name);
	int wellform_result = wellform(dg, "transfer rule");
	assert(wellform_result == 0);
	struct transfer_rule	*tr = dg_to_transfer_rule(name, dg, output_override);
	if(!tr)return -1;
	cleanup_rules = realloc(cleanup_rules, sizeof(struct transfer_rule*)*(ncleanup_rules+1));
	cleanup_rules[ncleanup_rules++] = tr;
	return 0;
}

int	study_transfer_rule(char	*name, struct dg	*dg, struct dg	*output_override)
{
	//printf("loading transfer rule '%s'\n", name);
	//printf("	dg type '%s'\n", dg->xtype->name);
	int wellform_result = wellform(dg, "transfer rule");
	assert(wellform_result == 0);
	struct transfer_rule	*tr = dg_to_transfer_rule(name, dg, output_override);
	if(!tr)return -1;
	transfer_rules = realloc(transfer_rules, sizeof(struct transfer_rule*)*(ntransfer_rules+1));
	transfer_rules[ntransfer_rules++] = tr;
	return 0;
}

int	load_transfer_rules()
{
	assert(g_transfer != 0);
	if(process_mtr_status("rule", study_transfer_rule))
	{
		fprintf(stderr, "transfer rules: unable to load rules, bailing out.\n");
		exit(-1);
	}
	return 0;
}

struct transfer_freezer
{
	struct transfer_rule	**trigger_rules;
	int						ntrigger_rules;
	struct transfer_rule	**fixup_rules;
	int						nfixup_rules;
	struct transfer_rule	**cleanup_rules;
	int						ncleanup_rules;
	struct transfer_rule	**idiom_rules;
	int						nidiom_rules;
	char					*non_idiom_root;
	struct transfer_rule	**transfer_rules;
	int						ntransfer_rules;
};

extern struct transfer_rule	**idiom_rules;
extern int						nidiom_rules;

struct transfer_rule	*freeze_transfer_rule(struct transfer_rule	*tr)
{
	struct transfer_rule	*fr = slab_alloc(sizeof(*fr));
	bzero(fr, sizeof(*fr));
	fr->name = freeze_string(tr->name);
	fr->dg = freeze_dg(tr->dg);
	fr->output_override = freeze_dg(tr->output_override);
	fr->optional = tr->optional;
	fr->disabled = 0;
	freeze_transfer_rule_more(fr);
	//fr->ncopy = tr->ncopy;
	//fr->copy = freeze_block(tr->copy, sizeof(int)*fr->ncopy);
	return fr;
}

void	*freeze_transfer()
{
	int	i;
	struct transfer_freezer	*fz = slab_alloc(sizeof(*fz));

	fz->trigger_rules = slab_alloc(sizeof(struct transfer_rule*)*ntrigger_rules);
	for(i=0;i<ntrigger_rules;i++)
		fz->trigger_rules[i] = freeze_transfer_rule(trigger_rules[i]);
	fz->ntrigger_rules = ntrigger_rules;

	fz->fixup_rules = slab_alloc(sizeof(struct transfer_rule*)*nfixup_rules);
	for(i=0;i<nfixup_rules;i++)
		fz->fixup_rules[i] = freeze_transfer_rule(fixup_rules[i]);
	fz->nfixup_rules = nfixup_rules;

	fz->cleanup_rules = slab_alloc(sizeof(struct transfer_rule*)*ncleanup_rules);
	for(i=0;i<ncleanup_rules;i++)
		fz->cleanup_rules[i] = freeze_transfer_rule(cleanup_rules[i]);
	fz->ncleanup_rules = ncleanup_rules;

	fz->idiom_rules = slab_alloc(sizeof(struct transfer_rule*)*nidiom_rules);
	for(i=0;i<nidiom_rules;i++)
		fz->idiom_rules[i] = freeze_transfer_rule(idiom_rules[i]);
	fz->nidiom_rules = nidiom_rules;
	if(non_idiom_root)fz->non_idiom_root = freeze_string(non_idiom_root);
	else fz->non_idiom_root = NULL;
	//printf("freezer: %s\n", fz->non_idiom_root);

	fz->transfer_rules = slab_alloc(sizeof(struct transfer_rule*)*ntransfer_rules);
	for(i=0;i<ntransfer_rules;i++)
		fz->transfer_rules[i] = freeze_transfer_rule(transfer_rules[i]);
	fz->ntransfer_rules = ntransfer_rules;

	return fz;
}

thaw_transfer_rule(struct transfer_rule	*tr)
{
	//printf("thaw %s\n", tr->name);
	//print_dg(tr->dg);
	//printf("\n");
	thaw_transfer_rule_part(&tr->input, tr);
	thaw_transfer_rule_part(&tr->context, tr);
	thaw_transfer_rule_part(&tr->filter, tr);
	thaw_transfer_rule_part(&tr->output, tr);
}

int	freeze_transfer_rule_more(struct transfer_rule	*tr)
{
	//printf("freezing rule '%s'\n", tr->name);
	//print_dg(tr->dg);
	//printf("\n\n");

	if(0 != process_transfer_rule_part(&tr->input, tr, "INPUT"))
		return -1;
	if(0 != process_transfer_rule_part(&tr->context, tr, "CONTEXT"))
		return -1;
	if(0 != process_transfer_rule_part(&tr->filter, tr, "FILTER"))
		return -1;
	if(0 != process_transfer_rule_part(&tr->output, tr, "OUTPUT"))
		return -1;

	tr->eq = slab_alloc(sizeof(struct dg*)*10);
	tr->ss = slab_alloc(sizeof(struct dg*)*10);
	bzero(tr->eq, sizeof(struct dg*)*10);
	bzero(tr->ss, sizeof(struct dg*)*10);
	tr->neq = tr->nss = 0;
	static int	eqpath[5]={-1}, sspath[5]={-1};
	struct dg	*eql = walk_dg(tr->dg, eqpath, "FLAGS", "EQUAL", 0);
	struct dg	*ssl = walk_dg(tr->dg, sspath, "FLAGS", "SUBSUME", 0);
	//printf("eql = \n");
	//print_dg(eql); printf("\n");
	while(eql && dg_hop(eql, 1))
	{
		assert(tr->neq < 10);
		tr->eq[tr->neq++] = dg_hop(eql, 1);
		eql = dg_hop(eql, 2);
	}
	while(ssl && dg_hop(ssl, 1))
	{
		assert(tr->nss < 10);
		tr->ss[tr->nss++] = dg_hop(ssl, 1);
		ssl = dg_hop(ssl, 2);
	}
	//printf("rule %s has %d EQs and %d SSs\n", tr->name, tr->neq, tr->nss);

	/*tr->output_copy_map = calloc(1, tr->output.neps);
	int i;
	for(i=0;i<tr->ncopy;i++)
	{
		assert(tr->copy[i] >= 0 && tr->copy[i] < tr->output.neps);
		tr->output_copy_map[tr->copy[i]] = 1;
	}*/

	return 0;
}

void	recover_transfer(void	*transfer)
{
	int	i;
	struct transfer_freezer	*fz = transfer;
	/*printf("sizeof mrs = %d\n", sizeof(struct mrs));
	printf("sizeof mrs_desc = %d\n", sizeof(struct mrs_desc));
	printf("sizeof mrs_ep_desc = %d\n", sizeof(struct mrs_ep_desc));
	printf("sizeof regex_t = %d\n", sizeof(regex_t));*/
	clear_slab();
	if(g_mode == GENERATING)
	{
		trigger_rules = fz->trigger_rules;
		ntrigger_rules = fz->ntrigger_rules;
		for(i=0;i<ntrigger_rules;i++)
			thaw_transfer_rule(trigger_rules[i]);
		//fprintf(stderr, "NOTE: thawed %d trigger rules.\n", ntrigger_rules);
		fixup_rules = fz->fixup_rules;
		nfixup_rules = fz->nfixup_rules;
		for(i=0;i<nfixup_rules;i++)
			thaw_transfer_rule(fixup_rules[i]);
	}
	if(g_transfer)
	{
		transfer_rules = fz->transfer_rules;
		ntransfer_rules = fz->ntransfer_rules;
		for(i=0;i<ntransfer_rules;i++)
			thaw_transfer_rule(transfer_rules[i]);
	}
	idiom_rules = fz->idiom_rules;
	nidiom_rules = fz->nidiom_rules;
	for(i=0;i<nidiom_rules;i++)
		thaw_transfer_rule(idiom_rules[i]);
	non_idiom_root = fz->non_idiom_root;
	cleanup_rules = fz->cleanup_rules;
	ncleanup_rules = fz->ncleanup_rules;
	for(i=0;i<ncleanup_rules;i++)
		thaw_transfer_rule(cleanup_rules[i]);
	clear_slab();
	clear_mrs();
	//printf("recover: %s\n", non_idiom_root);

	if(g_transfer && transfer_config_path)
	{
		FILE	*f = fopen(transfer_config_path,"r");
		if(!f){perror(transfer_config_path);exit(-1);}
		char	line[1024];
		for(i=0;i<ntransfer_rules;i++)
			transfer_rules[i]->disabled = 1;
		while(fgets(line,1023,f))
		{
			char	*name = trim_string(line);
			for(i=0;i<ntransfer_rules;i++)
			{
				if(!strcmp(name,transfer_rules[i]->name))
					transfer_rules[i]->disabled = 0;
			}
		}
		fclose(f);
	}
}

struct mrs_ep_desc	place_in_transfer_rule(struct transfer_rule	*tr, int	pl)
{
	if(pl < tr->input.neps)return tr->input.eps[pl];
	pl -= tr->input.neps;
	if(pl < tr->context.neps)return tr->context.eps[pl];
	pl -= tr->context.neps;
	if(pl < tr->filter.neps)return tr->filter.eps[pl];
	fprintf(stderr, "asked for nonexistant place in transfer rule '%s'\n", tr->name);
	exit(-1);
}

char	*pred_for_place_in_transfer_rule(struct transfer_rule	*tr, int	pl)
{
	if(pl < tr->input.neps)return tr->input.mrs->rels[pl].pred;
	pl -= tr->input.neps;
	if(pl < tr->context.neps)return tr->context.mrs->rels[pl].pred;
	pl -= tr->context.neps;
	if(pl < tr->filter.neps)return tr->filter.mrs->rels[pl].pred;
	fprintf(stderr, "asked for nonexistant predplace in transfer rule '%s'\n", tr->name);
	exit(-1);
}

int	is_semarg_type(struct type	*x)
{
	static struct type *semarg = NULL;
	if(!semarg || reset_memorized_types)assert(semarg = lookup_type(semarg_type));
	if(x->name[0]=='"')return 0;
	return descendent_of(x->tnum, semarg);
}

int equal_semarg_types(struct type	*x, struct type	*y)
{
	if(semi_th && ALLOW_SEMI_MODE)
	{
		return (x==y)?1:0;
	}
	else
	{
		DEBUG("eq-semarg-types: %s =? %s\n", x->name, y->name);
		if(x==y)return 1;
		char	*semi_x = internal_to_external_var_type(x->name);
		char	*semi_y = internal_to_external_var_type(y->name);
		DEBUG("compare %s [%s] to %s [%s]\n", semi_x, x->name, semi_y, y->name);
		return strcmp(semi_x, semi_y)?0:1;
	}
}

struct type	*semi_find_type(char	*name)
{
	extern struct type_hierarchy	*semi_th;
	assert(semi_th != NULL);
	return hash_find(semi_th->thash, name);
}

int subsume_semarg_types(struct type	*x, struct type	*y)
{
	if(semi_th && ALLOW_SEMI_MODE)
	{
		return (descendent_of(y->tnum, x))?1:0;
	}
	else
	{
		DEBUG("ss-semarg-types: %s >? %s\n", x->name, y->name);
		if(x==y)return 1;
		char	*semi_x = internal_to_external_var_type(x->name);
		char	*semi_y = internal_to_external_var_type(y->name);

		int r1;
		if(semi_th)
		{
			// method 1
			struct type	*sx = semi_find_type(semi_x);
			struct type	*sy = semi_find_type(semi_y);
			if(!(sx && sy))
			{
				//fprintf(stderr, "ERROR: checking whether '%s' subsumes '%s', but one of those didn't exist in the SEMI\n", semi_x, semi_y);
				//exit(-1);
				r1 = -1;
			}
			else r1 = descendent_of(sy->tnum, sx)?1:0;
		}

		// method 2
		char	*local_x = external_to_internal_var_type(semi_x);
		char	*local_y = external_to_internal_var_type(semi_y);
		// scared yet?
		DEBUG("compare %s [%s [%s]] to %s [%s [%s]]\n", local_x, semi_x, x->name, local_y, semi_y, y->name);
		struct type	*tx = lookup_type(local_x);
		struct type	*ty = lookup_type(local_y);
		assert(tx && ty);
		int	r2 = descendent_of(ty->tnum, tx)?1:0;
		if(r1 == -1)r2 = r1;

		if(semi_th)assert(r1 == r2);
		//printf("methods agree for '%s >? %s'\n", x->name, y->name);
		return r2;
	}
}

int	nfailed_transfer_unifies, nsuccessful_transfer_unifies;

void	show_transfer_counts() __attribute__ ((destructor));
void	show_transfer_counts()
{
	if(g_mode == GENERATING)
		fprintf(stderr, "NOTE: transfer did %d successful unifies and %d failed ones\n", nsuccessful_transfer_unifies, nfailed_transfer_unifies);
}

int	any_carc_points_to(struct mrs	*m, int	*align, int	count, struct dg	*to)
{
	int i, j;
	for(i=0;i<count;i++)
	{
		struct mrs_ep	*ep = m->rels + align[i];
		struct dg	*d = ep->dg;
		extern unsigned int generation;
		//printf("does EP `%s' (align %d) have %p as a carc?\n", ep->pred, i, to);
		if(d->gen != generation)continue;
		for(j=0;j<d->ncarcs;j++)
			if(dereference_dg(d->carcs[j].dest) == to)return 1;
	}
	return 0;
}

struct mrs_hcons	find_hc(struct transfer_rule	*tr, int	idx)
{
	if(idx < tr->input.mrs->nhcons)
		return tr->input.mrs->hcons[idx];
	idx -= tr->input.mrs->nhcons;
	if(idx < tr->context.mrs->nhcons)
		return tr->context.mrs->hcons[idx];
	idx -= tr->context.mrs->nhcons;
	if(idx < tr->filter.mrs->nhcons)
		return tr->filter.mrs->hcons[idx];
	idx -= tr->filter.mrs->nhcons;
	assert(!"not reached: no such HCONS");
}

int	unifiable_hcons(struct mrs_hcons	x, struct mrs_hcons	y)
{
	// don't actually perform any unifications; we have a fragile temporary DAG already.
	// determine whether x and y say the same thing.
	if(dereference_dg(x.hi->dg) != dereference_dg(y.hi->dg))return 0;
	if(dereference_dg(x.lo->dg) != dereference_dg(y.lo->dg))return 0;
	return 1;
}

int satisfiable_hconses(struct transfer_rule	*tr, int idx, int	need, struct mrs	*m, char	*usedmap)
{
	if(idx == need)return 1;

	struct mrs_hcons	hc = find_hc(tr, idx);
	int i;
	for(i=0;i<m->nhcons;i++)
		if(!usedmap[i])
		{
			if(!unifiable_hcons(hc, m->hcons[i]))
				continue;
			usedmap[i] = 1;
			if(satisfiable_hconses(tr, idx+1, need, m, usedmap))
				return 1;
			usedmap[i] = 0;
		}
	return 0;
}

int	transfer_qeq_bridge(struct mrs	*m, struct mrs_var	*x, struct mrs_var	*y)
{
	int i;
	if(!transfer_enable_qeq_bridge)return 0;
	for(i=0;i<m->nhcons;i++)
		if(m->hcons[i].type == hcons_qeq)
		{
			if(m->hcons[i].hi == x && m->hcons[i].lo == y)return 1;
			if(m->hcons[i].hi == y && m->hcons[i].lo == x)return 1;
		}
	return 0;
}

int	transfer_missing_roles(struct mrs_ep_desc	*rule, struct mrs_ep	*ep)
{
	int	i;
	for(i=0;i<rule->dg->narcs;i++)
	{
		extern char	*ep_drop;
		extern char	**fnames;
		if(ep_drop[rule->dg->label[i]])continue;
		char	*label = fnames[rule->dg->label[i]];
		if(!strcmp(label, "PRED"))continue;
		if(!strcmp(label, "LBL"))continue;
		if(!mrs_find_ep_role(ep, label))
		{
			//printf("CAUGHT: %s has no %s\n", ep->pred, label);
			return 1;
		}
	}
	return 0;
}

int	test_transfer_alignment(struct transfer_rule	*tr, struct mrs	*mrs, int	count, int	*align, int	total, int	hccount, int	*hcalignment, int	hctotal, int is_filter)
{
	int	i;
	for(i=0;i<count;i++)
	{
		static int	pred_fnum = -1, arg0_fnum=-1;
		if(pred_fnum == -1)pred_fnum = lookup_fname("PRED");
		if(arg0_fnum == -1)arg0_fnum = lookup_fname("ARG0");
		struct mrs_ep	*ep = &mrs->rels[align[i]];
		char	*ep_raw_pred = ep->pred;
		struct dg	*ep_p = dg_hop(ep->dg, pred_fnum);
		struct dg	*ep_a0 = dg_hop(ep->dg, arg0_fnum);
		struct mrs_ep_desc	de = place_in_transfer_rule(tr, i);
		char	*de_raw_pred = pred_for_place_in_transfer_rule(tr, i);
		struct dg	*de_p = dg_hop(de.dg, pred_fnum);
		struct dg	*de_a0 = dg_hop(de.dg, arg0_fnum);
		if(de_p && ep_p)
		{
			struct type	*de_pred = de_p->xtype;
			struct type	*ep_pred = ep_p->xtype;
			if(!glb(ep_pred, de_pred))
			{
				DEBUG("wrong pred: %s vs %s\n", de_pred->name, ep_pred->name);
				// most common failure path
				return -1;
			}
			extern struct type_hierarchy	*semi_th;
			struct type	*semi_de_pred = th_lookup_type(semi_th, de_raw_pred);
			struct type	*semi_ep_pred = th_lookup_type(semi_th, ep_raw_pred);
			if(!de.pred_re || !semi_ep_pred)
			{
				if(!semi_de_pred || !semi_ep_pred || !glb(semi_de_pred, semi_ep_pred))
				{
					DEBUG("wrong pred (sem-i): %s [%p] vs %s [%p]\n", de_raw_pred, semi_de_pred, ep_raw_pred, semi_ep_pred);
					return -1;
				}
			}
			if(de.pred_re)
			{
				//wchar_t	*wide = towide(ep_pred->name);
				wchar_t	*wide = towide(ep_raw_pred);
				DEBUG("need to see if '%S' and '%S' are RE-compatible\n", wide, de.pred_re);
				regmatch_t	mat;
				int	res = regexec(&de.re, wide, 1, &mat, 0);
				free(wide);
				if(res != 0)
				{
					DEBUG("nope.\n");
					return -1;
				}
				DEBUG("yup!\n");
			}
		}
		if(de_a0 && ep_a0)
		{
			if(!glb(de_a0->xtype, ep_a0->xtype))
			{
				return -1;
			}
		}
	}
	setup_tmp();

	// guarantee that the rule nodes get forwarded to the EP nodes,
	// rather than forwarding EP nodes to rule nodes.
	extern int allow_unify_swapping;
	allow_unify_swapping = 0;
	// note: if the rule has multiple re-entrancies for an EQUAL or SUBSUME node,
	// we need to do something slightly cleverer than what happens below.
	// right now, we see whether tr->eq[i]->xtype is compatible with
	// dereference_dg(tr->eq[i])->xtype.
	// i *think* in the case where there are multiple EP nodes that get
	// unified to the same EQ node (or SS node), we just have to walk
	// down the forwarding chain from tr->eq[i] one at a time and check
	// that each one's xtype is compatible with the original xtype.
	// if that turns out not to work... as a last resort, we could
	// recurse on the input EP's dag and find all nodes that are forwarded
	// to the same place as tr->eq[i]... but that sounds slow.
	// nov-8-2011: the forwarding chain idea won't work, because
	// we want to fail the SS or EQ test in cases where there was no
	// corresponding node on the input.  since these are only used
	// for variable nodes, we now use a variant of the "slow" idea
	// that just looks at the input EPs' top level dag nodes' ->carcs slots.
	// note that we *still* don't support the case where several input nodes unify to the EQ node...
	// we need to implement the forwarding-chain-walker.
	for(i=0;i<count;i++)
	{
		struct mrs_ep	*ep = &mrs->rels[align[i]];
		struct mrs_ep_desc	de = place_in_transfer_rule(tr, i);
		// in general, transfer rules *are* allowed to match when a specified role isn't present on the target EP...
		// when SUBSUME or EQUAL are used, then the role must actually be present.
		//if(transfer_missing_roles(&de, ep)) { forget_tmp(); allow_unify_swapping = 1; return -1; }
		//if(0 != unify_dg_tmp(ep->dg, de.dg, -1))
		if(0 != unify_dg_tmp(de.dg, ep->dg, -1))
		{
			//printf("TRANSFER: ");
			//unify_backtrace();

			forget_tmp();
			//printf("rule ep:\n");
			//print_dg(de.dg);printf("\n");
			//printf("input ep:\n");
			//print_dg(ep->dg);printf("\n");
			nfailed_transfer_unifies++;
			allow_unify_swapping = 1;
			return -1;
		}
		nsuccessful_transfer_unifies++;
	}
	// also unify the input MRS's LTOP and INDEX into the INPUT and CONTEXT mrs descriptions' HOOKs.
	int unify_vars(struct mrs_var	*vin, struct mrs_var	*vrule)
	{
		if(!vin || !vin->dg || !vrule || !vrule->dg)return 0;
		if(0 != unify_dg_tmp(vrule->dg, vin->dg, -1))
		{
			forget_tmp();
			allow_unify_swapping = 1;
			return -1;
		}
		return 0;
	}
	/*printf("trying to unify hooks\n");
	printf("input ltop = ");if(mrs->ltop)print_within_generation(mrs->ltop->dg);printf("\n");
	printf("rule input ltop = ");if(tr->input.mrs->ltop)print_within_generation(tr->input.mrs->ltop->dg);printf("\n");
	printf("rule context ltop = ");if(tr->context.mrs->ltop)print_within_generation(tr->context.mrs->ltop->dg);printf("\n");*/
	if(unify_vars(mrs->ltop, tr->input.mrs->ltop))return -1;
	if(unify_vars(mrs->ltop, tr->context.mrs->ltop))return -1;
	if(unify_vars(mrs->index, tr->input.mrs->index))return -1;
	if(unify_vars(mrs->index, tr->context.mrs->index))return -1;
	/*printf("after unifying hooks:\n");
	printf("input ltop = ");if(mrs->ltop)print_within_generation(mrs->ltop->dg);printf("\n");
	printf("rule input ltop = ");if(tr->input.mrs->ltop)print_within_generation(tr->input.mrs->ltop->dg);printf("\n");
	printf("rule context ltop = ");if(tr->context.mrs->ltop)print_within_generation(tr->context.mrs->ltop->dg);printf("\n");*/

	for(i=0;i<hccount;i++)
	{
		struct mrs_hcons	hrule = find_hc(tr, i);
		struct mrs_hcons	hin = mrs->hcons[hcalignment[i]];
		//if(!unifiable_hcons(hrule, hin))return -1;
		if(hrule.type != hin.type) { allow_unify_swapping = 1; return -1; }
		if(unify_vars(hin.hi, hrule.hi))return -1;
		if(unify_vars(hin.lo, hrule.lo))return -1;
	}
	allow_unify_swapping = 1;

	struct dg	*old_var_dg[mrs->vlist.nvars];
	// get the location of every old var in the unified mrs/rule dag conglomeration
	for(i=0;i<mrs->vlist.nvars;i++)
		old_var_dg[i] = dereference_dg(mrs->vlist.vars[i]->dg);

	// verify that no two variables dereference to the same DG;
	// we used to use INSTLOCs to cause unification failures in such cases,
	// but it's expensive to allocate so many INSTLOCs...
	int j;
	for(i=0;i<mrs->vlist.nvars;i++)
		for(j=0;j<i;j++)
			if(!mrs->vlist.vars[i]->is_const || !mrs->vlist.vars[j]->is_const)
				if(old_var_dg[i] == old_var_dg[j] && !transfer_qeq_bridge(mrs, mrs->vlist.vars[i], mrs->vlist.vars[j]))
				{
					//printf("match failed [%s]: %s%d & %s%d\n", tr->name, mrs->vlist.vars[i]->type, i, mrs->vlist.vars[j]->type, j);
					forget_tmp();
					return -1;	// failure; two distinct input variables got unified together
				}

	if(count == total && hccount == hctotal)
	{
		// unification is complete; test the EQUAL and SUBSUME conditions
		extern unsigned int	generation;
		for(i=0;i<tr->neq;i++)
		{
			if(tr->eq[i]->gen != generation)
			{
				//printf("variable with EQ condition untouched; could not be present on matching MRS; fail!\n");
				forget_tmp();
				return -1;
			}
			// we require that the *original* type of the node that matched tr->eq[i]
			// is equal to the *original* type of tr->eq[i] itself
			struct dg	*ep_original = dereference_dg(tr->eq[i]);
			struct type	*t_ep_original = ep_original->xtype;
			struct type	*t_eq_original = tr->eq[i]->xtype;
			if(equal_semarg_types(t_ep_original, t_eq_original) == 0)
			{
				DEBUG("failed EQ test: should have been type '%s'; actually '%s'\n", tr->eq[i]->xtype->name, t_ep_original->name);
				forget_tmp();
				return -1;
			}
			if(any_carc_points_to(mrs, align, count, ep_original))
			{
				DEBUG("fail EQ test: one of the inputs didn't have this path at all\n");
				forget_tmp();
				return -1;
			}
			DEBUG("passed EQ test %d for rule '%s'\n", i, tr->name);
		}
		for(i=0;i<tr->nss;i++)
		{
			if(tr->ss[i]->gen != generation)
			{
				//printf("variable with SS condition untouched; could not be present on matching MRS; fail!\n");
				forget_tmp();
				return -1;
			}
			struct dg	*ep_original = dereference_dg(tr->ss[i]);
			struct type	*t_ep_original = ep_original->xtype;
			struct type	*t_ss_original = tr->ss[i]->xtype;
			DEBUG("SS test: %s >? %s\n", t_ss_original->name, t_ep_original->name);
			if(subsume_semarg_types(t_ss_original, t_ep_original) == 0)
			//if(!descendent_of(t_ep_original->tnum, t_ss_original))
			{
				DEBUG("failed SS test\n");
				forget_tmp();
				return -1;
			}
			if(any_carc_points_to(mrs, align, count, ep_original))
			{
				DEBUG("fail SS test: one of the inputs didn't have this path at all\n");
				forget_tmp();
				return -1;
			}
		}
		/*
		// ensure that CONTEXT and FILTER HCONS specifications are satisfiable.
		char	used_hcons[mrs->nhcons];
		bzero(used_hcons, sizeof(used_hcons));
		int	nhc = tr->input.mrs->nhcons + tr->context.mrs->nhcons;
		if(is_filter)nhc += tr->filter.mrs->nhcons;
		if(satisfiable_hconses(tr, 0, nhc, mrs, used_hcons) == 0)
		{
			DEBUG("failed HCONS test\n");
			forget_tmp();
			return -1;
		}
		*/

		// don't forget_tmp() if we succeeded with the match and it was a complete match.
		return 0;
	}
	// succeeded with the match, but it was incomplete.
	forget_tmp();
	return 0;
}

int	align_transfer_rule0(struct transfer_rule	*tr, struct mrs	*mrs, int	place, int	total, int	*alignment, int	hcplace, int	hctotal, int	*hcalignment, int	(*callback)(int	*alignment, int	*hcalignment), int	is_filter)
{
	int	i;
	if(place == total && hcplace == hctotal && !is_filter)
	{
		/*printf("produced a complete alignment for rule '%s' [%d input, %d ctx]: ", tr->name, tr->input.neps, tr->context.neps);
		print_dg(tr->dg);
		for(i=0;i<total;i++)
			printf(" %d [%s]", alignment[i], mrs->rels[alignment[i]].pred);
		printf("\n");*/
		if(tr->filter.neps || tr->filter.nhcons)
		{
			// see if we can match the filter portion... uh oh!
			forget_tmp();
			int	did_filter = 0;
			int	filtercb(int	*filtalign, int *filthcalign) { did_filter = 1; return 1; }	// return of 1 indicates we don't care about more alignments; one is enough to say it was filtered.
			align_transfer_rule0(tr, mrs, place, tr->input.neps + tr->context.neps + tr->filter.neps, alignment, hcplace, tr->input.nhcons + tr->context.nhcons + tr->filter.nhcons, hcalignment, filtercb, 1);
			forget_tmp();
			if(did_filter)
			{
				//printf("FILTER fired for rule '%s'.\n", tr->name);
				return 0;
			}
			// if the rule has output, we need to reconstruct the temporary unifications, now that we've verified there were no filter firings :-/

			/*
				// it is tempting to add an 'if' clause here to avoid having to replay these unifications when there appears to be no output (e.g. just deleting an EP, or triggering a vacuous lexeme, etc).
				// but...
				// trigger rules with specialization constraints can rely on unifications to be present, and...
				// transfer rules even with no EP or HCONS output can (in theory ... we don't implement it, do we? maybe.) change the HOOK-level features of the output mrs.
			if(tr->output.neps || tr->output.nhcons)
			*/
			assert(0 == test_transfer_alignment(tr, mrs, place, alignment, total, hcplace, hcalignment, hctotal, is_filter));
		}
		int rv = callback(alignment, hcalignment);
		forget_tmp();
		return rv;
	}
	else if(place == total && hcplace == hctotal)
	{
		// FILTER callback
		int rv = callback(alignment, hcalignment);
		forget_tmp();
		return rv;
	}

	if(place < total)
	{
		// try to align 'place' to an unused EP in 'mrs'
		for(i=0;i<mrs->nrels;i++)
		{
			if(mrs->rels[i].active)continue;
			alignment[place] = i;
			DEBUG("how about rule %s spot %d for '%s'?\n", tr->name, place, mrs->rels[i].pred);
			if(0 != test_transfer_alignment(tr, mrs, place+1, alignment, total/*tr->input.neps + tr->context.neps*/, hcplace, hcalignment, hctotal, is_filter))
				continue;
			DEBUG("passed test.\n");
			mrs->rels[i].active = 1;
			int rv = align_transfer_rule0(tr, mrs, place+1, total, alignment, hcplace, hctotal, hcalignment, callback, is_filter);
			mrs->rels[i].active = 0;
			if(rv != 0)return rv;
		}
		return 0;
	}
	else
	{
		// try to align 'hcplace' to an unused HC in 'mrs'
		for(i=0;i<mrs->nhcons;i++)
		{
			if(mrs->hcons[i].active)continue;
			hcalignment[hcplace] = i;
			DEBUG("how about rule %s spot %d for HC %d?\n", tr->name, hcplace, i);
			if(0 != test_transfer_alignment(tr, mrs, place, alignment, total/*tr->input.neps + tr->context.neps*/, hcplace+1, hcalignment, hctotal, is_filter))
				continue;
			DEBUG("passed test.\n");
			mrs->hcons[i].active = 1;
			int rv = align_transfer_rule0(tr, mrs, place, total, alignment, hcplace+1, hctotal, hcalignment, callback, is_filter);
			mrs->hcons[i].active = 0;
			if(rv != 0)return rv;
		}
		return 0;
	}
}

int	align_transfer_rule(struct transfer_rule	*tr, struct mrs	*mrs, int	(*callback)(int	*alignment, int	*hcalignment))
{
	int	i;
	for(i=0;i<mrs->nrels;i++)
		mrs->rels[i].active = 0;
	for(i=0;i<mrs->nhcons;i++)
		mrs->hcons[i].active = 0;

	DEBUG("trying to align %s\n", tr->name);
	int	nplaces = tr->input.neps + tr->context.neps + tr->filter.neps;
	int	alignment[nplaces];
	int	nhcplaces = tr->input.nhcons + tr->context.nhcons + tr->filter.nhcons;
	int	hcalignment[nhcplaces];
	return align_transfer_rule0(tr, mrs, 0, tr->input.neps + tr->context.neps, alignment, 0, tr->input.nhcons + tr->context.nhcons, hcalignment, callback, 0);
}

void	activate_trigger_rules(struct mrs	*mrsin, void	trigger(char	*lexid, struct dg	*cons))
{
	int	i;
	/*printf("input MRS var DGs:\n");
	for(i=0;i<mrsin->vlist.nvars;i++)
	{
		struct mrs_var	*v = mrsin->vlist.vars[i];
		printf("%s%d: ", v->type, v->vnum);
		print_dg(v->dg);
		printf("\n");
	}*/

	int	use_trigger_constraints = feature_exists("TRIGGER-CONSTRAINT");
	//printf("use_trigger_constraints = %d\n", use_trigger_constraints);

	// note: generate() has already built the ep->dg's for each input relation

	if(semi_th && ALLOW_SEMI_MODE)
		semi_reformat_mrs(mrsin, 0);

	for(i=0;i<ntrigger_rules;i++)
	{
		int	found_alignment(int	*alignment, int	*hcalignment)
		{
			struct dg	*flags = dg_hop(trigger_rules[i]->dg, lookup_fname("FLAGS"));
			struct dg	*trig = dg_hop(flags, lookup_fname("TRIGGER"));
			struct dg	*trigcons = NULL;
			if(use_trigger_constraints)
				trigcons = dg_hop(flags, lookup_fname("TRIGGER-CONSTRAINT"));
			char	lexid[256];
			sprintf(lexid, "%.*s", (int)strlen(trig->xtype->name)-2, trig->xtype->name+1);
			if(temporary_expedient(lexid))
			{
				//printf("not triggering '%s' via '%s' because it is disabled for generation\n", lexid, trigger_rules[i]->name);
				//return;
			}
			else
			{
				char	*aligned_on = "<none>";
				if(trigger_rules[i]->input.neps + trigger_rules[i]->context.neps > 0)
					aligned_on = mrsin->rels[alignment[0]].pred;
				//printf("triggering '%s' via '%s', aligned on %s\n", lexid, trigger_rules[i]->name, aligned_on);
				if(trigcons)
				{
					struct dg	*dg = copy_dg_with_comp_arcs(trigcons);
					setup_tmp();	// prevent it from being forgotten when we return
					trigcons = dg;
					//printf("triggering '%s' via '%s', and TRIGGER-CONSTRAINT is:\n", lexid, trigger_rules[i]->name);
					//print_dg(dg);printf("\n");
				}
				trigger(lexid, trigcons);
			}
			if(trigcons)return 0;	// might find more alignments with different constraints
			else return 1;	// don't care to hear about more alignments; it's triggered.
		}
		align_transfer_rule(trigger_rules[i], mrsin, found_alignment);
	}
}

void debug_run_one_trigger_rule(struct mrs	*m, char	*rname, int detail)
{
	int i, j;
	for(i=0;i<ntrigger_rules;i++)
		if(!strcasecmp(trigger_rules[i]->name, rname))break;
	if(i==ntrigger_rules)
	{
		fprintf(stderr, "no such trigger rule `%s'\n", rname);
		return;
	}
	struct transfer_rule	*R = trigger_rules[i];

	int	found_alignment(int	*alignment, int	*hcalignment)
	{
		struct dg	*flags = dg_hop(R->dg, lookup_fname("FLAGS"));
		struct dg	*trig = dg_hop(flags, lookup_fname("TRIGGER"));
		char	lexid[256];
		sprintf(lexid, "%.*s", (int)strlen(trig->xtype->name)-2, trig->xtype->name+1);
		printf("rule %s matches EPs:", R->name);
		for(j=0;j<R->input.neps + R->context.neps;j++)
			printf(" %s", m->rels[alignment[j]].pred);
		printf("    -> %s\n", lexid);
		if(temporary_expedient(lexid))
			printf("  but that's on the temporary expedient, so skipping!\n");
	}
	debug_transfer = detail;
	align_transfer_rule(R, m, found_alignment);
	debug_transfer = 0;
}

void	debug_run_trigger_rules(struct mrs	*m)
{
	int	i;
	for(i=0;i<ntrigger_rules;i++)
		debug_run_one_trigger_rule(m, trigger_rules[i]->name, 0);
}



int	skolem_counter;
struct type	*transfer_next_skolem_constant()
{
	assert(default_type_hierarchy()->nstrings > skolem_counter);
	return default_type_hierarchy()->strings[skolem_counter++];
}

void destroy_existing_instlocs(struct dg	*dg)
{
	if(!dg)return;
	int	i;
	dg = p_dereference_dg(dg);
	struct dg	**arcs = DARCS(dg);
	static int instloc = -1;
	if(instloc ==-1)instloc = lookup_fname("INSTLOC");

	for(i=0;i<dg->narcs;i++)
	{
		if(dg->label[i] == instloc)
		{
			struct type	*t = arcs[i]->xtype;
			if(t->name[0]=='"')
			{
				struct dg	*iloc = dereference_dg(arcs[i]);
				iloc->xtype = iloc->type = default_type_hierarchy()->strtype;
			}
			return;
		}
		else destroy_existing_instlocs(arcs[i]);
	}
}

void	skolemize_mrs(struct mrs	*m, int	equate_qeqs)
{
	int	i;

	// tweak the INSTLOC fields of the mrs variables
	// so that they won't unify with each other.

	make_reliable_vnums(m);

	struct type	*sktypes[m->vlist.nvars];
	for(i=0;i<m->vlist.nvars;i++)
		sktypes[i] = transfer_next_skolem_constant();

	if(equate_qeqs)
		for(i=0;i<m->nhcons;i++)
		{
			assert(m->hcons[i].hi->vnum >= 0 && m->hcons[i].hi->vnum < m->vlist.nvars);
			assert(m->hcons[i].lo->vnum >= 0 && m->hcons[i].lo->vnum < m->vlist.nvars);
			sktypes[m->hcons[i].hi->vnum] = sktypes[m->hcons[i].lo->vnum];
		}

	for(i=0;i<m->vlist.nvars;i++)
	{
		struct dg	*dg;
		if(semi_th && ALLOW_SEMI_MODE)
			dg = m->vlist.vars[i]->semi_dg;
		else dg = m->vlist.vars[i]->dg;

		if(!dg)continue;	// invented LTOP, INDEX, XARG
		if(m->vlist.vars[i]->is_const)continue;

		/*printf("dag to skolemize for %s%d = \n", m->vlist.vars[i]->type, i);
		print_dg(dg);
		printf("\n");*/

		struct dg	*iloc = dg_hop(dg, instloc_feature);
		assert(iloc != NULL);
		iloc->type = iloc->xtype = sktypes[i];
	}
}

/*void	skolemize_for_transfer(struct mrs	*m)
{
	skolem_counter = 0;
	skolemize_mrs(m, EQUATE_QEQS_FOR_TRANSFER);
}*/

void	skolemize_for_generation(struct mrs	*m)
{
	skolem_counter = 0;
	skolemize_mrs(m, 1);
}

void	unskolemize_for_transfer(struct mrs	*m)
{
	int	i;

	for(i=0;i<m->nrels;i++)
		destroy_existing_instlocs(m->rels[i].dg);
	if(m->ltop)destroy_existing_instlocs(m->ltop->dg);
	if(m->index)destroy_existing_instlocs(m->index->dg);
	if(m->xarg)destroy_existing_instlocs(m->xarg->dg);
}

check_mrs_var_is_on_vlist(struct mrs_var	*v, struct mrs_vlist	*vl)
{
	if(!v)return 0;
	assert(v->vnum >= 0 && v->vnum < vl->nvars);
	assert(vl->vars[v->vnum] == v);
}

check_all_mrs_vars_are_on_vlist(struct mrs	*m)
{
	int	i;
	make_reliable_vnums(m);
	check_mrs_var_is_on_vlist(m->ltop, &m->vlist);
	check_mrs_var_is_on_vlist(m->xarg, &m->vlist);
	check_mrs_var_is_on_vlist(m->index, &m->vlist);
	for(i=0;i<m->nrels;i++)
	{
		struct mrs_ep	*ep = m->rels+i;
		check_mrs_var_is_on_vlist(ep->lbl, &m->vlist);
		int j;
		for(j=0;j<ep->nargs;j++)
			check_mrs_var_is_on_vlist(ep->args[j].value, &m->vlist);
	}
	for(i=0;i<m->nhcons;i++)
	{
		struct mrs_hcons	*hc = m->hcons+i;
		check_mrs_var_is_on_vlist(hc->hi, &m->vlist);
		check_mrs_var_is_on_vlist(hc->lo, &m->vlist);
	}
	for(i=0;i<m->nicons;i++)
	{
		struct mrs_icons	*ic = m->icons+i;
		check_mrs_var_is_on_vlist(ic->left, &m->vlist);
		check_mrs_var_is_on_vlist(ic->right, &m->vlist);
	}
}

int	strptrcmp(char	**x, char	**y)
{
	return strcmp(*x,*y);
}

int	equiv_mrs(struct mrs	*x, struct mrs	*y)
{
	/*printf("is %p eq %p?\n", x, y);
	print_mrs(x);
	printf(" vs \n");
	print_mrs(y);
	printf("???\n");*/
	// quick first step: see if PRED lists are identical
	if(x->nrels != y->nrels)return 0;
	char	*xpreds[x->nrels], *ypreds[y->nrels];
	int i;
	for(i=0;i<x->nrels;i++)xpreds[i]=x->rels[i].pred;
	for(i=0;i<y->nrels;i++)ypreds[i]=y->rels[i].pred;
	qsort(xpreds, x->nrels, sizeof(char*), (int(*)(const void*,const void*))strptrcmp);
	qsort(ypreds, y->nrels, sizeof(char*), (int(*)(const void*,const void*))strptrcmp);
	for(i=0;i<x->nrels;i++)if(strcmp(xpreds[i], ypreds[i]))return 0;
	extern int g_mrs_test_demand_equality;
	g_mrs_test_demand_equality = 1;
	int result = mrs_subsumes(x,y);
	g_mrs_test_demand_equality = 0;
	return result;
	//if(!mrs_subsumes(x,y))return 0;
	//if(!mrs_subsumes(y,x))return 0;
	//printf("yes\n");
	return 1;
}

int	mrs_is_on_list(struct mrs	*m, int	n, struct mrs	**l)
{
	int	i;
	for(i=0;i<n;i++)
		if(equiv_mrs(m, l[i]))return 1;
	return 0;
}

struct transfer_mrs_set
{
	int	n;
	struct mrs	**mrs;
};

transfer_add_preds(struct hash	*seen, struct mrs	*m)
{
	int	i, j;
	static int	predf = -1;
	struct type_hierarchy	*th = default_type_hierarchy();
	if(predf==-1)predf=lookup_fname("PRED");
	extern int g_normalize_predicates;
	extern struct type_hierarchy	*semi_th, *main_th;
	if(g_normalize_predicates)th = semi_th;
	else th = main_th;
	for(i=0;i<m->nrels;i++)
	{
		struct mrs_ep	*e = m->rels+i;
		//struct dg	*pr = dg_hop(e->dg, predf);
		//assert(pr!=NULL);
		//struct type	*prt = pr->xtype;
		struct type	*prt = th_lookup_type(th, e->pred);//semi_find_type(e->pred);
		if(!prt)continue;
		if(!hash_find(seen, prt->name))
			hash_add(seen, prt->name, (void*)0x1);
		for(j=0;j<prt->ndescendents;j++)
			if(prt->descendents[j]!=prt->tnum && !hash_find(seen, th->types[prt->descendents[j]]->name))
				hash_add(seen, th->types[prt->descendents[j]]->name, (void*)0x1);
	}
}

transfer_rule_has_seen_all_preds(struct hash	*seen, struct transfer_rule	*tr)
{
	int i;
	static int	predf = -1;
	if(predf==-1)predf=lookup_fname("PRED");
	for(i=0;i<tr->context.neps+tr->input.neps;i++)
	{
		struct mrs_ep_desc	epd = place_in_transfer_rule(tr, i);
		if(epd.pred_re)continue;
		struct dg	*pd = dg_hop(epd.dg, predf);
		if(!pd)continue;
		extern struct type_hierarchy	*semi_th;
		char	*pred = pred_for_place_in_transfer_rule(tr, i);
		struct type	*pt = pd->xtype, *pts = th_lookup_type(semi_th, pred);
		if(pt->ndescendents > 1 || (pts && pts->ndescendents>1))
		{
			//printf("rule pred type %s has %d descendents\n", pt->name, pt->ndescendents);
			continue;	// not a string type or leaf type
		}
		if(hash_find(seen, pred))continue;
		if(hash_find(seen, pt->name))continue;
		//printf("can totally skip %s because %s not found\n", tr->name, pt->name);
		return 0;
	}
	return 1;
}

int	process_one_transfer_result(struct transfer_rule	*tr, int	*alignment, int	*hcalignment, struct mrs	*min, struct transfer_mrs_set	*ts, int	pack_start, struct hash	*preds_seen)
{
	struct mrs	*mout = transfer_mrs_result(tr, alignment, hcalignment, min);
	if(!mout)return -1;	// latent cycle check failed

	// make a copy of 'mout', so we don't have to worry about structure sharing in subsumption tests
	// the problem with structure sharing is each side has its own ->vnum's
	mout = slab_copy_mrs(mout, 1);
	start_and_alloc_profiler(&transfer_packing_profiler, "packing", transfer_profiler, NULL);
	if(!mrs_is_on_list(mout, ts->n - pack_start, ts->mrs + pack_start))
	{
		// new result.
		ts->mrs = slab_realloc(ts->mrs, sizeof(struct mrs*)*ts->n, sizeof(struct mrs*)*(ts->n+1));
		ts->mrs[ts->n++] = mout;
		setup_tmp();	// prevent subsequent forget_tmp()'s from destroying this
		transfer_add_preds(preds_seen, mout);
	}
	stop_profiler(transfer_packing_profiler, 1);

	//printf("rule fired: %s\n", tr->name);
	//print_mrs(mout);printf("\n");
	return 0;
}

// this is slowish. faster idea: when a particular transfer operation is started, make a hash set of the pred values that have actually been seen.
int	pred_present(struct mrs	*m, struct type	*pred)
{
	int	i;
	static int	pred_fnum = -1;
	if(!pred)return 0;
	if(pred_fnum == -1)pred_fnum = lookup_fname("PRED");
	for(i=0;i<m->nrels;i++)
	{
		struct mrs_ep	*ep = &m->rels[i];
		//struct dg	*ep_p = dg_hop(ep->dg, pred_fnum);
		//assert(ep_p);
		//if(glb(ep_p->xtype, pred))return 1;
		extern struct type_hierarchy	*semi_th;
		assert(semi_th != NULL);
		struct type	*ep_pt = th_lookup_type(semi_th, ep->pred);
		if(ep_pt && glb(ep_pt, pred))return 1;
	}
	return 0;
}

// return 1 if all context/input pred values can be matched, 0 otherwise
int	tr_quickcheck(struct transfer_rule	*tr, struct mrs	*min)
{
	static int	pred_fnum = -1;
	if(pred_fnum == -1)pred_fnum = lookup_fname("PRED");
	int	nplaces = tr->input.neps + tr->context.neps;
	int	i;
	for(i=0;i<nplaces;i++)
	{
		struct mrs_ep_desc	epd = place_in_transfer_rule(tr, i);
		struct dg	*de_p = dg_hop(epd.dg, pred_fnum);
		if(!de_p || de_p->xtype==get_top())continue;	// no PRED info to match (or regex)
		char	*pred = pred_for_place_in_transfer_rule(tr, i);
		extern int g_normalize_predicates;
		if(g_normalize_predicates)
		{
			if(!pred_present(min, semi_find_type(pred)))return 0;
		}
		else
		{
			if(!pred_present(min, lookup_type(pred)))
			{
				//printf("not present: %s / %s\n", de_p->xtype->name, pred);
				return 0;
			}
		}
		// don't bother with regex's; they're typically quite general and will match most MRSes somewhere. the question is whether they match in the right variable pattern, which we won't discover here anyway.
		// they're also relatively rare (hypothesis).
	}
	return 1;
}

int	transfer_mrs1(struct transfer_rule	*tr, struct transfer_mrs_set	*ts, int first_route_only, struct hash	*preds_seen)
{
	DEBUG("rule %s -- optional %d\n", tr->name, tr->optional);
	int	i, nresult = 0, nfires = 0;
	struct mrs	**result = NULL;
	int	pack_start = ts->n;
	for(i=0;i<ts->n;i++)
		if(tr_quickcheck(tr, ts->mrs[i]))break;
	if(i==ts->n)
	{
		DEBUG("quickly rejected: %s\n", tr->name);
		return 0;
	}
	for(i=0;i<ts->n && !cancel_task;i++)
	{
		if((slab_usage() / (1024*1024)) >= MAX_TRANSFER_CHUNKS)
		{
			fprintf(stderr, "NOTE: hit RAM limit while transfering\n");
			itsdb_error("ran out of RAM while transfering");
			return -1;
		}
		struct mrs	*min = ts->mrs[i];
		if(i == pack_start)
		{
			// we've processed all of the results that have had K applications
			// henceforth all results we see have had K+1 applications
			// furthermore, no results have been generated with K+2 applications
			// keep track of where the K+2 generation starts...
			pack_start = ts->n;
			// this assumes that it is impossible for two edges that have had different numbers of applications of `tr' to pack with each other.  likely, to say the least.  if the assumption is violated, the worst that happens is we have suboptimal packing.
		}

		int	nalignments = 0;
		int	found_alignment(int	*alignment, int *hcalignment)
		{
			if(0 != process_one_transfer_result(tr, alignment, hcalignment, min, ts, pack_start, preds_seen))
				return 0;

			nalignments++;
			nfires++;
			return first_route_only;
		}
		if(tr_quickcheck(tr, min))
			align_transfer_rule(tr, min, found_alignment);
		//else printf("quickly rejected for one candidate only: %s\n", tr->name);
		if(nalignments == 0 || tr->optional)
		{
			// make a copy of 'min', so we don't have to worry about structure sharing in subsumption tests
			//if(nresult)min = slab_copy_mrs(min,1);
			//printf("ts[%d] being saved as %p\n", i, min);
			// keep this mrs
			// ... but make sure it's not already on the result list.
			if(!mrs_is_on_list(min, nresult, result))
			{
				result = slab_realloc(result, sizeof(struct mrs*)*nresult, sizeof(struct mrs*)*(nresult+1));
				setup_tmp();	// prevent subsequent forget_tmp()'s from destroying this
				result[nresult++] = min;
			}
			else
			{
				fprintf(stderr, "WARNING: duplicate MRS created during transfer\n");
			}
		}
		else
		{
			// ditch this mrs
		}
	}
	if(nfires)
	{
		extern int debug_level;
		if(debug_level)
		{
			printf("transfer rule %s fired %d times; %d intermediates; %d results to pass on\n", tr->name, nfires, ts->n, nresult);
			extern int trace;
			if(trace)
				for(i=0;i<nresult;i++)print_mrs(result[i]);
		}
	}
	ts->n = nresult;
	ts->mrs = result;
	return nfires;
}

struct profiler	**fixup_profilers;
struct profiler	**cleanup_profilers;
struct profiler	**idiom_profilers;
struct profiler	**transfer_rule_profilers;

int	transfer_mrs(int	nrules, struct transfer_rule	**rules, struct mrs	*m, struct mrs	***Results, int first_route_only)
{
	int	i;

	if(g_profiling)
	{
		start_and_alloc_profiler(&transfer_profiler, "transfer", NULL, NULL);
		transfer_profiler->sortable = 5;
	}

	if(semi_th && ALLOW_SEMI_MODE)
		semi_reformat_mrs(m, 0);

	//skolemize_for_transfer(m);

	struct hash	*preds_seen = hash_new("transfer preds seen");
	transfer_add_preds(preds_seen, m);

	struct transfer_mrs_set	ts;
	ts.n = 1;
	ts.mrs = slab_alloc(sizeof(*m));
	ts.mrs[0] = m;

	for(i=0;i<nrules && !cancel_task;i++)
	{
		if(rules[i]->disabled)continue;
		if(!transfer_rule_has_seen_all_preds(preds_seen, rules[i]))continue;
		//printf("trying %s\n", rules[i]->name);
		if(g_profiling)
		{
			if(!transfer_rule_profilers)
				transfer_rule_profilers = calloc(sizeof(struct profiler*), nrules);
			start_and_alloc_profiler(transfer_rule_profilers+i, rules[i]->name, transfer_profiler, NULL);
		}
		int	fro = first_route_only?1:0;
		if(rules[i]->optional && first_route_only==2)fro=0;	// 2 means FRO for obligatory rules but not for optionals
		int nfires = transfer_mrs1(rules[i], &ts, fro, preds_seen);
		if(nfires == -1)
		{
			if(g_profiling)
			{
				stop_profiler(transfer_rule_profilers[i], 0);
				stop_profiler(transfer_profiler, 0);
			}
			return -1;
		}
		if(g_profiling)
			stop_profiler(transfer_rule_profilers[i], nfires);
	}
	hash_free_nokeys(preds_seen);

	unskolemize_for_transfer(m);

	// since we copy every output mrs, the following will actually work
	// and will lead to less confusion for consumers
	for(i=0;i<ts.n;i++)
	{
		unskolemize_for_transfer(ts.mrs[i]);
		make_reliable_vnums(ts.mrs[i]);
	}

	if(g_profiling)stop_profiler(transfer_profiler, 1);

	if(Results)*Results = ts.mrs;
	return ts.n;
}

struct mrs	*reformat_mrs_for_transfer(struct mrs	*m)
{
	// what this does is re-extract every variable and EP from the DG representation,
	// so that it matches what the results of transfer rules will look like.
	// if we don't do this, some transfer rules can unintentially create slight differences
	// in places that they don't want to, defeating packing.
	clear_mrs();

	int i;
	for(i=0;i<m->vlist.nvars;i++)
		if(!m->vlist.vars[i]->dg)
		{
			int dagify_result = dagify_mrs_var(m->vlist.vars[i], NULL);
			assert(dagify_result == 0);
		}
		else
		{
			m->vlist.vars[i]->dg = p_dereference_dg(m->vlist.vars[i]->dg);
			m->vlist.vars[i]->dg->gen = 0;	// if gen ==1 we stand a chance of dg_to_mrs_var() not extracting a new struct mrs_var, and worse still, the variable not making it onto the new_vlist.
		}
	for(i=0;i<m->nrels;i++)
	{
		int dagify_result = dagify_mrs_ep(m->rels+i);
		assert(dagify_result == 0);
	}

	struct mrs_vlist	new_vlist;

	// be careful. we have to allocate enough room for the number of variables that we will actually get out of the DAG, not how many we think there ought to be.
	new_vlist.nvars = 0;
	struct mrs_var	**tmp_vlist = malloc(sizeof(struct mrs_var*) * 10240);
	new_vlist.vars = tmp_vlist;
	inhibit_vpm++;
	m->ltop = m->ltop?dg_to_mrs_var(m->ltop->dg, &new_vlist):NULL;
	m->index = m->index?dg_to_mrs_var(m->index->dg, &new_vlist):NULL;
	m->xarg = m->xarg?dg_to_mrs_var(m->xarg->dg, &new_vlist):NULL;
	for(i=0;i<m->nrels;i++)
	{
		// keep the predicate, because the AVM representation does NOT include it
		char	*pred = m->rels[i].pred;
		dg_to_mrs_ep(m->rels[i].dg, &new_vlist, m->rels+i);
		m->rels[i].pred = pred;
		m->rels[i].epnum = i;
	}
	for(i=0;i<m->nhcons;i++)
	{
		m->hcons[i].hi = dg_to_mrs_var(m->hcons[i].hi->dg, &new_vlist);
		m->hcons[i].lo = dg_to_mrs_var(m->hcons[i].lo->dg, &new_vlist);
	}
	for(i=0;i<m->nicons;i++)
	{
		m->icons[i].left = dg_to_mrs_var(m->icons[i].left->dg, &new_vlist);
		m->icons[i].right = dg_to_mrs_var(m->icons[i].right->dg, &new_vlist);
	}
	new_vlist.vars = malloc(sizeof(struct mrs_var*) * new_vlist.nvars);
	memcpy(new_vlist.vars, tmp_vlist, sizeof(struct mrs_var*) * new_vlist.nvars);
	free(tmp_vlist);
	m->vlist = new_vlist;
	inhibit_vpm--;
	return m;
}

struct mrs	*fixup_mrs(struct mrs	*m)
{
#ifdef	NO_FIXUP
	return m;
#else
	if(!nfixup_rules)return m;
	m = reformat_mrs_for_transfer(m);
	//printf("reformatted mrs:\n");
	//print_mrs(m);
	//printf("there are %d fixup rules\n", nfixup_rules);

	struct mrs	**results = NULL;
	transfer_rule_profilers = fixup_profilers;
	int	n = transfer_mrs(nfixup_rules, fixup_rules, m, &results, FIXUP_FIRST_ROUTE_ONLY);
	fixup_profilers = transfer_rule_profilers;
	assert(n >= 0);
	if(n > 1)
		fprintf(stderr, "WARNING: ambiguity in generator fixup rules; using first result.\n");
	return results[0];
#endif
}

struct mrs	*cleanup_mrs(struct mrs	*m)
{
	if(!ncleanup_rules)return m;
	// we shouldn't have to reformat() m; it should have come straight off of a DAG.
	// caveat: the ->ltop may have been manufactured.
	if(!m->ltop->dg)
	{
		int dagify_result = dagify_mrs_var(m->ltop, NULL);
		assert(dagify_result == 0);
	}
	//m = reformat_mrs_for_transfer(m);
	//printf("reformatted mrs:\n");
	//print_mrs(m);
	struct mrs	**results = NULL;
	transfer_rule_profilers = cleanup_profilers;
	int	n = transfer_mrs(ncleanup_rules, cleanup_rules, m, &results, CLEANUP_FIRST_ROUTE_ONLY);
	cleanup_profilers = transfer_rule_profilers;
	assert(n >= 0);
	if(n > 1)
		fprintf(stderr, "WARNING: ambiguity in generator cleanup rules; using first result.\n");
	return results[0];
}

int	transfer(struct mrs	*m)
{
	extern char	*transfer_input_relation_prefix;
	if(transfer_input_relation_prefix)
	{
		int i, pl = strlen(transfer_input_relation_prefix);
		for(i=0;i<m->nrels;i++)
		{
			// the input MRS is stored on the heap...
			char	*pred = m->rels[i].pred;
			int		len = strlen(pred);
			char	*revised = malloc(len + pl + 1 + 3);
			// all predication names become quoted in this operation.
			if(pred[0]=='"')
				sprintf(revised, "\"%s%s", transfer_input_relation_prefix, pred+1);
			else sprintf(revised, "\"%s%s\"", transfer_input_relation_prefix, pred);
			free(m->rels[i].pred);
			m->rels[i].pred = revised;
		}
	}
	m = apply_transfer_input_vpm(m);
	m = reformat_mrs_for_transfer(m);
	//printf("reformatted mrs:\n");
	//print_mrs(m);

	cancel_task = 0;
	did_timeout = 0;
	signal(SIGALRM, alarm_handler);

	if(timeout_seconds > 0)
		alarm(timeout_seconds);

	struct mrs	**results = NULL;
	int	n = transfer_mrs(ntransfer_rules, transfer_rules, m, &results, 2);
	int i;
	for(i=0;i<n;i++)
	{
		struct mrs	*out = apply_transfer_output_vpm(results[i]);
		print_mrs(out);
	}
	printf("\n");
	fflush(stdout);
	fprintf(stderr, "NOTE: %d transfer results\t", n);
	print_slab_stats();
	clear_mrs();
	clear_slab();
}
