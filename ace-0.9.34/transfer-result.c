#define		_GNU_SOURCE
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>


//#define	DEBUG	printf
#define	DEBUG(...)	do { } while(0)

#include	"unicode.h"
#include	"transfer.h"
#include	"freeze.h"
#include	"chart.h"
#include	"dag.h"
#include	"type.h"
#include	"hash.h"
#include	"conf.h"
#include	"mrs.h"
#include	"timer.h"

extern int inhibit_vpm;

void	compute_variable_mapping(struct mrs	*min, struct mrs_vlist	*new_vars, struct dg	**old_var_dg, struct mrs_var	**new_var_map)
{
	// see if any of the new variables are old variables in disguise.
	// for truly new variables, issue a new INSTLOC. -- or don't, these days.
	bzero(new_var_map, sizeof(struct mrs_var*)*min->vlist.nvars);
	int i, j;
	for(i=0;i<new_vars->nvars;i++)
	{
		// for every extracted variable 'v', one of the following must happen:
		// 1. it's an old variable; set new_var_map[] accordingly
		// 2. it's truly new; make sure it has a new INSTLOC
		// 3. we can't tell, throw an error
		struct mrs_var	*v = new_vars->vars[i];
		if(v->is_const)continue;	// don't try to align new constants to old constants; they aren't skolemized anyway.
		struct dg	*vdg = v->dg;
		if(ALLOW_SEMI_MODE)
			v->semi_dg = vdg;	// ?? or should it be vdg = v->semi_dg?
		vdg = dereference_dg(vdg);

		//struct dg	*iloc = dg_hop(vdg, instloc_feature);
		//assert(iloc != NULL);

		// old_var_dg[]-based method of figuring out whether it's an old variable
		int	noldvars = 0;
		for(j=0;j<min->vlist.nvars;j++)
			if(old_var_dg[j] == vdg)
			{
				new_var_map[j] = v;
				noldvars++;
			}
		/*if(!noldvars)
		{
			// it may need to have an INSTLOC allocated
			char	*ilt = iloc->xtype->name;
			if(*ilt != '"')
				iloc->xtype = iloc->type = transfer_next_skolem_constant();
		}*/

/*
		// INSTLOC-based method of figuring out whether it's an old variable...
		char	*ilt = iloc->xtype->name;
		if(*ilt == '"')
		{
			// INSTLOC was set; this variable may exist in the input MRS. find it.
			//   in case v is a handle that is/was part of a QEQ,
			//   the INSTLOC by itself may not be enough to determine which
			//   input variable 'v' corresponds to.
			//   e.g. 'v' may be the RSTR of a newly +copy+'d quantifier EP
			//   we have to make sure we new_var_map[] the old HI end of the QEQ
			//   to 'v', rather than the old LO end.
			//printf("new var %d has instloc type %s\n", i, ilt);
			for(j=0;j<min->vlist.nvars;j++)
			{
				struct mrs_var	*ivar = min->vlist.vars[j];
				if(ivar->is_const)continue;
				struct dg	*ivdg = ALLOW_SEMI_MODE?ivar->semi_dg:ivar->dg;
				struct dg	*iiloc = dg_hop(ivdg, instloc_feature);
				assert(iiloc != NULL);
				if(iiloc->xtype == iloc->xtype)break;
			}
			if(j == min->vlist.nvars)
			{
#ifdef	COPIED_VARIABLES_NEED_REENTRANCIES
				// make sure this was one of the variables we gave a brand new instloc to.
				for(j=0;j<ninstlocs_to_fix;j++)
					if(dereference_dg(instlocs_to_fix[j]) == vdg)break;
				if(j==ninstlocs_to_fix)
#endif
				{
					printf("ERROR: found INSTLOC %s in output Ep variable dg %p, but that is not a variable in the input MRS and is not a variable we assigned a new INSTLOC to.\n", ilt, vdg);
					assert(!"not reached");
				}
			}
			else
			{
				//printf(" ... was actually old variable %s%d\n", min->vlist.vars[j]->type, j);
				new_var_map[j] = v;
			}
		}
		else
		{
#ifdef	COPIED_VARIABLES_NEED_REENTRANCIES
			// should have already allocated instlocs to all new variables... code higher up.
			assert(!"not reached");
#else

			// INSTLOC was not set; this variable is being invented brand new by this rule.
			// give it an INSTLOC for future use.
			iloc->xtype = iloc->type = transfer_next_skolem_constant();
			//printf("new var %d was really new\n", i);
#endif
		}
*/
	}
}

void	transfer_result_dg_to_mrs(struct transfer_rule	*tr, struct mrs_vlist	*new_vars, struct dg	**copy_ep_out_dgs, struct mrs_ep	*new_eps, struct dg	**copy_hc_hi, struct dg	**copy_hc_lo, struct mrs_var	**copy_hc_hi_v, struct mrs_var	**copy_hc_lo_v, struct mrs	*mout, struct dg	*copy_ltop, struct dg	*copy_index, struct dg	*copy_xarg)
{
	int i;

	inhibit_vpm = 1;	// in SEMI-mode, the variables are already external.  in non-SEMI-mode, we want to keep variables internal.
	clear_mrs();	// we don't want spurious reentrancies with variables read off of previous invocations of this rule

	/*for(i=0;i<tr->output.neps;i++)
	{
		printf("output EP dag:\n");
		print_dg(copy_ep_out_dgs[i]);
		printf("\n");
	}*/
	for(i=0;i<tr->output.neps;i++)
	{
		extern int g_normalize_predicates;
		if(g_normalize_predicates)
			assert(!"not reached; code to extract new PRED value for EPs created in transfer is not yet written for SEM-I-enabled ACE");
		dg_to_mrs_ep(copy_ep_out_dgs[i], new_vars, &new_eps[i]);
		/*printf("new EP %d:    ", i);
		printf("[ %s LBL: ", new_eps[i].pred);
		print_mrs_var(new_eps[i].lbl);
		int j;
		for(j=0;j<new_eps[i].nargs;j++)
		{
			printf(" %s: ", new_eps[i].args[j].name);
			print_mrs_var(new_eps[i].args[j].value);
		}
		printf(" ]\n");*/
	}
	for(i=0;i<tr->output.nhcons;i++)
	{
		copy_hc_hi_v[i] = dg_to_mrs_var(copy_hc_hi[i], new_vars);
		copy_hc_lo_v[i] = dg_to_mrs_var(copy_hc_lo[i], new_vars);
	}

	mout->ltop = dg_to_mrs_var(copy_ltop, new_vars);
	mout->index = dg_to_mrs_var(copy_index, new_vars);
	mout->xarg = copy_xarg?dg_to_mrs_var(copy_xarg, new_vars):NULL;

	for(i=0;i<new_vars->nvars;i++)
		new_vars->vars[i]->dg->copy = NULL;	// make sure dg_to_mrs_var in future passes doesn't return this by mistake
	inhibit_vpm = 0;
}

void	transfer_top_level_variables(struct transfer_rule	*tr, struct mrs	*min, struct mrs	*mout, struct mrs_var	*(*map_variable)(struct mrs_var	*vin))
{
/*
	// XXX shouldn't this be looking at tr->output.mrs->ltop etc?
	// yes, it should. Dan sent a complaint about this behavior being broken Nov-14-2013.
	mout->ltop = map_variable(min->ltop);
	mout->index = map_variable(min->index);
	mout->xarg = map_variable(min->xarg);
	// these duties are now carried out by transfer_result_dg_to_mrs()
*/
}

void	transfer_hcons_result(struct transfer_rule	*tr, struct mrs	*min, struct mrs	*mout, int	*hcalignment, struct mrs_var	**copy_hc_hi_v, struct mrs_var	**copy_hc_lo_v, struct mrs_var	*(*map_variable)(struct mrs_var	*vin))
{
	int	expected_hcons = min->nhcons - tr->input.nhcons + tr->output.nhcons;
	int	i;
	mout->nhcons = 0;
	mout->hcons = slab_alloc(sizeof(struct mrs_hcons) * expected_hcons);
	char	hc_ditch[min->nhcons];
	bzero(hc_ditch, sizeof(hc_ditch));
	for(i=0;i<tr->input.nhcons;i++)
		hc_ditch[hcalignment[i]] = 1;
	for(i=0;i<min->nhcons;i++)
		if(!hc_ditch[i])
		{
			struct mrs_hcons	*hcin = min->hcons+i;
			struct mrs_hcons	*hcout = mout->hcons+mout->nhcons++;
			hcout->type = hcin->type;
			hcout->hi = map_variable(hcin->hi);
			hcout->lo = map_variable(hcin->lo);
		}
	for(i=0;i<tr->output.nhcons;i++)
	{
		struct mrs_hcons	*hcnew = tr->output.mrs->hcons+i;
		struct mrs_hcons	*hcout = mout->hcons + mout->nhcons++;
		hcout->type = hcnew->type;
		hcout->hi = copy_hc_hi_v[i];
		hcout->lo = copy_hc_lo_v[i];
	}
	assert(mout->nhcons == expected_hcons);
}

void	transfer_icons_result(struct transfer_rule	*tr, struct mrs	*min, struct mrs	*mout, struct mrs_var	*(*map_variable)(struct mrs_var	*vin))
{
	int	i;
	mout->nicons = min->nicons;
	mout->icons = slab_alloc(sizeof(struct mrs_icons) * mout->nicons);
	for(i=0;i<min->nicons;i++)
	{
		struct mrs_icons	*icin = min->icons+i;
		struct mrs_icons	*icout = mout->icons+i;
		icout->type = icin->type;
		icout->left = map_variable(icin->left);
		icout->right = map_variable(icin->right);
	}
}

void	transfer_ep_result(struct transfer_rule	*tr, struct mrs	*min, struct mrs	*mout, int	*alignment, struct mrs_ep	*new_eps, struct mrs_var	*(*map_variable)(struct mrs_var	*vin))
{
	int	expected_rels = min->nrels - tr->input.neps + tr->output.neps;
	int	i;
	//printf("activated rule '%s' to ditch %d EPs\n", tr->name, tr->input.neps);
	mout->nrels = 0;
	mout->rels = slab_alloc(sizeof(struct mrs_ep) * expected_rels);
	char	ep_ditch[min->nrels];
	bzero(ep_ditch, sizeof(ep_ditch));
	for(i=0;i<tr->input.neps;i++)
		ep_ditch[alignment[i]] = 1;
	for(i=0;i<min->nrels;i++)
		if(!ep_ditch[i])
		{
			struct mrs_ep	*epin = min->rels+i;
			struct mrs_ep	*epout = mout->rels + mout->nrels;
			*epout = *epin;
			epout->args = slab_alloc(sizeof(struct mrs_ep_role)*epin->nargs);
			int k, anydiff = 1;
			char	diffarg[epin->nargs];
			epout->lbl = map_variable(epin->lbl);
			for(k=0;k<epin->nargs;k++)
			{
				epout->args[k].name = epin->args[k].name;
				epout->args[k].value = map_variable(epin->args[k].value);
				if(epout->args[k].value != epin->args[k].value)
				{
					anydiff = 1;
					diffarg[k] = 1;
				}
				else diffarg[k] = 0;
			}
			if(anydiff)
			{
				// need to build a new DAG for this EP
				struct dg	*odg = dereference_dg(epin->dg);
				int	label_bytes = DAG_EXTRA_LABELS_SIZE_FOR_COUNT(odg->narcs);
				struct dg	*ndg = slab_alloc(sizeof(struct dg) + label_bytes + sizeof(struct dg*)*odg->narcs);
				bzero(ndg, sizeof(struct dg));
				ndg->type = ndg->xtype = odg->xtype;
				ndg->narcs = odg->narcs;
				struct dg	**narcs = DARCS(ndg);
				struct dg	**oarcs = DARCS(odg);
				for(k=0;k<odg->narcs;k++)
				{
					ndg->label[k] = odg->label[k];
					extern char	**fnames;
					char	*role = fnames[ndg->label[k]];
					int l = -1;
					if(!strcmp(role, "LBL"))
					{
						struct mrs_var	*v = epout->lbl;
						narcs[k] = ALLOW_SEMI_MODE?v->semi_dg:v->dg;
					}
					else for(l=0;l<epout->nargs;l++)
						if(!strcasecmp(role, epout->args[l].name))
						{
							struct mrs_var	*v = epout->args[l].value;
							narcs[k] = ALLOW_SEMI_MODE?v->semi_dg:v->dg;
							break;
						}
					if(l==epout->nargs)
						narcs[k] = oarcs[k];
					assert(narcs[k] != NULL);
				}
				epout->dg = ndg;
				/*if(ALLOW_SEMI_MODE)
					semi_reformat_mrs_ep(epout, 0);
				else dagify_mrs_ep(epout);*/
			}
			epout->epnum = mout->nrels++;
		}
	for(i=0;i<tr->output.neps;i++)
	{
		mout->rels[mout->nrels] = new_eps[i];
		mout->rels[mout->nrels].epnum = mout->nrels;
		mout->nrels++;
	}
	assert(expected_rels == mout->nrels);
}

void	transfer_vlist_result(struct transfer_rule	*tr, struct mrs	*min, struct mrs	*mout, struct mrs_vlist	*new_vars, int	ncarried_input_variables, char	*input_variable_is_carried, struct mrs_var	*(*map_variable)(struct mrs_var	*vin))
{
	// the new vlist should have the old variables that were returned by map_variable(), union the new variables
	int	i, expected_vars = ncarried_input_variables + new_vars->nvars;
	mout->vlist.nvars = 0;
	mout->vlist.vars = slab_alloc(sizeof(struct mrs_var*) * expected_vars);
	for(i=0;i<min->vlist.nvars;i++)
		if(input_variable_is_carried[i])
			mout->vlist.vars[mout->vlist.nvars++] = min->vlist.vars[i];
				// was = map_variable(min->vlist.vars[i]);
	for(i=0;i<new_vars->nvars;i++)
		mout->vlist.vars[mout->vlist.nvars++] = new_vars->vars[i];
	assert(expected_vars == mout->vlist.nvars);
	for(i=0;i<mout->vlist.nvars;i++)
		mout->vlist.vars[i]->vnum = -1;	// the 'vnum' property is not reliable, since variables can be shared between different MRSes, and should only be used for printing purposes. set it to -1 to encourage crashing if we mistakenly try to rely on it some day.

	//check_all_mrs_vars_are_on_vlist(mout);
	//check_all_mrs_vars_are_on_vlist(min);
}

// when creating a new EP (i.e. on the output list),
// in principal all of the variables it references are (potentially) changed or new.
// we can get away with considering them all new.
// *but* they may be / will be reentrant with variables referenced by other parts of the MRS.
// use the new variables' INSTLOC to see what old variable they correspond to,
// and in the result MRS, update all obsoleted old variables to their new counterparts.

void	perform_override(struct dg	*into, struct dg	*from)
{
	assert(into && from);
	into = dereference_dg(into);
	from = dereference_dg(from);
	if(from->xtype != get_top())	// don't override for nodes created implicitly along the path to an authored constraint
		into->type = into->xtype = from->xtype;
	else if(into->xtype == NULL)	// except to revive nodes that were marked for deletion due to nonexistant input variables
		into->xtype = into->type;
	int i;
	struct dg	**fromarcs = DARCS(from);
	for(i=0;i<from->narcs;i++)
	{
		struct dg	*into2 = dg_hop(into, from->label[i]);
		assert(into2 || !"dag to be edited did not have the required path");
		perform_override(into2, fromarcs[i]);
	}
}

void	prune_unmatched_parts(struct dg	*dg)
{
	assert(dg && dg->xtype);
	int i, newn = 0, oldn = dg->narcs;
	unsigned short	newlabels[oldn];
	struct dg	**arcs = DARCS(dg);
	struct dg	*newarcs[oldn];
	for(i=0;i<oldn;i++)
	{
		if(arcs[i]->xtype == NULL)	// pruned
			{ }
		else	// kept
		{
			newlabels[newn] = dg->label[i];
			newarcs[newn] = arcs[i];
			newn++;
			prune_unmatched_parts(arcs[i]);
		}
	}
	if(newn != oldn)
	{
		dg->narcs = newn;
		arcs = DARCS(dg);
		memcpy(dg->label, newlabels, sizeof(unsigned short)*newn);
		memcpy(arcs, newarcs, sizeof(struct dg*)*newn);
	}
}

struct mrs	*transfer_mrs_result(struct transfer_rule	*tr, int	*alignment, int	*hcalignment, struct mrs	*min)
{
	//printf("finding result of transfer rule '%s'\n", tr->name);
	//check_all_mrs_vars_are_on_vlist(min);
	int i, j;

	struct dg	*old_var_dg[min->vlist.nvars];
	// get the location of every old var in the unified mrs/rule dag conglomeration
	for(i=0;i<min->vlist.nvars;i++)
		old_var_dg[i] = dereference_dg(min->vlist.vars[i]->dg);

	// if a rule variable was touched by the unifier, it matched something in the input
	extern unsigned int generation;
	char	input_vars_exist[tr->input.mrs->vlist.nvars];
	for(i=0;i<tr->input.mrs->vlist.nvars;i++)
		input_vars_exist[i] = (!tr->input.mrs->vlist.vars[i]->dg || tr->input.mrs->vlist.vars[i]->dg->gen == generation)?1:0;
	char	context_vars_exist[tr->context.mrs->vlist.nvars];
	for(i=0;i<tr->context.mrs->vlist.nvars;i++)
		context_vars_exist[i] = (!tr->context.mrs->vlist.vars[i]->dg || tr->context.mrs->vlist.vars[i]->dg->gen == generation)?1:0;

	// make a copy of the unified rule, so we can apply the output edits and extract things from it
	struct dg	*full_tr_copy = copy_dg_with_comp_arcs(tr->dg);
	if(!full_tr_copy)return NULL;	// cycle detected; the unification really failed but we didn't notice until now.

	// mark parts of the copy that come from parts of the rule matching nonexistant variables from min, by setting their '->xtype' to NULL
	for(i=0;i<tr->input.mrs->vlist.nvars;i++)
		if(!input_vars_exist[i])
		{
			struct mrs_var	*v = tr->input.mrs->vlist.vars[i];
			assert(v->dg->copy);
			v->dg->copy->xtype = NULL;
			//printf("rule input variable %s did not exist in mrs input\n", v->name);
		}
	for(i=0;i<tr->context.mrs->vlist.nvars;i++)
		if(!context_vars_exist[i])
		{
			assert(tr->context.mrs->vlist.vars[i]->dg->copy);
			tr->context.mrs->vlist.vars[i]->dg->copy->xtype = NULL;
		}

	// now, apply the edits specified in the OUTPUT section
	// note that in cases where output_override says something about a variable that didn't exist in the input,
	// this undoes the above marking.
	perform_override(dg_hop(full_tr_copy, lookup_fname("OUTPUT")), tr->output_override);

	// prune parts of the result that came from matching variables that didn't exist in the input
	prune_unmatched_parts(full_tr_copy);

	struct dg	*find_copied(struct dg	*rule_dg, int	must_exist)
	{
		extern unsigned int generation;
		rule_dg = dereference_dg(rule_dg);	// see where it moved during unification
		if(rule_dg->gen != generation)rule_dg = NULL;
		else rule_dg = rule_dg->copy;	// see where it moved during copying -- might not have been copied
		assert(rule_dg || !must_exist);
		if(rule_dg)assert(rule_dg->xtype);
		return rule_dg;
	}

	// make copies of all the output EPs and HCONSes -- and the input EPs too when we are working with a +copy+
	struct dg	*copy_ep_out_dgs[tr->output.neps];
	struct dg	*copy_hc_hi[tr->output.nhcons];
	struct dg	*copy_hc_lo[tr->output.nhcons];
	struct mrs_var	*copy_hc_hi_v[tr->output.nhcons];
	struct mrs_var	*copy_hc_lo_v[tr->output.nhcons];
	for(i=0;i<tr->output.neps;i++)
		copy_ep_out_dgs[i] = find_copied(tr->output.eps[i].dg, 1);
	for(i=0;i<tr->output.nhcons;i++)
	{
		copy_hc_hi[i] = find_copied(tr->output.mrs->hcons[i].hi->dg, 1);
		copy_hc_lo[i] = find_copied(tr->output.mrs->hcons[i].lo->dg, 1);
	}

	struct dg	*copy_ltop = find_copied(tr->output.mrs->ltop->dg, 1);
	struct dg	*copy_index = find_copied(tr->output.mrs->index->dg, 1);
	struct dg	*copy_xarg = tr->output.mrs->xarg?find_copied(tr->output.mrs->xarg->dg, 1):NULL;

	// we have now copied everything that we will copy;
	// figure out where old variables' dags got copied to
	for(i=0;i<min->vlist.nvars;i++)
		old_var_dg[i] = find_copied(min->vlist.vars[i]->dg, 0);
	// old_var_dg[] now are either NULL or are pointers into the new copies

	bump_generation();

	//printf("for result (after applying +copy+), tr dg is:\n");print_dg(full_tr_copy);printf("\n");

	// we have just produced three lists:
	// copy_ep_out_dgs		-- 'struct dg's representing the output EPs
	// copy_hc_hi			-- 'struct dg's representing the hi side of output HCONSs
	// copy_hc_lo			-- 'struct dg's representing the lo side of output HCONSs

	// from here on out, the job is to convert those into a new 'struct mrs', with all the right variable reentrancies

	// extract 'struct mrs_ep' and 'struct mrs_var' for the EPs and HCONSes, from the 'struct dg's we just made
	struct mrs_ep	new_eps[tr->output.neps];
	struct mrs_vlist	new_vars;
	bzero(&new_vars, sizeof(new_vars));
	struct mrs_var	*vpbuffer[1024];
	new_vars.vars = vpbuffer;

	// put it all together into a result 'struct mrs'
	struct mrs	*mout = slab_alloc(sizeof(*mout));
	bzero(mout, sizeof(*mout));

	transfer_result_dg_to_mrs(tr, &new_vars, copy_ep_out_dgs, new_eps, copy_hc_hi, copy_hc_lo, copy_hc_hi_v, copy_hc_lo_v, mout, copy_ltop, copy_index, copy_xarg);

	// figure out what new variable each old variable maps to, if any [, and assign skolem constants to new varibles -- no longer?]
	struct mrs_var	*new_var_map[min->vlist.nvars];
	compute_variable_mapping(min, &new_vars, old_var_dg, new_var_map);

	int ncarried_input_variables = 0;
	char	input_variable_is_carried[1024];//min->vlist.nvars];
	bzero(input_variable_is_carried, sizeof(input_variable_is_carried));
	make_reliable_vnums(min);
	struct mrs_var	*map_variable(struct mrs_var	*vin)
	{
		if(!vin)return NULL;
		assert(vin->vnum >= 0 && vin->vnum < min->vlist.nvars);
		assert(min->vlist.vars[vin->vnum] == vin);
		struct mrs_var	*corresponding_new_var = new_var_map[vin->vnum];
		if(corresponding_new_var)
			return corresponding_new_var;
		if(!input_variable_is_carried[vin->vnum])
		{
			input_variable_is_carried[vin->vnum] = 1;
			ncarried_input_variables++;
		}
		return vin;
	}

	transfer_top_level_variables(tr, min, mout, map_variable);
	transfer_ep_result(tr, min, mout, alignment, new_eps, map_variable);
	transfer_hcons_result(tr, min, mout, hcalignment, copy_hc_hi_v, copy_hc_lo_v, map_variable);
	transfer_icons_result(tr, min, mout, map_variable);
	transfer_vlist_result(tr, min, mout, &new_vars, ncarried_input_variables, input_variable_is_carried, map_variable);

	setup_tmp();	// make sure subsequent forget_tmp() calls don't delete our saved EP dags or MRS structure

	//printf("result mrs = ");
	//print_mrs(mout);
	return mout;
}
