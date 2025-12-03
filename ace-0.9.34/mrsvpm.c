#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

#include	"freeze.h"
#include	"mrs.h"
#include	"dag.h"

struct vpm
{
	char	*inputh, *outputh;	// type hierarchy names
	char	*filename;
	struct vpm_context
	{
		int		ninput, noutput;
		char	**input, **output;
		struct vpm_rule
		{
			char			**input, **output;
			#define	VPM_INPUT_TO_OUTPUT	0x1
			#define	VPM_OUTPUT_TO_INPUT	0x2
			#define	VPM_BIDIRECTIONAL	(VPM_INPUT_TO_OUTPUT | VPM_OUTPUT_TO_INPUT)
			unsigned		direction:2;
			unsigned		require_equality:1;
		}	*rules;
		int	nrules;
	}		*contexts;
	int		ncontexts;
};

static struct vpm *parser_v, *parser_vinv;
static struct vpm *transfer_input_v;
static struct vpm *transfer_output_v;

struct vpm	*invert_vpm(struct vpm	*v)
{
	if(!v)return NULL;
	struct vpm	*vpm = malloc(sizeof(*v));
	struct vpm_context *ctx, *fctx;
	struct vpm_rule	*r, *fr;
	int			i, j, k;

	vpm->ncontexts = v->ncontexts;
	vpm->contexts = malloc(sizeof(struct vpm_context)*vpm->ncontexts);
	vpm->inputh = v->outputh;
	vpm->outputh = v->inputh;
	for(i=0;i<vpm->ncontexts;i++)
	{
		ctx = v->contexts+i;
		fctx = vpm->contexts+i;
		*fctx = *ctx;
		fctx->ninput = ctx->noutput;
		fctx->noutput = ctx->ninput;
		fctx->output = ctx->input;
		fctx->input = ctx->output;
		fctx->rules = malloc(sizeof(struct vpm_rule)*ctx->nrules);
		fctx->nrules = ctx->nrules;
		for(j=0;j<ctx->nrules;j++)
		{
			r = ctx->rules+j;
			fr = fctx->rules+j;
			fr->direction = (r->direction==VPM_BIDIRECTIONAL)?r->direction:(r->direction^VPM_BIDIRECTIONAL);
			fr->require_equality = r->require_equality;
			fr->output = r->input;
			fr->input = r->output;
		}
	}
	return vpm;
}

/*char	*type_for_empty_if_rule(char	*token)
{
	int	sl=strlen(token);
	if(! (token[0]=='[' && token[sl-1]==']'))return NULL;
	token = freeze_string(token+1);
	token[sl-2] = 0;
	return token;
}*/

struct vpm	*load_vpm(char	*path)
{
	FILE	*f;
	char	line[1024], *args[32], *p;
	int		nargs, iop, i, lnum=0;
	struct vpm_context *ctx;
	struct vpm			vpm = {.inputh = 0, .outputh = 0, .ncontexts = 0, .contexts = 0};

	if(!path)return NULL;
	f = fopen(path, "r");
	if(!f)
	{
		perror(path);
		exit(-1);
		return NULL;
	}
	vpm.filename = freeze_string(path);
	vpm.ncontexts++;
	vpm.inputh = freeze_string("avm");
	vpm.outputh = freeze_string("mrs");
	ctx = vpm.contexts = slab_alloc(sizeof(*ctx));
	bzero(ctx, sizeof(*ctx));
	ctx->input = slab_alloc(sizeof(char*));	ctx->input[0]=freeze_string(""); ctx->ninput = 1;
	ctx->output = slab_alloc(sizeof(char*));	ctx->output[0]=freeze_string(""); ctx->noutput = 1;
	while(!feof(f) && (p = fgets(line, 1023, f)) != NULL)
	{
		++lnum;
		nargs = 0; args[0] = 0;
		while(*p)
		{
			if(*p==';' || *p=='\n' || *p=='\r'){*p=0; break;}
			if(*p==' ' || *p=='\t'){*p=0; if(args[nargs])args[++nargs]=0; }
			else if(!args[nargs])args[nargs] = p;
			p++;
		}
		if(args[nargs])nargs++;
		else if(!nargs)continue;
		else if(nargs<3)
		{
			syntax:
			fprintf(stderr, "vpm: syntax error on line %d, LHS op RHS expected\n", lnum);
			exit(-1);
			return NULL;
		}

		for(iop=1;iop<nargs-1;iop++)
			if(!strcmp(args[iop], "<>") || !strcmp(args[iop], "<<") || !strcmp(args[iop], ">>") || !strcmp(args[iop], ":") || !strcmp(args[iop], "==") || !strcmp(args[iop], "<=") || !strcmp(args[iop], "=>"))break;
		if(iop==nargs-1)goto syntax;

		if(args[iop][0]==':')
		{
			// set context
			vpm.ncontexts++;
			vpm.contexts = slab_realloc(vpm.contexts,
				sizeof(struct vpm_context)*(vpm.ncontexts-1),
				sizeof(struct vpm_context)*vpm.ncontexts);
			ctx = vpm.contexts + vpm.ncontexts-1;
			ctx->ninput = iop; ctx->noutput = nargs-iop-1;
			ctx->input = slab_alloc(sizeof(char*)*ctx->ninput);
			ctx->output = slab_alloc(sizeof(char*)*ctx->noutput);
			for(i=0;i<ctx->ninput;i++)ctx->input[i] = freeze_string(args[i]);
			for(i=0;i<ctx->noutput;i++)ctx->output[i] = freeze_string(args[iop+1+i]);
			ctx->rules = 0;
			ctx->nrules = 0;
		}
		else
		{
			struct vpm_rule r;
			int	ninput = iop, noutput = nargs-iop-1;
			int	directionality = VPM_BIDIRECTIONAL;

			bzero(&r,sizeof(r));
			// check for directionality
			int	require_equality = 0;
			if(!strcmp(args[iop], "<<"))
				directionality = VPM_OUTPUT_TO_INPUT;
			if(!strcmp(args[iop], ">>"))
				directionality = VPM_INPUT_TO_OUTPUT;
			if(!strcmp(args[iop], "=="))
			{
				directionality = VPM_BIDIRECTIONAL;
				require_equality = 1;
			}
			if(!strcmp(args[iop], "=>"))
			{
				directionality = VPM_INPUT_TO_OUTPUT;
				require_equality = 1;
			}
			if(!strcmp(args[iop], "<="))
			{
				directionality = VPM_INPUT_TO_OUTPUT;
				require_equality = 1;
			}
			if(ninput != ctx->ninput || noutput != ctx->noutput)
			{
				fprintf(stderr, "vpm: syntax error on line %d, %d/%d context but %d/%d rule\n",
					lnum, ctx->ninput, ctx->noutput, iop, nargs-iop-1);
				exit(-1);
				return NULL;
			}
			r.direction = directionality;
			r.require_equality = require_equality;
			r.input = slab_alloc(sizeof(char*)*ctx->ninput);
			for(i=0;i<ctx->ninput;i++)
			{
				if(args[i][0]=='[')	// for rules like "[e]", only record "[e" to make it easier to test with them
					args[i][strlen(args[i])-1] = 0;
				r.input[i] = freeze_string(args[i]);
			}
			r.output = slab_alloc(sizeof(char*)*ctx->noutput);
			for(i=0;i<ctx->noutput;i++)
			{
				if(args[iop+1+i][0]=='[')
					args[iop+1+i][strlen(args[iop+1+i])-1] = 0;
				r.output[i] = freeze_string(args[iop+1+i]);
			}
			ctx->nrules++;
			ctx->rules = slab_realloc(ctx->rules,
				sizeof(struct vpm_rule)*(ctx->nrules-1),
				sizeof(struct vpm_rule)*ctx->nrules);
			ctx->rules[ctx->nrules-1] = r;
		}
	}
	struct vpm	*v;
	v = slab_alloc(sizeof(vpm));
	*v = vpm;
	return v;
}

int	load_parser_vpm(char	*path)
{
	parser_v = load_vpm(path);
}

int	load_transfer_input_vpm(char	*path)
{
	transfer_input_v = load_vpm(path);
}

int	load_transfer_output_vpm(char	*path)
{
	transfer_output_v = load_vpm(path);
}

int	load_transfer_bidir_vpm(char	*path)
{
	transfer_output_v = load_vpm(path);
	transfer_input_v = invert_vpm(transfer_output_v);
}

void	print_vpm(struct vpm	*v)
{
	int i;
	printf("vpm [%s # %s] has %d contexts:\n", v->inputh, v->outputh, v->ncontexts);
	for(i=0;i<v->ncontexts;i++)
	{
		int j;
		struct vpm_context	*ctx = v->contexts+i;
		printf("input context:"); for(j=0;j<ctx->ninput;j++)printf("	%s", ctx->input[j]); printf("\n");
		printf("output context:"); for(j=0;j<ctx->noutput;j++)printf("	%s", ctx->output[j]); printf("\n");
		for(j=0;j<ctx->nrules;j++)
		{
			struct vpm_rule *r = ctx->rules+j;
			int k;
			if(r->direction == VPM_BIDIRECTIONAL)
				printf("bidirectional rule:\n");
			if(r->direction == VPM_INPUT_TO_OUTPUT)
				printf("forward-only rule:\n");
			if(r->direction == VPM_OUTPUT_TO_INPUT)
				printf("backward-only rule:\n");
			printf("  input types:");
			for(k=0;k<ctx->ninput;k++)
				printf("	%s", r->input[k]);
			printf("\n");
			printf("  output types:");
			for(k=0;k<ctx->noutput;k++)
				printf("	%s", r->output[k]);
			printf("\n");
		}
	}
}

struct vpm_freezer
{
	struct vpm	*parser_v;
	struct vpm	*transfer_input_v;
	struct vpm	*transfer_output_v;
};

void	*freeze_one_vpm(struct vpm	*v)
{
	if(!v)return NULL;
	struct vpm	*vpm = freeze_block(v, sizeof(*v));
	struct vpm_context *ctx, *fctx;
	struct vpm_rule	*r, *fr;
	int			i, j, k;

	vpm->contexts = slab_alloc(sizeof(struct vpm_context)*vpm->ncontexts);
	vpm->ncontexts = v->ncontexts;
	vpm->inputh = freeze_string(v->inputh);
	vpm->outputh = freeze_string(v->outputh);
	for(i=0;i<vpm->ncontexts;i++)
	{
		ctx = v->contexts+i;
		fctx = vpm->contexts+i;
		*fctx = *ctx;
		fctx->input = slab_alloc(sizeof(char*)*ctx->ninput);
		fctx->output = slab_alloc(sizeof(char*)*ctx->noutput);
		for(j=0;j<ctx->ninput;j++)
			fctx->input[j] = freeze_string(ctx->input[j]);
		for(j=0;j<ctx->noutput;j++)
			fctx->output[j] = freeze_string(ctx->output[j]);
		fctx->rules = slab_alloc(sizeof(struct vpm_rule)*ctx->nrules);
		fctx->nrules = ctx->nrules;
		for(j=0;j<ctx->nrules;j++)
		{
			r = ctx->rules+j;
			fr = fctx->rules+j;
			fr->direction = r->direction;
			fr->require_equality = r->require_equality;
			fr->input = slab_alloc(sizeof(char*)*ctx->ninput);
			fr->output = slab_alloc(sizeof(char*)*ctx->noutput);
			for(k=0;k<ctx->ninput;k++)
				fr->input[k] = freeze_string(r->input[k]);
			for(k=0;k<ctx->noutput;k++)
				fr->output[k] = freeze_string(r->output[k]);
		}
	}
	return vpm;
}

void	*freeze_vpm()
{
	struct vpm_freezer	*frz = slab_alloc(sizeof(*frz));
	frz->parser_v = freeze_one_vpm(parser_v);
	frz->transfer_input_v = freeze_one_vpm(transfer_input_v);
	frz->transfer_output_v = freeze_one_vpm(transfer_output_v);
	return frz;
}

void recover_vpm(void *frzer)
{
	struct vpm_freezer	*frz = frzer;
	parser_v = frz->parser_v;
	transfer_input_v = frz->transfer_input_v;
	transfer_output_v = frz->transfer_output_v;
}

extern int prop_subsumes(char*,char*);

// return 0 if value matches rule, else return nonzero
int vpm_test(char	*vartype, char *value, char *rule, int require_equality)
{
	int res;
	if(!strcmp(rule, "*"))
	{
		if(value)return 0;
		else return -1;
	}
	if(!strcmp(rule, "!"))
	{
		if(value)return -1;
		else return 0;
	}
	if(rule[0]=='[')
	{
		/* PRIOR TO March 12 2016, ACE thought:
		// semantics of "[x" rule:
		// matches iff value is missing and var is of type x
		if(value)return -1;
		else if(prop_subsumes(rule+1, vartype))return 0;
		else return -1;*/
		/* BUT NOW... */
		// semantics of "[x" rule:
		// matches if var is of type x
		if(prop_subsumes(rule+1, vartype))return 0;
		else return -1;
	}
	if(!value)return -1;
	//printf("compare `%s' vs `%s' flags %d\n", rule, value, flags);
	//if(flags & VPM_TYPE_EQUALITY)return strcasecmp(rule, value);
	if(require_equality)res = strcasecmp(rule, value);
	else res = !prop_subsumes(rule, value);
	return res;
}

static inline void	*slab_malloc(int l) { if(l%4)l += (4-(l%4)); return slab_alloc(l); }
static inline void	*slab_calloc(int a, int b) { int l = a*b; void *p = slab_malloc(l); bzero(p, l); return p; }

char	*vpm_map(char	*vartype, char	**input, struct vpm_context	*ctx, int	output_slot)
{
	int	i, j, dbg = 0;

	/*if(ctx->ninput==1 && !strcmp(ctx->input[0], "TENSE"))
	{
		printf("mapping TENSE '%s' for vartype '%s'\n", input[0], vartype);
		dbg = 1;
	}*/

	//printf("input[0] = %s\n", input[0]);

	for(i=0;i<ctx->nrules;i++)
	{
		struct vpm_rule	*r = ctx->rules+i;
		if(! (r->direction & VPM_INPUT_TO_OUTPUT))
			continue;	// only consider rules working forward
		//printf(" ... check rule '%s' => '%s'\n", r->input[0], r->output[0]);
		for(j=0;j<ctx->ninput;j++)
			if(vpm_test(vartype, input[j], r->input[j], r->require_equality) != 0)
				break;
		if(j<ctx->ninput)continue;
		// else the rule applies.
		char	*rout = r->output[output_slot];
		//printf(" ... rule '%s' fires\n", rout);
		if(!strcmp(rout, "*"))
		{
			assert(output_slot < ctx->ninput);
			return input[output_slot];
		}
		else if(!strcmp(rout, "!"))return NULL;
		else if(rout[0] == '[' && prop_subsumes(rout+1, vartype))return NULL;
		else return rout;
	}
	// for equal-sized mappings, default to identity map -- NO, don't.
	/*if(ctx->ninput == ctx->noutput)return input[output_slot];
	else */return NULL;
}

char	*convert_mrs_var_type(struct vpm	*v, char	*type)
{
	if(!v)return type;
	int	i;
	for(i=0;i<v->ncontexts;i++)
	{
		struct vpm_context	*ctx = v->contexts+i;
		if(ctx->ninput == 1 && !*ctx->input[0] && ctx->noutput == 1 && !*ctx->output[0])
		{
			// context matches root level, i.e. variable types
			char	*tout = vpm_map(type, &type, ctx, 0);
			if(!tout)tout = type;
			return tout;
		}
	}
	return type;
}

struct mrs_var	*convert_mrs_var(struct vpm *v, struct mrs_var	*vin)
{
	if(!v) { vin->refs++; return vin; }

	struct mrs_var	*vout = slab_malloc(sizeof(*vout));
	int				i, j, k;

	*vout = *vin;
	vout->name = vin->name;
	vout->type = vin->type;
	vout->nprops = 0;
	vout->props = NULL;

	static struct mrs_var_property	*tmp_props = NULL;
	if(!tmp_props)tmp_props = malloc(sizeof(struct mrs_var_property) * 1024);
	vout->props = tmp_props;
	vout->type = convert_mrs_var_type(v, vin->type);
	assert(vout->type != NULL);

	for(i=0;i<v->ncontexts;i++)
	{
		struct vpm_context *ctx = v->contexts+i;
		if(ctx->ninput==1 && !*ctx->input[0] && ctx->noutput==1 && !*ctx->output[0])
		{
		/*
			// context matches root level, i.e. variable types
			vout->type = vpm_map(vin->type, &vin->type, ctx, 0);
			if(!vout->type)
			{
				//fprintf(stderr, "WARNING: vpm did not define mapping for variable type '%s'\n", vin->type);
				// silently accept this...
				vout->type = vin->type;
			}
		*/
		}
		else
		{
			char	*values[ctx->ninput];
			int		props[ctx->ninput];
			// try to align context input to vin's properties
			for(j=0;j<ctx->ninput;j++)values[j] = NULL;
			for(j=0;j<ctx->ninput;j++)
			{
				for(k=0;k<vin->nprops;k++)
					if(!strcasecmp(vin->props[k].name, ctx->input[j]))
					{
						values[j] = vin->props[k].value;
						props[j] = k;
						break;
					}
				if(k==vin->nprops)
				{
					values[j] = NULL;
					props[j] = -1;
				}
			}
			for(j=0;j<ctx->noutput;j++)
			{
				char	*nval = vpm_map(vin->type, values, ctx, j);
				//printf("mapping values for '%s': %s...; result = %s\n", ctx->output[j], values[0], nval);
				if(!nval)continue; // don't include NULL outputs (the VPM rule drops this property in this case)
				vout->nprops++;
				assert(vout->nprops < 1024);
//				vout->props = slab_realloc(vout->props, sizeof(struct mrs_var_property)*(vout->nprops-1),
//														sizeof(struct mrs_var_property)*vout->nprops);
				vout->props[vout->nprops-1].name = ctx->output[j];
				vout->props[vout->nprops-1].value = nval;
			}
		}
	}

	vout->props = slab_alloc(sizeof(struct mrs_var_property) * vout->nprops);
	memcpy(vout->props, tmp_props, sizeof(struct mrs_var_property) * vout->nprops);
	//printf("input: ");print_mrs_var(vin);printf("\n");
	//printf("converted: ");print_mrs_var(vout);printf("\n");
	return vout;
}

struct mrs_var	*internal_to_external_mrs_var(struct mrs_var	*vin)
{
	return convert_mrs_var(parser_v, vin);
}

struct mrs_var	*external_to_internal_mrs_var(struct mrs_var	*vin)
{
	if(!parser_vinv)parser_vinv = invert_vpm(parser_v);
	return convert_mrs_var(parser_vinv, vin);
}

char		*internal_to_external_var_type(char	*in)
{
	return convert_mrs_var_type(parser_v, in);
}

char		*external_to_internal_var_type(char	*ex)
{
	if(!parser_vinv)parser_vinv = invert_vpm(parser_v);
	return convert_mrs_var_type(parser_vinv, ex);
}

// produce a copy of 'min' on the slab, with converted MRS variables
struct mrs	*convert_mrs_with_vpm(struct mrs	*min, struct vpm	*vpm)
{
	struct mrs	*mout = slab_calloc(sizeof(*mout),1);
	bzero(mout, sizeof(*mout));
	int	i, j;

	make_reliable_vnums(min);

	mout->vlist.nvars = min->vlist.nvars;
	mout->vlist.vars = slab_malloc(sizeof(struct mrs_var*) * mout->vlist.nvars);
	for(i=0;i<mout->vlist.nvars;i++)
		mout->vlist.vars[i] = convert_mrs_var(vpm, min->vlist.vars[i]);

	mout->nhcons = min->nhcons;
	mout->hcons = slab_malloc(sizeof(struct mrs_hcons) * mout->nhcons);
	for(i=0;i<mout->nhcons;i++)
	{
		struct mrs_hcons	*hin = min->hcons+i;
		struct mrs_hcons	*hout = mout->hcons+i;
		hout->type = hin->type;
		hout->hi = mout->vlist.vars[hin->hi->vnum];
		hout->lo = mout->vlist.vars[hin->lo->vnum];
	}

	mout->nicons = min->nicons;
	mout->icons = slab_malloc(sizeof(struct mrs_icons) * mout->nicons);
	for(i=0;i<mout->nicons;i++)
	{
		struct mrs_icons	*iin = min->icons+i;
		struct mrs_icons	*iout = mout->icons+i;
		iout->type = iin->type;
		iout->left = mout->vlist.vars[iin->left->vnum];
		iout->right = mout->vlist.vars[iin->right->vnum];
	}

	if(min->ltop)mout->ltop = mout->vlist.vars[min->ltop->vnum];
	if(min->index)mout->index = mout->vlist.vars[min->index->vnum];
	if(min->xarg)mout->xarg = mout->vlist.vars[min->xarg->vnum];

	mout->nrels = min->nrels;
	mout->rels = slab_calloc(sizeof(struct mrs_ep), mout->nrels);
	for(i=0;i<mout->nrels;i++)
	{
		struct mrs_ep	*ein = min->rels+i;
		struct mrs_ep	*eout = mout->rels+i;
		eout->pred = freeze_string(ein->pred);
		eout->lbl = mout->vlist.vars[ein->lbl->vnum];
		eout->epnum = ein->epnum;
		eout->cfrom = ein->cfrom;
		eout->cto = ein->cto;
		eout->nargs = ein->nargs;
		eout->args = slab_malloc(sizeof(struct mrs_ep_role) * eout->nargs);
		for(j=0;j<eout->nargs;j++)
		{
			eout->args[j].name = freeze_string(ein->args[j].name);
			eout->args[j].value = mout->vlist.vars[ein->args[j].value->vnum];
		}
	}

	return mout;
}

struct mrs	*internal_to_external_mrs(struct mrs	*min)
{
	return convert_mrs_with_vpm(min, parser_v);
}

struct mrs	*external_to_internal_mrs(struct mrs	*min)
{
	if(!parser_vinv)parser_vinv = invert_vpm(parser_v);
	return convert_mrs_with_vpm(min, parser_vinv);
}

struct mrs	*apply_transfer_input_vpm(struct mrs	*min)
{
	return convert_mrs_with_vpm(min, transfer_input_v);
}

struct mrs	*apply_transfer_output_vpm(struct mrs	*min)
{
	return convert_mrs_with_vpm(min, transfer_output_v);
}
