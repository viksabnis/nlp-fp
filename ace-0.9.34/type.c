#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<wctype.h>

#include	"unicode.h"
#include	"hash.h"
#include	"tdl.h"
#include	"type.h"
#include	"freeze.h"
#include	"conf.h"

static struct type_hierarchy	*default_th;

struct type_hierarchy	*main_th;

struct type_hierarchy	*default_type_hierarchy() { return default_th; }
void	set_default_type_hierarchy(struct type_hierarchy	*th) { default_th = th; }

static int	init_top_type(char	*top_type)
{
	default_th->types = calloc(sizeof(struct type*), 1);
	if(add_type_only(top_type, 0, 0, 0)) return -1;
	default_th->types[0]->dg = atomic_dg(top_type);
	return 0;
}

struct type_hierarchy	*new_type_hierarchy(char	*id, char	*topname)
{
	struct type_hierarchy	*th = calloc(sizeof(struct type_hierarchy), 1);
	th->id = strdup(id);
	th->thash = hash_new("type-name-hash");

	//fprintf(stderr, "INITIALIZING hierarchy '%s' with top '%s'\n", id, topname);

	struct type_hierarchy	*tmp = default_type_hierarchy();
	set_default_type_hierarchy(th);
	if(init_top_type(topname) != 0)
	{
		fprintf(stderr, "unable to initialize top type `%s' for hierarchy `%s'\n", topname, id);
		exit(-1);
	}
	th->top = th->types[0];
	set_default_type_hierarchy(tmp);
	return th;
}

//int		ntypes;
//struct type	**types;
int		glb_type_count;

//int		nstrings;
//struct type	**strings;

struct type	*get_top() { return default_th->top; }

//struct type	*strtype = 0;

#define	THSIZE	100000
static struct type	**typehash;

extern unsigned int generation;
extern int g_loaded;

void	th_init()
{
	typehash = calloc(sizeof(struct type*), THSIZE);
}

void	inval_thash()
{
	if(typehash)
	{
		free(typehash);
		typehash = 0;
	}
}

/*unsigned int	thash(char	*name)
{
	unsigned int	h = 0;

	while(*name)
	{
		h <<= 1;
		h ^= tolower(*name++);
	}
	return h;
}*/

void	th_add(struct type	*t)
{
	hash_add(default_th->thash, t->name, t);
}

struct type	*th_look(struct type_hierarchy	*th, char	*name)
{
	char	*p;
	for(p=name;*p;p++)
		if(isalpha(*p) && isupper(*p))
			*p = tolower(*p);
	return hash_find(th->thash, name);
}

struct type	*lookup_type(char	*name)
{
	if(!default_th)
	{
		fprintf(stderr, "lookup_type(%s) called with no default type hierarchy active\n", name);
		exit(-1);
	}
	return th_lookup_type(default_th, name);
}

struct type	*th_lookup_type(struct type_hierarchy	*th, char	*name)
{
	int	i;

	if(th==main_th && (name[0]=='"' || name[0]=='\'' || name[0]=='^'))
	{
		if(!strcmp(name, "\"\\\"\""))strcpy(name, "\"\"\"");

		// elsewhere in the code we assume strings start with ".
		// the type 'foobar should be interpreted as identical to "FOOBAR"
		// (determined in 'mrs comparison' session of delphin 2012)
		if(name[0]=='\'')
		{
			wchar_t	*wname = towide(name);
			int	l = wcslen(wname);
			wchar_t	*wnewname = malloc(sizeof(wchar_t)*(l+2));
			int	i;
			wnewname[0] = '\"';
			for(i=1;wname[i];i++)
				wnewname[i] = towupper(wname[i]);
			wnewname[i] = '\"';
			wnewname[i+1] = 0;
			char	*newname = freeze_tombs(wnewname);
			free(wnewname); free(wname);
			fprintf(stderr, "WARNING: deprecated type name |%s| being interpreted as |%s|\n", name, newname);
			name = newname;
			// if 'newname' is a pre-existing string type, then the memory for 'newname' will be leaked... acceptable since it's a deprecated usage and we warn them, but also not a huge problem since it probably only happens during grammar loading.  at run time, this could be reached when dagify()ing an MRS EP with a 'neg_rel, for example.  but in that situation, the slab-allocated leak will disappear when that item is done being processed.
		}
		else if(name[0]=='^')
		{
			// regex string type... make it look like a string to make the rest of the code happy.  we only actually interpret these in lattice-mapping.c
			name[0]='"';
		}
		// auto-add strings. this does a lookup too.
		struct type_hierarchy	*tmp = default_th;
		default_th = th;
		struct type	*t = add_string(name);
		default_th = tmp;
		return t;
	}

	return th_look(th, name);
}

void	print_type(char	*name)
{
	struct type	*t = lookup_type(name);

	if(!t)
	{
		fprintf(stderr, "print_type: `%s' doesn't exist\n", name);
		return;
	}
	printf("type `%s': ", name);
	if(t->dg)print_dg(t->dg);
	else printf("not yet constrained\n");
	printf("\n\n");
}

int	descendent_of(int	dec, struct type	*of)
{
	int	i, j, k, x;

	if(!of->ndescendents)return 0;
	if(dec==default_th->ntypes-1)return dec==of->descendents[of->ndescendents-1];
	i = 0, j = of->ndescendents-1;
	while(i<j)
	{
		k = (i+j)/2;
		x = of->descendents[k];
		if(x==dec)return 1;
		else if(x<dec)i=k+1;
		else j=k-1;
	}
	return dec == of->descendents[i];
}

void	add_descendent(struct type	*anc, int	dec)
{
	int	i;

	if(dec==default_th->ntypes-1)
	{
		i=anc->ndescendents;
		if(i && anc->descendents[i-1] == dec)
			return;
	}
	else
	{
		for(i=0;i<anc->ndescendents;i++)
		{
			if(dec == anc->descendents[i])return;
			if(dec < anc->descendents[i])break;
		}
	}
	anc->ndescendents++;
	anc->descendents = realloc(anc->descendents, sizeof(short)*anc->ndescendents);
	if(i!=anc->ndescendents-1)
		memmove(anc->descendents+i+1, anc->descendents+i, sizeof(short) * (anc->ndescendents-1-i));
	anc->descendents[i] = dec;
}

struct dg	*atomic_top()
{
	return atomic_dg(default_th->top->name);
}

struct type	*temporary_string_type(char *string)
{
	struct type	*ty = slab_alloc(sizeof(*ty));

	// make a type representing 'name'
	bzero(ty, sizeof(*ty));
	ty->name = string;
	ty->dg = atomic_top();
	ty->dg->type = ty->dg->xtype = ty;
	ty->tnum = -1;	// it doesn't matter that this is reused; it's a string type, anyway

	return ty;
}

struct type	*add_string(char	*name)
{
	struct type	*t;
	int		i, j, k, r;

	int	nstrings = default_th->nstrings;
	struct type	**strings = default_th->strings;

	// binary search for existing string
	for(i=0,j=nstrings-1;i<=j;)
	{
		k = (i+j)/2;
		r = strcmp(strings[k]->name, name);
		if(r==0)return strings[k];

		if(r<0)i = k+1;
		else j = k-1;
	}
	// i is (conveniently) the right place to insert

	if(g_loaded)
		return temporary_string_type(name);

	nstrings++;
	if(FROZEN(strings))
	{
		struct type **str = malloc(sizeof(struct type*)*nstrings);
		memcpy(str, strings, sizeof(struct type*)*(nstrings-1));
		strings = str;
	}
	else strings = realloc(strings, sizeof(struct type*) * nstrings);
	default_th->strings = strings;
	default_th->nstrings = nstrings;

	t = calloc(sizeof(struct type), 1);

	memmove(strings+i+1, strings+i, sizeof(struct type*) * (nstrings-1-i));
	strings[i] = t;

	t->name = strdup(name);
	t->ndescendents = 0;
	t->descendents = 0;
	t->dg = 0;
	t->tnum = -1;//nstrings-1;

	return t;
}

void	number_strings()
{
	int	i;

	for(i=0;i<default_th->nstrings;i++)default_th->strings[i]->tnum = i;
}

int	add_type_only(char	*name, int	npar, struct type	**par, int	overwrite)
{
	struct type	*t;
	int		i, pari, lexical = 0;

	char	*c;
	int	did_lower = 0;
	for(c=name;*c;c++)
	{
		if(isalpha(*c) && isupper(*c))
		{
			/*if(!did_lower)
			{
				fprintf(stderr, "warning: downcasing type name '%s'\n", name);
				did_lower = 1;
			}*/
			*c = tolower(*c);
		}
	}

	/*fprintf(stderr, "new type `%s' inherits from:", name);
	for(i=0;i<npar;i++)
	{
		fprintf(stderr, " %s", par[i]->name);
	}
	fprintf(stderr, "\n");*/

	t = th_look(default_th, name);
	if(t)
	{
		if(!overwrite)
		{
			fprintf(stderr, "type: `%s' already declared, go away!\n", name);
			return -1;
		}
		else
		{
			// SEM-I type definition is supposed to be revokable...
			// i.e. we can come in later and say "actually, this type is NOT a parent of that type."
			// the call to setup_type_lineage() below will overwrite parent info.
			// SEM-I construction calls rebuild_th() after completion, to get descendent and daughter links right.
		}
	}
	else
	{
		t = calloc(sizeof(struct type), 1);
		default_th->ntypes++;
		default_th->types = realloc(default_th->types, sizeof(struct type*) * default_th->ntypes);
		default_th->types[default_th->ntypes-1] = t;
		t->name = strdup(name);
		t->ndescendents = 0;
		t->descendents = 0;
		t->dg = NULL;
		if(!strcasecmp(name, "string"))default_th->strtype = t;	// XXX hardcoded type name
		t->tnum = default_th->ntypes-1;
		th_add(t);
	}

	if(npar>=0)setup_type_lineage(t, npar, par);
	return 0;
}

void	add_to_ancestors(struct type	*a, int	tnum)
{
	if(descendent_of(tnum, a))return;
	add_descendent(a, tnum);
	int i;
	for(i=0;i<a->nparents;i++)
		add_to_ancestors(a->parents[i], tnum);
}

setup_type_lineage(struct type	*t, int	npar, struct type	**par)
{
	int i;
	t->nparents = npar;
	t->parents = malloc(sizeof(struct type*) * npar);
	memcpy(t->parents, par, sizeof(struct type*) * npar);

	for(i=0;i<npar;i++)
	{
		struct type	*p = par[i];
		p->ndaughters++;
		p->daughters = realloc(p->daughters, sizeof(struct type*) * p->ndaughters);
		p->daughters[p->ndaughters-1] = t;
	}

	//fprintf(stderr, " - linking\n");
	add_to_ancestors(t, t->tnum);

	return 0;
}

extern int		g_loaded;

int	constrain_type(char	*name, struct dg	*dg, struct tdl_line	*tdl)
{
	struct type	*type = lookup_type(name);

	assert(dg != NULL);
	if(!type)
	{
		fprintf(stderr, "type: tried to constrain type `%s' which doesn't exist yet\n", name);
		return -1;
	}
	type->dg = copy_dg(dg);
	if(!type->dg)
	{
		fprintf(stderr, "type: cyclic dag specified for type `%s'\n", name);
		return -1;
	}

	type->dg->type = type->dg->xtype = type;
	type->tdl = tdl;

	//printf("type: %s	definition: %s\n", tdl->lhs, tdl->rhs);
	//print_dg(type->dg); printf("\n");
	return 0;
}

struct type	*most_general_type_for_dg(struct dg	*d);
int		wfpath[1024], wfpl = 0;

long top_unifies_wellform;

int	wellforming_th = 0, nwfu;
char	*wellforming_th_map;
begin_wellforming_th(struct type_hierarchy	*th)
{
	wellforming_th = 1;
	nwfu = 0;
	wellforming_th_map = calloc(th->ntypes, 1);
}
int end_wellforming_th()
{
	wellforming_th = 0;
	free(wellforming_th_map);
	return nwfu;
}
struct type	*wellforming_type;
now_wellforming_type(struct type	*t)
{
	wellforming_type = t;
}
mark_as_updated() { if(wellforming_th)wellforming_th_map[wellforming_type->tnum] = 1; nwfu++; }
int	type_has_been_updated(struct type	*t)
{
	if(t->name[0]=='"')return 0;
	return wellforming_th_map[t->tnum];
}

// make children well-formed
int	wellform(struct dg	*d, char	*typename)
{
	int		i;
	struct type	*t;
	extern char	**fnames;
	struct dg	**arcs = DARCS(d);
	extern int g_mode, debug_level;

	for(i=0;i<d->narcs;i++)
	{
		arcs[i] = dereference_dg(arcs[i]);
		if(arcs[i]->gen != generation)
		{
			arcs[i]->type = arcs[i]->xtype;
			arcs[i]->forwarded = 0;
			arcs[i]->copy = 0;
			arcs[i]->ncarcs = 0;
			arcs[i]->carcs = 0;
			arcs[i]->gen = generation;
		}
		wfpath[wfpl++] = d->label[i];
		int wellform_result = wellform(arcs[i], typename);
		if(wellform_result != 0)return -1;
		t = most_general_type_for_dg(arcs[i]);
		if(!t)
		{
			if(debug_level || g_mode==-1)
			{
				fprintf(stderr, "well-formedness: no type is compatible with features and type of `%s'\n", arcs[i]->xtype->name);
				fprintf(stderr, "	while processing `%s'\n", typename);
			}
			return -1;
		}
		if(t != arcs[i]->xtype || (wellforming_th && type_has_been_updated(t)))
		{
			/*printf("well-formedness forces dag `%s' -> `%s'  (inside constraint for type %s)\n", arcs[i]->xtype->name, t->name, typename);
			int j;
			for(j=0;j<wfpl;j++)
				printf("%s ", fnames[wfpath[j]]);
			printf("\n");*/
			if(!descendent_of(t->tnum, arcs[i]->xtype))
			{
				if(debug_level || g_mode==-1)
				{
					fprintf(stderr, "unexpected well-formedness constraint forces dag `%s' to become more general type `%s'!\n", arcs[i]->xtype->name, t->name);
					fprintf(stderr, "	while processing `%s'\n", typename);
				}
				return -1;
			}
			top_unifies_wellform++;
			if(unify_dg_infrom(arcs[i], copy_dg(t->dg)))
			{
				if(debug_level || g_mode==-1)
				{
					int j;
					fprintf(stderr, "entity `%s' failed well-formedness constraint!\n", typename?typename:"(unknown)");
					fprintf(stderr, "at path: ");
					for(j=0;j<wfpl;j++)
						fprintf(stderr, "%s ", fnames[wfpath[j]]);
					fprintf(stderr, "\n");
					fprintf(stderr, "reason: unable to unify with type `%s'\n", t->name);
	#ifdef	UNIFY_PATHS
					funify_backtrace(stderr);
	#endif
					fprintf(stderr, "partly unified dag fragment from entity to be wellformed:\n");
					fprint_dg(stderr, arcs[i]);fprintf(stderr, "\n");
					fprintf(stderr, "dag type to be wellformed:\n");
					fprint_dg(stderr, t->dg);fprintf(stderr, "\n");
				}
				return -1;
			}
			if(wellforming_th)
				mark_as_updated();
			/*printf("now:\n");
			print_dg(arcs[i]);printf("\n");
			printf("\n");*/
		}
		wfpl--;
	}
	return 0;
}

int	constrain_glbs_and_wellformedness()
{
	int	i, j, descbytes = 0;

	fix_glbs();

	for(i=0;i<default_th->ntypes;i++)
	{
		default_th->types[i]->dg = dereference_dg(default_th->types[i]->dg);
		// introduce top-level features for this type, it might be the most general type for them
		//printf("pre-welformed dag for `%s':\n", default_th->types[i]->name);
		//print_dg(default_th->types[i]->dg); printf("\n\n");
		for(j=0;j<default_th->types[i]->dg->narcs;j++)
			introduce_feature(default_th->types[i]->dg->label[j], i);
	}
	number_strings();	// just in case

	// XXX hack!  why do this?  ran into a real case where this caused a generation crash....
	//generation = 11;
	// XXX hack!

	int	first_time = 1;
	again:
	begin_wellforming_th(default_th);
	if(first_time)
	{
		for(i=0;i<default_th->ntypes;i++)
			wellforming_th_map[i] = 1;
		first_time = 0;
	}
	descbytes = 0;
	for(i=0;i<default_th->ntypes;i++)
	{
		//printf("well-forming `%s', current dag:\n", default_th->types[i]->name);
		//print_dg(default_th->types[i]->dg); printf("\n");
		now_wellforming_type(default_th->types[i]);
		int wellform_result = wellform(default_th->types[i]->dg, default_th->types[i]->name);
		assert(wellform_result == 0);
		descbytes += default_th->types[i]->ndescendents * sizeof(short);
		//printf("after wellforming, final dag:\n");
		//print_dg(default_th->types[i]->dg); printf("\n");
	}
	int changes = end_wellforming_th();
	if(changes)
	{
		//printf("wellforming type hierarchy: %d changes on that pass\n", changes);
		goto again;
	}
	//printf("no changes\n");

	return 0;
}

void	init_type_hierarchy()
{
	main_th = new_type_hierarchy("main", top_type);
	if(!main_th)exit(-1);
	set_default_type_hierarchy(main_th);
}

int	load_types()
{
extern int enable_out_of_order;
int	typify_tdl_line(struct tdl_line	*line, void	*ref);

	enable_out_of_order = 1;
	process_tdl_status("type", typify_tdl_line, 0);

	run_task("checking for glbs...", make_glbs);

	process_tdl_dgs_status("type", constrain_type);
	enable_out_of_order = 0;

	run_task("processing constraints...", constrain_glbs_and_wellformedness);
	return 0;
}


struct type	*lub(struct type	*a, struct type	*b)
{
	if(a==b)return a;

	int	tn = a->tnum;
	if(b->tnum < tn)tn = b->tnum;

	if(a->name[0]=='"')return lub(default_th->strtype, b);
	if(b->name[0]=='"')return lub(a, default_th->strtype);
	while(tn >= 0)
	{
		if(descendent_of(a->tnum, default_th->types[tn]))
			if(descendent_of(b->tnum, default_th->types[tn]))
				return default_th->types[tn];
		tn--;
	}
	fprintf(stderr, "no upper bound for '%s' and '%s'\n", a->name, b->name);
	assert(!"no upper bound found");
}

char	*type_to_string(struct type	*ty)
{
	assert(ty->name[0]=='"');
	int	i, slen = strlen(ty->name)-2, alen = slen + 1;
	assert(slen >= 0 && ty->name[slen+1]=='"');
	if(alen%4)alen = (alen&~3)+4;
	char	*s = slab_alloc(alen);
	sprintf(s, "%.*s", slen, slab_unescape(ty->name+1));
	return s;
}

struct type	*string_to_type(char	*str)
{
	str = slab_escape(str);
	int	i, slen = strlen(str), alen = slen + 3;
	if(alen%4)alen = (alen&~3)+4;
	char	*s = slab_alloc(alen);
	sprintf(s, "\"%.*s\"", slen, str);
	struct type	*t = lookup_type(s);
	return t;
}
