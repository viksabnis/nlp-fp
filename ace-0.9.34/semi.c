#define		_GNU_SOURCE
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>
#include	<wctype.h>

#include	"tdl.h"
#include	"dag.h"
#include	"hash.h"
#include	"conf.h"
#include	"unicode.h"

struct type_hierarchy	*semi_th, *semi_p_th;

enum
{
	semi_variables = 1,
	semi_properties = 2,
	semi_roles = 3,
	semi_predicates = 4
};

int	semi_mode = 0;

int	isoperator(char	c)
{
	if(c==':')return 1;
	if(c=='<')return 1;
	if(c==',')return 1;
	if(c=='[')return 1;
	if(c==']')return 1;
	if(c=='{')return 1;
	if(c=='}')return 1;
	if(c=='&')return 1;
	if(c=='.')return 1;
	else return 0;
}

struct type	*semi_super;//, *semi_top;

void	semi_set_super(char	*what)
{
	if(!strcmp(what, "semi-predicate"))set_default_type_hierarchy(semi_th);
	else set_default_type_hierarchy(semi_p_th);

	if(!lookup_type(what))
	{
		//printf("adding %s as a subtype of %p\n", what, semi_top);
		struct type	*semi_top = lookup_type(semi_top_type);
		add_type_only(what, 1, &semi_top, 0);
	}
	semi_super = lookup_type(what);
	//semi_super = semi_top;
}

int	process_semi_command(char	*parent, int	lnum, char	*cmd)
{
	if(0) {}
	else if(!strcasecmp(cmd, "variables:"))
	{
		semi_mode = semi_variables;
		semi_set_super("semi-variable");
	}
	else if(!strcasecmp(cmd, "properties:"))
	{
		semi_mode = semi_properties;
		semi_set_super("semi-property");
	}
	else if(!strcasecmp(cmd, "roles:"))
	{
		semi_mode = semi_roles;
		semi_super = NULL;
	}
	else if(!strcasecmp(cmd, "predicates:"))
	{
		semi_mode = semi_predicates;
		semi_set_super("semi-predicate");
	}
	else
	{
		fprintf(stderr, "%s:%d:  unknown SEMI command: `%s'\n", parent, lnum, cmd);
		exit(-1);
	}
	return 0;
}

char	semi_peek(char	**P)
{
	char	*p = *P;
	while(isspace(*p))
		p++;
	return *p;
}

char	*semi_tokenize(char	**P, int	*L)
{
	char	*p = *P;
	// skip to end of whitespace
	while(isspace(*p))
	{
		if(*p=='\n')(*L)++;
		p++;
	}
	*P = p;
	// anything left?
	if(!*p)return NULL;
	// skip comments
	if(*p == ';')
	{
		while(*p && *p!='\n')p++;
		*P=p;
		return semi_tokenize(P,L);
	}
	// punctuation tokens are single letter tokens
	if(isoperator(*p))
	{
		char	*tok = malloc(2);
		tok[0]=*p++;
		tok[1]=0;
		*P=p;
		return tok;
	}
	// all other tokens extend until whitespace or a punctuation mark
	else
	{
		char	*ts = p;
		// special case 1: ':' can appear inside an identifier (but cannot start one).
		// special case 2: '.' can appear inside an identifier (but cannot start or end one).
		while(*p && !isspace(*p) && (*p==':' || (*p=='.' && !isspace(p[1])) || !isoperator(*p)))p++;
		char	*tok = malloc(p-ts+1);
		memcpy(tok,ts,p-ts);
		tok[p-ts]=0;
		*P=p;
		return tok;
	}
}

int	ndefs, adefs;
struct semi_def
{
	char	*name;
	int		npar;
	char	**par;
	int		active;
}	*defs;

void semi_define_immediately(char	*name)
{
	if(lookup_type(name))return;
	add_type_only(name, 1, &semi_super, 0);
}

semi_define(char	*name, int	npar, char	**par)
{
	if(ndefs+1 > adefs)
	{
		adefs = (adefs+1)*1.5;
		defs = realloc(defs, sizeof(struct semi_def)*adefs);
	}
	defs[ndefs].name = strdup(name);
	defs[ndefs].npar = npar;
	defs[ndefs].par = malloc(sizeof(char*)*npar);
	defs[ndefs].active = 0;
	memcpy(defs[ndefs].par, par, sizeof(char*)*npar);
	ndefs++;
}

struct type	*semi_process_1_def(struct semi_def	*d)
{
	if(d->active)
	{
		if(d->active==2)return lookup_type(d->name);	// already did this.
		fprintf(stderr, "ERROR: SEM-I: %s is part of a circular hierarchy\n", d->name);
		exit(-1);
	}
	d->active = 1;
	//printf("process definition of %s\n", d->name);
	assert(d->npar > 0);
	int j;
	struct type	*par[d->npar];
	for(j=0;j<d->npar;j++)
	{
		par[j] = lookup_type(d->par[j]);
		if(!par[j])
		{
			int k;
			for(k=0;k<ndefs;k++)if(!strcmp(defs[k].name,d->par[j]))break;
			if(k >= ndefs)
			{
				//fprintf(stderr, "ERROR: SEM-I: %s (parent of %s) undefined\n", d->par[j], d->name);
				//exit(-1);
				//printf("SEM-I: %s (parent of %s) undefined, adding implicitly at top of predicate hierarchy\n", d->par[j], d->name);
				add_type_only(d->par[j], 1, &semi_super, 0);
				par[j] = lookup_type(d->par[j]);
			}
			else par[j] = semi_process_1_def(&defs[k]);
		}
		assert(par[j] != NULL);
	}
	add_type_only(d->name, d->npar, par, 1);
	d->active = 2;
	return lookup_type(d->name);
}

void semi_process_definitions()
{
	int i;
	// visit defs in an order s.t. parents are defined before subtypes
	for(i=0;i<ndefs;i++)
		semi_process_1_def(&defs[i]);
	ndefs = 0;
}

semi_declare_role(char	*role, char	*value)
{
	//printf("semi role: %s : %s\n", role, value);
}

// find_type is from tdl.c
struct type	*find_type(char	*name, int	constrain);

process_semi_declaration(char	*path, char	**P, int	*Lnum, char	*lhs)
{
	//printf("processing declaration for %s:%d `%s'\n", path, *Lnum, lhs);
	char	*end = semi_tokenize(P, Lnum);
	assert(end && *end && isoperator(*end));
	switch(semi_mode)
	{
		case	semi_variables:;
		case	semi_properties:;
		case	semi_predicates:;
			int	npars = 0;
			char	*pars[100];
			// read supertypes
			while(*end!='.' && *end!=':')
			{
				assert(*end=='<' || *end=='&');
				free(end);
				char	*parent = semi_tokenize(P, Lnum);
				assert(parent && *parent);
				pars[npars++] = parent;
				end = semi_tokenize(P, Lnum);
				assert(end&&*end);
				assert(npars<100);
			}
			// read appropriate properties / roles
			if(semi_mode == semi_properties)assert(*end=='.');
			else while(*end!='.')
			{
				assert(*end==':' || *end==',');
				free(end);
				char	*feature = semi_tokenize(P, Lnum);
				assert(feature && *feature);
				int optional = 0;
				if(!strcmp(feature, "["))
				{
					optional = 1;
					free(feature);
					feature = semi_tokenize(P, Lnum);
					assert(feature && *feature);
				}
				char	*value = semi_tokenize(P, Lnum);
				assert(value && *value);
				//printf("appropriate to %s: [ %s %s ]\n", lhs, feature, value);
				if(semi_peek(P)=='{')
				{
					char	*brace = semi_tokenize(P, Lnum);
					assert(brace && !strcmp(brace,"{"));free(brace);
					do {
						char	*prop = semi_tokenize(P, Lnum);
						assert(prop&&*prop);
						char	*val = semi_tokenize(P, Lnum);
						assert(val&&*val);
						//printf(" ... with properties %s = %s\n", prop, val);
						brace = semi_tokenize(P, Lnum);
					} while(brace && !strcmp(brace,","));
					if(!brace || strcmp(brace,"}"))
					{
						fprintf(stderr, "ERROR: SEM-I syntax at %s:%d ; expected '}', found '%s'\n", path, *Lnum, brace);
						exit(-1);
					}
					assert(brace && !strcmp(brace,"}"));free(brace);
				}
				if(optional)
				{
					char	*closebracket = semi_tokenize(P, Lnum);
					assert(closebracket && !strcmp(closebracket, "]"));
					free(closebracket);
				}
				end = semi_tokenize(P, Lnum);
				assert(end&&*end);
			}
			free(end);
			if(!npars)semi_define_immediately(lhs);
			else semi_define(lhs, npars, pars);
			break;
		case	semi_roles:;
			assert(*end==':');
			free(end);
			char	*value = semi_tokenize(P, Lnum);
			assert(value && *value);
			semi_declare_role(lhs, value);
			if(**P=='.')
			{
				end = semi_tokenize(P, Lnum);
				free(end);
			}
			break;
		default: assert(!"no semi mode!");
	}
}

load_semi_path(char	*path)
{
	FILE	*f = fopen(path, "r");
	if(!f){perror(path);exit(-1);}
	fseek(f, 0, SEEK_END);
	long	len = ftell(f);
	rewind(f);
	char	*buffer = malloc(len+1);
	assert(len == fread(buffer, 1, len, f));
	buffer[len] = 0;
	fclose(f);

	char	*p = buffer, *key;
	int	lnum = 1;
	while(key = semi_tokenize(&p, &lnum))
	{
		assert(*key);
		//printf("%s main loop |%s|\n", path, key);
		if(key[strlen(key)-1]==':')
		{
			if(!strcmp(key, "include:"))
			{
				char	*file = semi_tokenize(&p, &lnum);
				assert(file && *file);
				char	*iname = path_for_include(path, file, ".smi");
				//fprintf(stderr, "SEMI INCLUDE %s\n", iname);
				load_semi_path(iname);
				free(iname);
				free(file);
			}
			else
			{
				semi_process_definitions();
				process_semi_command(path, lnum, key);
			}
		}
		else process_semi_declaration(path, &p, &lnum, key);
		free(key);
	}
	free(buffer);
}

extern int	g_normalize_predicates;

int	load_semi(char	*path)
{
	struct type_hierarchy	*main_th = default_type_hierarchy();
	if(!path)
	{
		semi_th = main_th;
		semi_p_th = main_th;
		return 0;
	}
	g_normalize_predicates = 1;
	semi_th = new_type_hierarchy("semi", semi_top_type);
	semi_p_th = new_type_hierarchy("semi-prop", semi_top_type);
	set_default_type_hierarchy(semi_th);
	load_semi_path(path);
	semi_process_definitions();
	rebuild_hierarchy(0, semi_th);	// BECAUSE we allow overwriting parent lists (see email from oe Mar-15-2017)
	make_glbs();
	set_default_type_hierarchy(semi_p_th);
	rebuild_hierarchy(0, semi_p_th);	// BECAUSE we allow overwriting parent lists (see email from oe Mar-15-2017)
	make_glbs();
	set_default_type_hierarchy(main_th);
}
