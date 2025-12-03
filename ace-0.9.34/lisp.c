// facilities for reading grammar configuration files written in lispy syntax,
// specifically the Version.lsp file (and maybe in the future some LKB globals.lsp and mrsglobals.lsp files)

/* LISP subsyntax parsed:
	- segments of lines following semicolons which are not in quotes are ignored
	- blocks inside #| and |# are ignored, unless the opening #| is in quotes
	- whitespace is ignored everywhere except within an identifier and within a string
	- each statement must be a list
	- values in lists may be identifiers or strings
	- identifiers are sequences of characters not including whitespace or quotes
	- strings are sequences of characters not including unescaped quotes, surrounded on both sides by double quotes

 Of all this, only the defparameter top-level command is actually interpreted,
 and its syntax is (defparameter some-identifier some-value)
 *and for now, some-value must be a string*
*/

#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

#include	"hash.h"
#include	"lisp.h"

struct hash	*lisp_parameters;

static char	*lisp_fname;
static int	lisp_lnum;

struct field
{
	struct s_exp	*value;
};

int	is_lisp_id_char(char	x)
{
	if(isalpha(x))return 1;
	if(isdigit(x))return 1;
	if(x=='*' || x=='_' || x=='+' || x=='-' || x==':')return 1;
	return 0;
}

int	is_lisp_s_exp_char(char	x)
{
	if(x==0)return 1;
	if(x=='\'')return 1;
	if(x=='(')return 1;
	if(x==')')return 1;
	if(x=='"')return 1;
	if(x=='.')return 1;
	if(is_lisp_id_char(x))return 1;
	return 0;
}

int	is_lisp_eol(char	x)
{
	if(x==0)return 1;
	if(x=='\n')return 1;
	return 0;
}

void	skip_to_eol(char	**P)
{
	while(!is_lisp_eol(**P))(*P)++;
}

void	skip_block_comment(char	**P)
{
	assert((*P)[0]=='#' && (*P)[1]=='|');
	char	*end = strstr(2+*P, "|#");
	if(!end)*P = strlen(*P) + *P;
	else *P = 2 + end;
}

int	lisp_skip_junk(char	**P)
{
	while(!is_lisp_s_exp_char(**P))
	{
		if(**P == ';')skip_to_eol(P);
		else if(strchr(" \t\n\r", **P))
		{
			if(**P == '\n')lisp_lnum++;
			(*P)++;
		}
		else if(**P == '#' && (*P)[1]=='|')skip_block_comment(P);
		else
		{
			fprintf(stderr, "%s:%d:  lisp parse error while skipping near '%.16s'\n", lisp_fname, lisp_lnum, *P);
			return -1;
		}
	}
	return 0;
}

struct s_exp	*parse_lisp_list(char	**P)
{
	assert(**P == '(');
	(*P)++;
	if(0 != lisp_skip_junk(P))return NULL;
	struct s_exp	*l = calloc(sizeof(*l),1);
	l->type = s_exp_list;
	while(**P != ')')
	{
		if(**P == '.')
		{
			if(l->len != 1 || l->type == s_exp_cons)
			{
				cons_error:
				fprintf(stderr, "%s:%d:  lisp parse error; cons cell notation in a list of length %d\n", lisp_fname, lisp_lnum, l->len);
				return NULL;
			}
			l->type = s_exp_cons;
			(*P)++;
			if(0 != lisp_skip_junk(P))return NULL;
			continue;
		}
		if(l->type == s_exp_cons && l->len > 1)goto cons_error;
		struct s_exp	*s = parse_lisp(P, 0);
		if(!s)return NULL;
		if(0 != lisp_skip_junk(P))return NULL;
		l->len++;
		l->list = realloc(l->list, sizeof(struct s_exp*)*l->len);
		l->list[l->len-1] = s;
	}
	if(l->type == s_exp_cons && l->len == 1)goto cons_error;
	assert(l->type != s_exp_cons || l->len == 2);
	assert(**P == ')');
	(*P)++;
	return l;
}

struct s_exp	*parse_lisp_string(char	**P)
{
	assert(**P == '"');
	(*P)++;
	char	*str = calloc(1,1);
	int		slen = 0;
	while(**P != '"')
	{
		char	s = **P;
		(*P)++;
		if(s == 0)
		{
			fprintf(stderr, "%s:%d:  lisp parse error in string\n", lisp_fname, lisp_lnum);
			return NULL;
		}
		if(s == '\\')
		{
			switch(**P)
			{
				case	0:
					fprintf(stderr, "%s:%d:  lisp parse error in escape sequence\n", lisp_fname, lisp_lnum);
					return NULL;
				case	'n': s = '\n'; break;
				case	't': s = '\t'; break;
				default:	s = **P; break;
			}
			(*P)++;
		}
		slen++;
		str = realloc(str, slen+1);
		str[slen-1] = s;
		str[slen] = 0;
	}
	assert(**P == '"');
	(*P)++;
	struct s_exp	*s = calloc(sizeof(*s),1);
	s->type = s_exp_str;
	s->value = str;
	return s;
}

struct s_exp	*parse_lisp_id(char	**P)
{
	assert(is_lisp_id_char(**P));
	char	*id = calloc(1,1);
	int		idlen = 0;
	while(is_lisp_id_char(**P))
	{
		idlen++;
		id = realloc(id, idlen+1);
		id[idlen-1] = **P;
		id[idlen] = 0;
		(*P)++;
	}
	if(idlen == 0)
	{
		fprintf(stderr, "%s:%d:  lisp parse error in identifier\n", lisp_fname, lisp_lnum);
		return NULL;
	}
	struct s_exp	*s = calloc(sizeof(*s),1);
	s->type = s_exp_id;
	s->value = id;
	return s;
}

struct field	*lisp_get_field(char	*name)
{
	if(!lisp_parameters)lisp_parameters = hash_new("lisp parameters");
	struct field	*f = hash_find(lisp_parameters, name);
	if(!f)
	{
		f = calloc(sizeof(*f),1);
		hash_add(lisp_parameters, strdup(name), f);
	}
	return f;
}

void	defparameter(char	*parameter, struct s_exp	*value)
{
	//printf("def %s = %s\n", parameter, value);
	struct field	*f = lisp_get_field(parameter);
	f->value = value;
}

struct s_exp	*evaluate(struct s_exp	*l)
{
	// evaluate
	if(l->len > 0 && l->list[0]->type==s_exp_id)
	{
		char	*func = l->list[0]->value;
		if(!strcasecmp(func, "defparameter"))
		{
			if(l->len != 3)
			{
				fprintf(stderr, "%s:%d: ignoring defparameter() with wrong arity\n", lisp_fname, lisp_lnum);
				return l;
			}
			if(l->list[1]->type != s_exp_id)
			{
				fprintf(stderr, "%s:%d: first argument to defparameter() must be an identifier\n", lisp_fname, lisp_lnum);
				return l;
			}
			defparameter(l->list[1]->value, l->list[2]);
		}
	}
	return l;
}

struct s_exp	*parse_lisp(char	**P, int	quoted)
{
	if(0 != lisp_skip_junk(P))return NULL;

	if(**P == '\'')
	{
		if(quoted)
		{
			fprintf(stderr, "%s:%d:  doubly quoted s-expression\n", lisp_fname, lisp_lnum);
			return NULL;
		}
		(*P)++;
		return parse_lisp(P, 1);
	}

	if(**P == 0)return NULL;
	else if(**P == ')')
	{
		fprintf(stderr, "%s:%d:  unmatched parenthesis\n", lisp_fname, lisp_lnum);
		return NULL;
	}
	else if(**P == '(')
	{
		struct s_exp	*l = parse_lisp_list(P);
		if(!quoted)l = evaluate(l);
		return l;
	}
	else if(**P == '"')return parse_lisp_string(P);
	else return parse_lisp_id(P);
}

void	lisp_print_s_exp(struct s_exp	*s)
{
	switch(s->type)
	{
		case	s_exp_str:	printf("\"%s\"", s->value);	return;
		case	s_exp_id:	printf("%s", s->value); return;
		case	s_exp_list:
			{ int i;
			printf("(");
			for(i=0;i<s->len;i++)
			{
				if(i)printf(" ");
				lisp_print_s_exp(s->list[i]);
			}
			printf(")");
		return; }
	}
}

void	load_lisp(char	*path)
{
	FILE	*f = fopen(path, "r");
	if(!f) { perror(path); exit(-1); }
	fseek(f, 0, SEEK_END);
	long	len = ftell(f);
	rewind(f);
	char	*buffer = malloc(len+1);
	assert(len == fread(buffer, 1, len, f));
	buffer[len] = 0;
	fclose(f);

	lisp_parameters = hash_new("lisp parameters");

	char	*p = buffer;
	lisp_fname = path;
	lisp_lnum = 1;
	while(p < buffer+len)
	{
		struct s_exp	*s = parse_lisp(&p, 0);
		if(!s)break;
		//lisp_print_s_exp(s);
		//printf("\n");
	}
}

char	*get_lisp_parameter(char	*name)
{
	struct field	*f = lisp_get_field(name);
	if(!f->value)return NULL;
	if(f->value->type != s_exp_str)
	{
		fprintf(stderr, "warning: ignoring value of %s, since it is not a string\n", name);
		return NULL;
	}
	return f->value->value;
}
