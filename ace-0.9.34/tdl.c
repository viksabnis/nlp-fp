#define		_GNU_SOURCE
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>
#include	<wctype.h>

#include	"tdl.h"
#include	"preprocessor.h"
#include	"morpho.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"dag.h"
#include	"transfer.h"
#include	"hash.h"
#include	"conf.h"
#include	"unicode.h"
#ifdef POST
#include	"post.h"
#endif
#include	"version.h"
#include	"ubertag.h"

int	dagify_tdl_line(struct tdl_line	*line, void	*ref);
int	typify_tdl_line(struct tdl_line	*line, void	*ref);
int	load_tdl(char	*path);

char	*grammar_version = 0;

void show_task_name(char *task)
{
	printf("\033[0;1m%-28s\033[0m", task);
	fflush(stdout);
}

char	*trim_string(char	*str)
{
	int	len;

	while(*str==' ' || *str=='\t' || *str=='\n' || *str=='\r')str++;
	len = strlen(str);
	if(len==0)return str;
	while(len>0 && (str[len-1]==' ' || str[len-1]=='\t' || str[len-1]=='\n' || str[len-1]=='\r'))len--;
	str[len] = 0;
	return str;
}

long			ntdllines;
struct tdl_line		**tdllines;
char			*tdlstatus = "grammar";

struct hash	*tdl_hash;

int	loud_noises = 0;

struct type	*_current_building_type = NULL;

int	enable_out_of_order = 0;

struct tdl_line	*get_conf_line(char	*lhs)
{
	char	key[256];
	sprintf(key, "%s %s", "config", lhs);
	return hash_find(tdl_hash, key);
}

char	*get_conf(char	*lhs)
{
	struct tdl_line	*tdl = get_conf_line(lhs);
	return tdl?tdl->rhs:NULL;
}

char	*get_conf_unq(char	*lhs)
{
	char	*q = get_conf(lhs);
	if(q && *q=='"')
	{
		char	*p = strdup(q);
		p++;
		if(strrchr(p, '"'))
			*strrchr(p, '"') = 0;
		return p;
	}
	else return q;
}

char	*get_conf_parent_dir(char	*lhs)
{
	struct tdl_line	*tdl = get_conf_line(lhs);
	assert(tdl);

	char	*dir = strdup(tdl->filename);
	if(strrchr(dir, '/') > dir)
		*strrchr(dir, '/') = 0;
	else
	{
		free(dir);
		dir = strdup(".");
	}
	return dir;
}

char	*get_conf_file_path(char	*lhs)
{
	char	*u = get_conf_unq(lhs), *p = 0;
	if(!u)return NULL;

	char	*dir = get_conf_parent_dir(lhs);
	//printf("should get path for %s; might be relative to %s\n", u, dir);

	assert(-1 != asprintf(&p, "%s/%s", dir, u));
	free(dir);
	return p;
}

void	augment_definition(struct tdl_line	*tdl, char	*rhs, int	lnum, char	*path)
{
	char	*old = tdl->rhs;
	char	*new = malloc(strlen(old) + strlen(rhs) + 32);
	sprintf(new, "%s & __ace__unique_corefs & %s", old, rhs);
	free(tdl->rhs);
	tdl->rhs = new;
	//fprintf(stderr, "%s:%d augments type `%s' from %s:%d\n", path, lnum, tdl->lhs, tdl->filename, tdl->lnum);
	//fprintf(stderr, "  new definition: %s\n", new);
}

char	*key_for_status_and_lhs(char	*status, char	*lhs)
{
	char	key[512];
	sprintf(key, "%s %s", status, lhs);
	wchar_t	*widekey = towide(key);
	wchar_t	*wkp = widekey;
	while(*wkp) { *wkp = towlower(*wkp); wkp++; }
	return tombs(widekey);
}

void	add_tdlline(char	*lhs, char	operation, char	*rhs, char	*odef, int	lnum, char	*path)
{
	char	*mbskey = key_for_status_and_lhs(tdlstatus?:"instance", lhs);
	struct tdl_line	*tdl = hash_find(tdl_hash, mbskey);;

	if(tdl)
	{
		if(operation == '+')
		{
			augment_definition(tdl, rhs, lnum, path);
			return;
		}
		else
		{
			fprintf(stderr, "warning: %s:%d redefines type `%s' from %s:%d\n", path, lnum, lhs, tdl->filename, tdl->lnum);
		}
	}
	else
	{
		if(operation == '+')
		{
			fprintf(stderr, "error: %s:%d augments nonexistant type `%s'\n", path, lnum, lhs);
			exit(-1);
		}
		ntdllines++;
		tdllines = realloc(tdllines, sizeof(struct tdl_line*)*ntdllines);
		tdl = tdllines[ntdllines-1] = malloc(sizeof(struct tdl_line));
		tdl->lhs = strdup(lhs);
		hash_add(tdl_hash, mbskey, tdl);
	}
	tdl->processed = 0;
	tdl->rhs = strdup(rhs);
	tdl->filename = path;
	tdl->status = tdlstatus?:"instance";
	tdl->odef = (odef && *odef)?strdup(odef):NULL;
	tdl->lnum = lnum;
	tdl->operation = operation;
}

int	process_comments(char	*line, int	in_comment)
{
	char	*ptr, *oline;
	int	inquote = 0, in_regex = 0;

	// handle block-comments first
	for(oline=ptr=line;*ptr;ptr++)
	{
		if(!inquote && !in_regex && ptr[0]=='#' && ptr[1]=='|')in_comment++, ptr++;
		else if(!inquote && !in_regex && ptr[0]=='|' && ptr[1]=='#')in_comment--, ptr++;
		else if(!in_comment)
		{
			if(*ptr=='\\' && (inquote || in_regex) && ptr[1])
				{*oline++ = *ptr++;*oline++ = *ptr;continue;}
			if(*ptr=='^' && !inquote)in_regex = 1;
			if(*ptr=='$' && !inquote)in_regex = 0;
			if(*ptr=='"' && !in_regex)inquote=!inquote;

			if(*ptr==';' && !in_regex && !inquote)*oline++ = 0;
			else *oline++ = *ptr;
		}
	}
	*oline = 0;
	return in_comment;
}

int	unbalanced(char	*line)
{
	int	in3quote = 0;
	int	inquote = 0, bal = 0, regex = 0;
	int	escape = 0;

	while(*line)
	{
		if(escape) { line++; escape = 0; }
		else if(*line == '\\') { line++; escape = 1; }
		else if(in3quote)
		{
			if(!strncmp(line,"\"\"\"",3)) { line += 3; in3quote = 0; }
			else line += 1;
		}
		else if(!strncmp(line,"\"\"\"",3)) { line += 3; in3quote = 1; }
		else if(!inquote && !regex && *line==':' && line[1]=='<')line+=2;
		else switch(*line++)
		{
			case	'^':	if(!inquote)regex = 1;	break;
			case	'$':	if(!inquote)regex = 0;	break;
			case	'<':	if(!regex && !inquote)bal++;	break;
			case	'>':	if(!regex && !inquote)bal--;	break;
			case	'"':	if(!regex)inquote = !inquote;	break;
			case	'\\':	escape = 1;		break;
		}
	}
	return (bal != 0 || regex != 0 || inquote || in3quote);
}

char	*tdlstatus_stack[16] = {"grammar"};
int		tdlstatus_stack_pointer = 0;

void	tdl_push_status(char	*mystatus)
{
	if(tdlstatus_stack_pointer>10)
	{
		fprintf(stderr, "TDL status stack overflow\n");
		return;
	}
	tdlstatus = tdlstatus_stack[++tdlstatus_stack_pointer] = mystatus;
}

void	tdl_pop_status()
{
	if(tdlstatus_stack_pointer <= 0)
	{
		fprintf(stderr, "TDL status stack underflow\n");
		return;
	}
	tdlstatus = tdlstatus_stack[--tdlstatus_stack_pointer];
}

char	*path_for_include(char	*parent, char	*what, char	*suffix)
{
	char	dirpath[10240];
	strcpy(dirpath, parent);
	char	*p = dirpath + strlen(dirpath) - 1;
	while(p>dirpath && *p!='/')p--;
	*p = 0;
	char	iname[10240];
	sprintf(iname, "%s%s%s", dirpath, dirpath[0]?"/":"", what);
	if(suffix)
		if(!strstr(what, suffix))
			strcat(iname, suffix);
	return strdup(iname);
}

int	process_colon_command(char	*parent, char	*cmd)
{
	char	*word, *what, *status, *whatstatus, *p;

	cmd = trim_string(cmd);
	word = strtok(cmd, " 	\n");

	if(word && !strcmp(word, ":begin"))
	{
		what = strtok(0, " 	\n");
		if(what && !strcmp(what, ":type"))tdl_push_status("type");
		else if(what && !strcmp(what, ":instance"))
		{
			status = strtok(0, " 	\n");
			if(status && !strcmp(status, ":status"))
			{
				whatstatus = strtok(0, " 	\n");
				if(whatstatus)tdl_push_status(strdup(whatstatus));
			}
			else
			{
				tdl_push_status("instance");
			}
		}
		//printf("status now `%s'\n", tdlstatus);
	}
	else if(word && !strcmp(word, ":end"))
		tdl_pop_status();
	else if(word && !strcmp(word, ":include"))
	{
		extern int g_transfer;
		char	*suffix = g_transfer?NULL:".tdl";
		what = trim_string(cmd + 9);
		if(what[0]=='"' && what[strlen(what)-1]=='"' && strlen(what) > 2)
		{
			what++;
			what[strlen(what)-1] = 0;
			if(strstr(what, ".mtr"))suffix=NULL;
			load_tdl(path_for_include(parent, what, suffix));
		}
		else
		{
			fprintf(stderr, "malformed TDL syntax: `:include %s'\n", what);
			return -1;
		}
	}
	else printf("colon command: `%s'\n", cmd);
	return 0;
}

char	*strip_docstring_v1(char	*rhs, int	lnum, char	*path)
{
	// docstring can appear immediately before the first opening '[', or not at all.
	char	*q = strchr(rhs, '"');
	if(!q)return NULL;
	// we're only interested if there's a & before the ".
	char	*m = q-1;
	while(m>rhs && *m!='&' && (*m==' ' || *m=='\t' || *m=='\n' || *m=='\r'))m--;
	if(m<=rhs || *m!='&')return NULL;	// preceded by something other than '&'
	while(m>=rhs && *m!='[')m--;
	if(m>=rhs)return NULL;	// found a '[' before the '"'; it's not a docstring
	char	*p = q+1;
	while(*p && *p!='"')
	{
		if(*p=='\\' && p[1])p++;
		p++;
	}
	if(!*p)
	{
		fprintf(stderr, "ERROR: quoted docstring not terminated at %s:%d\n", path, lnum);
		exit(-1);
	}
	assert(*p=='"');
	char	*s = p+1;
	while(*s && (*s==' ' || *s=='\t' || *s=='\n' || *s=='\r') )s++;
	if(*s != '[' && *s != '.')
	{
		fprintf(stderr, "ERROR: quoted docstring does not precede open '[' or '.' at %s:%d.\n", path, lnum);
		exit(-1);
	}
	*p = 0;
	// it's a docstring.
	char	*docstring = strdup(q+1);
	memmove(q, p+1, strlen(p+1)+1);
	return docstring;
}

char	*strip_docstring_v2(char	*rhs, int	lnum, char	*path)
{
	// docstring can appear pretty much anywhere
	char	*q = strstr(rhs, "\"\"\"");
	if(!q)return NULL;
	// the """ pattern cannot legally occur outside a docstring, since it would necessarily be two adjacent strings, which is not valid TDL.
	// find the end of the docstring.
	char	*p = q+3;
	while(*p && strncmp(p,"\"\"\"",3))
	{
		if(*p=='\\' && p[1])p++;
		p++;
	}
	if(!*p)
	{
		fprintf(stderr, "ERROR: triple-quoted docstring not terminated at %s:%d\n", path, lnum);
		exit(-1);
	}
	assert(!strncmp(p,"\"\"\"",3));
	*p = 0;
	char	*docstring = strdup(q+3);
	memmove(q, p+3, strlen(p+3)+1);
	return docstring;
}

int	load_tdl(char	*path)
{
	if(!path)
		return -1;
	FILE	*f = fopen(path, "r");
	char	buffer[102400], *lhs, *rhs, *end;
	char	line[102400], *lp;
	char	odef[102400], doing[256];
	int	in_comment = 0;
	int	lnum = 0;
	char	*tdlstatuses = 0;

	if(!f)
	{
		perror(path);
		return -1;
	}
	buffer[0] = 0;

	if(tdlstatus && !strcmp(tdlstatus, "type"))tdlstatuses = "types";
	if(tdlstatus && !strcmp(tdlstatus, "rule"))tdlstatuses = "rules";
	if(tdlstatus && !strcmp(tdlstatus, "lex-rule"))tdlstatuses = "lexical rules";
	if(tdlstatus && !strcmp(tdlstatus, "lex-entry"))tdlstatuses = "lexical entries";
	if(tdlstatus && !strcmp(tdlstatus, "tree-node-label"))tdlstatuses = "tree labels";
	if(tdlstatus && !strcmp(tdlstatus, "config"))tdlstatuses = "configuration";
	if(tdlstatus && !strcmp(tdlstatus, "grammar"))tdlstatuses = "grammar";
	if(!tdlstatuses)
	{
		if(tdlstatus)tdlstatuses = tdlstatus;
		else tdlstatuses = "instances";
	}

	sprintf(doing, "reading %s", tdlstatuses); show_task_name(doing);
	printf("from `%s'\n", path);

	path = strdup(path);	// make our own copy so we can put it in tdlline records without duplicating further
	*odef = 0;
	while(fgets(line, 102399, f))
	{
		if(line[0]==0)break;
		lnum++;
//		if(line[0]=='\n')continue;
//		if(line[strlen(line)-1]=='\n')	// make sure we don't kill noeol files' last char
//			line[strlen(line)-1] = 0;
		if(in_comment || line[0]!='%')in_comment = process_comments(line, in_comment);

		lp = trim_string(line);

		if(*lp == 0)continue;

		/*if(loading_semi)
		{
			if(strchr(lp, ':') && (!strchr(lp, ' ') || strchr(lp, ':')<strchr(lp, ' ')))
			{
				if(process_semi_command(path, lnum, lp))return -1;
				continue;
			}
			else
			{
				if(process_semi_line(path, lnum, lp))return -1;
				continue;
			}
		}*/

		if(lp[0] == '%')
		{
			if(lp[1]=='(')setup_morpho(lp+1);
			else strcpy(odef, lp+1);
			continue;
		}

		if(buffer[0])strcat(buffer, " ");
		strcat(buffer, lp);
		if(!buffer[0])continue;
		//printf("... accum tdl '%s'\n", buffer);
		if(strlen(buffer) > 100000)
		{
			fprintf(stderr, "tdl statement too long: `%s'\n", buffer);
			return -1;
		}
		end = buffer + strlen(buffer)-1;
		if(*end != '.')
		{
			//fprintf(stderr, "tdl: `%s' malformed input string, does not end '.'\n", buffer);
			continue;
		}
		if(unbalanced(buffer))continue;	// '.' can validly occur inside a list without ending the tdl statement.
		*end = 0;
		lhs = trim_string(buffer);
		if(lhs[0]==':')
		{
			if(process_colon_command(path, lhs))return -1;
			*buffer = *odef = 0;
			continue;
		}
		end = strstr(lhs, ":=");
		if(!end)end = strstr(lhs, ":<");
		if(!end)end = strstr(lhs, ":+");
		if(!end)
		{
			fprintf(stderr, "tdl: `%s' malformed input string, does not contain ':=' or ':<' or ':+'.\n", buffer);
			*buffer = *odef = 0;
			continue;
		}
		*end = 0;
		char operation = end[1];
		// for our purposes, there doesn't seem to be any distinction between := and :< ...
		rhs = end+2;
		lhs = trim_string(lhs);
		rhs = trim_string(rhs);
		if(*lhs==0)// || *rhs==0)
		{
			fprintf(stderr, "tdl: `%s :%c %s' malformed input string, degenerate statement\n", lhs, operation, rhs);
			*buffer = *odef = 0;
			continue;
		}

		//printf("tdl input: `%s'  -->  `%s'\n", lhs, rhs);
		char	*next_ds;
		do
		{
			next_ds = strip_docstring_v2(rhs, lnum, path);
			//if(next_ds)printf("HEY! I found and stripped a triple-quoted docstring: |%s|\n", next_ds);
		} while(next_ds);
		char	*docstring = strip_docstring_v1(rhs, lnum, path);
		//if(docstring)printf("HEY! I found and stripped a docstring: |%s|\n", docstring);
		add_tdlline(lhs, operation, rhs, odef, lnum, path);
		*buffer = 0;
		*odef = 0;
	}
	fclose(f);
	return 0;
}

void	free_tdl()
{
	int	i;

	for(i=0;i<ntdllines;i++)
	{
		free(tdllines[i]->lhs);
		free(tdllines[i]->rhs);
		if(tdllines[i]->odef)
			free(tdllines[i]->odef);
		free(tdllines[i]);
	}
	ntdllines = 0;
	if(tdllines)free(tdllines);
	tdllines = NULL;
}

int	process_tdl_status(char	*status, int	(*callback)(struct tdl_line	*line, void	*ref), void	*ref)
{
	int	i;

	for(i=0;i<ntdllines;i++)
		tdllines[i]->processed = 0;
	for(i=0;i<ntdllines;i++)
	{
		if(strcmp(status, tdllines[i]->status))continue;
		if(tdllines[i]->processed)continue;
		tdllines[i]->processed = 1;
		if(callback(tdllines[i], ref))
		{
			fprintf(stderr, "tdl: top-level error occured near %s:%d\n", tdllines[i]->filename, tdllines[i]->lnum);
			exit(-1);
			return -1;
		}
	}
	return 0;
}

int	process_tdl_dgs_status(char	*status, int	(*callback)(char	*lhs, struct dg	*dg, struct tdl_line	*line))
{
	return process_tdl_status(status, dagify_tdl_line, callback);
}

struct type	*find_type(char	*name, int	constrain)
{
	struct type	*type = lookup_type(name);
	int		i;
	int	is_atomic = (name[0]=='"' || name[0]=='\'' || name[0]=='^');

	if(!type || (!is_atomic && constrain && !type->dg))
	{
		// try to find constraint for this type before returning it
		if(type && name[0]=='g' && name[1]=='(')
		{
			// glb types may not be referenced explicitly
			type = 0;
			goto notype;
		}
		char	*key = key_for_status_and_lhs("type", name);
		struct tdl_line	*tdl = hash_find(tdl_hash, key);
		
		if(tdl)
		{
			if(tdl->processed)
			{
				fprintf(stderr, "tdl: cycle detected! type `%s' needed before completely defined.\n", name);
				return 0;
			}
			else
			{
				if(enable_out_of_order)
				{
					//printf(" -- found `%s' later in .tdl file\n", name);
					tdl->processed = 1;
					if(constrain)
					{
						struct type	*tmp = _current_building_type;
						if(dagify_tdl_line(tdl, constrain_type))
						{
							fprintf(stderr, "tdl: error constraining occured near line %d\n", tdl->lnum);
							return 0;
						}
						_current_building_type = tmp;
					}
					else if(typify_tdl_line(tdl, 0))
					{
						fprintf(stderr, "tdl: error typing occured near line %d\n", tdl->lnum);
						return 0;
					}
					type = lookup_type(name);
					//printf(" -- finished sneaking `%s' in\n", name);
				}
			}
		}
	}

	if(!type)
	{
		notype:
		fprintf(stderr, "tdl: no such type as `%s'\n", name);
	}
	return type;
}

struct dg	*type_dg(char		*name)
{
	struct type	*type = find_type(name, 1);
	struct dg	*ret;

	if(!type)return NULL;//exit(-1);
	if(!type->dg)return atomic_dg(name);
	ret = copy_dg(type->dg);
	if(!ret) { fprintf(stderr, "type_dg(%s) couldn't copy %p\n", name, type->dg); exit(-1); }
	return ret;
}

struct dagify_record
{
	int	current_path[1024];
	int	current_pathlen;

	struct	coref
	{
		int	*path;
		int	pathlen;
		char	*name;
	}	*corefs;
	int	ncorefs;
	int	unique_addendum;
/*
	struct tcopy	*tcopies;
	int	ntcopies;*/
};

/* a note about coreferencing and +copy+ in transfer rules...
 * constraints appearing on the OUTPUT portion of a transfer rule are never applied to the other parts,
 * even when they are coreferenced.  instead, type constraints on the OUTPUT portion are stored under a separate dg (tr->output_override),
 * and the portion from the input (tr->dg / OUTPUT) is default-unified into it.
 * we can then treat +copy+ as if it were a written coreference between the corresponding INPUT and OUTPUT EP.
 */

static void coreference(struct dagify_record	*R, char	*name)
{
	R->ncorefs++;
	R->corefs = realloc(R->corefs, sizeof(struct coref)*R->ncorefs);
	R->corefs[R->ncorefs-1].path = malloc(sizeof(int) * R->current_pathlen);
	R->corefs[R->ncorefs-1].pathlen = R->current_pathlen;
	memcpy(R->corefs[R->ncorefs-1].path, R->current_path, sizeof(int) * R->current_pathlen);
	char	*uniqname;
	uniqname = malloc(strlen(name) + 20);
	//int	in_output = (g_transfer!=0 && R->current_pathlen!=0 && R->current_path[0]==lookup_fname("OUTPUT"));
	//sprintf(uniqname, "%s %s %d", in_output?"_o_":"_i_", name, R->unique_addendum);
	sprintf(uniqname, "%s %d", name, R->unique_addendum);
	R->corefs[R->ncorefs-1].name = uniqname;
}

/*static void record_tcopy(struct dagify_record	*R, int	*from, int	flen, int	*to, int	tlen)
{
	R->ntcopies++;
	R->tcopies = realloc(R->tcopies, sizeof(struct tcopy)*R->ntcopies);
	R->tcopies[R->ntcopies-1].frompath = malloc(sizeof(int) * flen);
	R->tcopies[R->ntcopies-1].frompathlen = flen;
	memcpy(R->tcopies[R->ntcopies-1].frompath, from, sizeof(int)*flen);
	R->tcopies[R->ntcopies-1].topath = malloc(sizeof(int) * tlen);
	R->tcopies[R->ntcopies-1].topathlen = tlen;
	memcpy(R->tcopies[R->ntcopies-1].topath, to, sizeof(int)*tlen);
}*/

static void transfer_ep_copy(struct dagify_record	*R)
{
	// as near as I can tell, +copy+ means the (say, I'th) output should be
	// identical to the I'th input, with some additional constraints thrown in.
	// the additional output specifications are meant to override features of the input when copied.
	// we treat this just like a coreference (but note that type constraints inside transfer rule
	// OUTPUT sections have special treatment)
	assert(R->current_pathlen && lookup_fname("OUTPUT") == R->current_path[0]);
	//int	pathcopy[R->current_pathlen];
	//memcpy(pathcopy, R->current_path, sizeof(int)*R->current_pathlen);
	//pathcopy[0] = lookup_fname("INPUT");
	//record_tcopy(R, pathcopy, R->current_pathlen, R->current_path, R->current_pathlen);
	static int tcopy_id = 0;
	char	name[128];
	sprintf(name, "tcopy-%d", tcopy_id++);
	R->current_path[0] = lookup_fname("INPUT");
	coreference(R, name);
	R->current_path[0] = lookup_fname("OUTPUT");
	coreference(R, name);
}

struct dg *add_dg_path(struct dg	*d, int	*path, int	len, struct dg	*target)
{
	int	i;
	struct dg *step, *ret = d;

	for(i=0;i<len-1;i++)
	{
		step = dg_hop(d, path[i]);
		if(!step)
		{
			step = atomic_dg(top_type);
			d = add_dg_hop(d, path[i], step);
			if(i==0)ret = d;
		}
		d = step;
	}
	d = add_dg_hop(d, path[len-1], target);
	if(i==0)ret = d;
	return ret;
}

static int patch_coreferences(struct dagify_record	*R, struct dg	*target)
{
	int		i, j;
	struct dg	*coref_template;
	struct dg	*reentrancies[256];
	char		*rnames[256];
	int		nr = 0;

	if(!R->ncorefs)return 0;
	for(i=0;i<256;i++)
	{
		reentrancies[i] = 0;
		rnames[i] = 0;
	}
	for(i=0;i<R->ncorefs;i++)
	{
		for(j=0;j<nr;j++)
			if(!strcmp(rnames[j], R->corefs[i].name))break;
		if(j==nr)
		{
			assert(nr < 256);
			reentrancies[j] = atomic_dg(top_type);
			rnames[j] = R->corefs[i].name;
			nr++;
		}
		extern char **fnames;
		//printf("coref %d: %s = ", i, R->corefs[i].name);
		//for(j=0;j<R->corefs[i].pathlen;j++)printf("%s ", fnames[R->corefs[i].path[j]]);
		//printf("\n");
	}
	for(j=0;j<nr;j++)
	{
		coref_template = atomic_dg(top_type);
		for(i=0;i<R->ncorefs;i++) if(!strcmp(rnames[j], R->corefs[i].name))
			coref_template = add_dg_path(coref_template, R->corefs[i].path, R->corefs[i].pathlen, reentrancies[j]);
		//printf("coref template:\n"); print_dg(coref_template); printf("\n");
		//printf("target:\n");print_dg(target);printf("\n");
		if(unify_dg_infrom(target, coref_template))
		{
			//printf("patch failed\n");
			return -1;
		}
	}
	/*if(g_transfer!=0)
	{
		for(j=0;j<nr;j++)
		{
			if(strncmp(rnames[j], "_o_ ", 4))continue;
			// [j] is an OUTPUT tag; see if we can find a matching INPUT tag
			for(i=0;i<nr;i++)
			{
				if(strncmp(rnames[i], "_i_ ", 4))continue;
				if(strcmp(rnames[i]+4, rnames[j]+4))continue;
				// [i] is the corresponding INPUT tag.
				// need to generate a tcopy record.
				// first, find representative paths for the INPUT and OUTPUT equivalence classes.
				int k, l;
				for(k=0;k<R->ncorefs;k++)
					if(!strcmp(rnames[j], R->corefs[k].name))break;
				assert(k<R->ncorefs);
				for(l=0;l<R->ncorefs;l++)
					if(!strcmp(rnames[i], R->corefs[l].name))break;
				assert(l<R->ncorefs);
				// [l] is the INPUT path, which needs to be default unified to the OUTPUT path, [k], after transfer rule processing
				record_tcopy(R, R->corefs[l].path, R->corefs[l].pathlen, R->corefs[k].path, R->corefs[k].pathlen);
			}
		}
	}*/
	//printf("patch succeeded\n");
	return 0;
}

static struct dg	*rdagify(struct dagify_record	*R, char	*str);
static struct dg	*dlistify(struct dagify_record	*R, char	*str);

static struct dg	*listify(struct dagify_record	*R, char	*str, struct dg	**last)
{
	int	len = strlen(str), bracket, iplen = R->current_pathlen;
	char		ch, *item, *comma;
	struct dg	*dg, *lp, *nlp, *idg;
	int		inquote = 0;

	if(str[1]=='!' && !last)return dlistify(R, str);

	if(str[len-1] != '>')
	{
		fprintf(stderr, "tdl: lists syntax is < ... >, not `%s'\n", str);
		return 0;
	}
	str[len-1] = 0;
	str = trim_string(str+1);

	if(*str=='!')
	{
		len = strlen(str);
		if(!last || str[len-1]!='!')
		{
			fprintf(stderr, "tdl: diff-list syntax is <! ... !>\n");
			return 0;
		}
		// chop '!'s out, we already know it's a difflist.
		str[len-1] = 0;
		str = trim_string(str+1);
	}
	//printf("listify (%p) `%s'\n", last, str);

	if(*str==0)
	{
		lp = type_dg(last?g_list_type:g_null_type);
		if(last)*last = lp;
		return lp;
	}
	if(!strcmp(str, "..."))
	{
		lp = type_dg(g_list_type);
		if(last)*last = lp;
		return lp;
	}

	lp = dg = type_dg(g_cons_type);
	if(!dg)return 0;

	while(*str)
	{
		comma = str;
		bracket=0;
		int	regex = 0;
		while(*comma && (bracket || regex || inquote || (*comma!=',' && *comma!='.')))switch(*comma++)
		{
			case	'^':	if(!inquote)regex = 1;	break;
			case	'$':	if(!inquote)regex = 0;	break;
			case	'<':	case	'[':	if(!regex && !inquote)bracket++;	break;
			case	'>':	case	']':	if(!regex && !inquote)bracket--;	break;
			case	'\\':	if((regex || inquote) && *comma)comma++;	break;	// skip a char
			case	'"':	if(!regex)inquote = !inquote;		break;
		}
		if(bracket)
		{
			fprintf(stderr, "tdl: unmatched bracket in list near `%s'\n", str);
			R->current_pathlen = iplen;
			return 0;
		}
		if(inquote)
		{
			fprintf(stderr, "tdl: unmatched quote in list near '%s'\n", str);
			R->current_pathlen = iplen;
			return 0;
		}
		if(regex)
		{
			fprintf(stderr, "tdl: regex not in matched ^...$ near '%s'\n", str);
			R->current_pathlen = iplen;
			return 0;
		}

		if(*comma)
		{
			ch = *comma;
			*comma = 0;
			item = trim_string(str);
			str = trim_string(comma+1);
			if(ch == '.')
			{
				if(last) fprintf(stderr, "tdl: WARNING -- '.' list cons notation used in a diff-list!\n");
				R->current_path[R->current_pathlen++] = 2;	// REST
				nlp = rdagify(R, str);
				R->current_pathlen--;
				if(!nlp)return 0;
				*str = 0;	// make sure we break
			}
			else if(!strcmp(str, "..."))
			{
				*str = 0;
				nlp = type_dg(g_list_type);
			}
			else nlp = type_dg(g_cons_type);
		}
		else
		{
			item = str;
			str = item+strlen(item);
			if(last)nlp = type_dg(g_list_type);	// dlists need to be open-ended
			else nlp = type_dg(g_null_type);
		}

		//printf("list item `%s'\n", item);
		R->current_path[R->current_pathlen++] = 1;	// FIRST
		idg = rdagify(R, item);
		R->current_pathlen--;
		if(!idg)
		{
			R->current_pathlen = iplen;
			return 0;
		}
		lp = add_dg_feature(lp, "FIRST", idg);
		lp = add_dg_feature(lp, "REST", nlp);
		lp = nlp;
		R->current_path[R->current_pathlen++] = 2;	// REST
	}
	R->current_pathlen = iplen;
	if(last)*last = lp;

	return p_dereference_dg(dg);
}

static struct dg	*dlistify(struct dagify_record	*R, char	*str)
{
	struct dg	*list, *last, *dg;

	R->current_path[R->current_pathlen++] = lookup_fname("LIST");
	list = listify(R, str, &last);
	R->current_pathlen--;
	if(!list)return 0;

	dg = type_dg(g_diff_list_type);
	dg = add_dg_feature(dg, "LIST", list);
	dg = add_dg_feature(dg, "LAST", last);
	return dg;
}

static struct dg	*structify(struct dagify_record	*R, char	*str)
{
	char	*ptr, *dot;
	char	*label, *vptr;
	struct dg	*dg, *value;
	int	bracket, len, depth;

	str = trim_string(str);

	if(!strcmp(str, "__ace__unique_corefs"))
	{
		R->unique_addendum++;
		return atomic_dg(top_type);
	}

	if(*str == '#')
	{
		if(strchr(str, ' ') || strchr(str, '\t'))
		{
			fprintf(stderr, "tdl: tag `%s' may not have whitespace in it!\n", str);
			return 0;
		}
		coreference(R, str+1);
		return atomic_dg(top_type);
	}

	if(*str == '<')
	{
		dg = listify(R, str, 0);
		if(!dg)fprintf(stderr, "hint: listify failed\n");
		return dg;
	}
	if(*str != '[')
	{
		if(*str == '"' && R->current_pathlen == 0)
		{
			// this was a type comment.  terrible syntax.
			return atomic_dg(top_type);
			//printf("calling type_dg(%s)\n", str);
		}
		if(g_transfer!=0 && !strcmp(str, "+copy+"))
		{
			transfer_ep_copy(R);
			dg = type_dg(top_type);
		}
		else dg = type_dg(str);
		if(!dg)fprintf(stderr, "hint: type_dg(%s) failed\n", str);
		return dg;
	}

	dg = atomic_dg(top_type);

	ptr = trim_string(str+1);
	len = strlen(ptr);
	if(ptr[len-1] != ']')
	{
		fprintf(stderr, "tdl: unbalanced '[' in dag string `%s'\n", str);
		return 0;
	}
	ptr[--len] = 0;
	trim_string(ptr);

	while(*ptr)
	{
		// if we are looking at a comma, skip over it (they can appear detached sometimes...)
		if(*ptr == ',')ptr = trim_string(ptr+1);
		if(!*ptr)break;
		// handle one feature
		label = ptr;
		morelabel:
		while(*ptr && (*ptr!=' ' && *ptr!='\t' && *ptr!='[' && *ptr!='<'))ptr++;
		if(*ptr==' ' && (ptr[1] == '.' || (ptr[1] && ptr>label && ptr[-1]=='.')))
		{
			// someone put a space in a path, like:
			// LOCAL .CAT.VAL.COMPS < blah >, or
			// LOCAL.CAT. VAL.COMPS < blah >
			// be nice to them.
			ptr++;
			goto morelabel;
		}
		if(!*ptr)
		{
			novalue:
			fprintf(stderr, "tdl: label `%s' had no value\n", label);
			return 0;
		}

		// make a null-terminated copy of the label
		label = memcpy(calloc(ptr-label+1,1), label, ptr-label);
		//printf("label `%s'\n", label);
		// *ptr = 0;
		//ptr = trim_string(ptr+1);

		ptr = trim_string(ptr);
		if(!*ptr)goto novalue;
		// find the length of its value
		vptr = ptr;
		if(*ptr!='^')
		{
			bracket = 0;
			int	quote = 0, regex = 0;
			while(*ptr && (bracket || quote || regex || *ptr!=','))switch(*ptr++)
			{
				case	'^':	if(!quote)regex = 1;	break;
				case	'$':	if(!quote)regex = 0;	break;
				case	'"':	if(!regex)quote = ~quote;	break;
				case	'\\':	if((regex || quote) && *ptr)ptr++;	break;	// skip a char on escape
				case	'<':	case	'[':	if(!regex && !quote)bracket++;	break;
				case	'>':	case	']':	if(!regex && !quote)bracket--;	break;
			}
			if(bracket)
			{
				fprintf(stderr, "tdl: unbalanced '[' in dag value `%s'\n", vptr);
				return 0;
			}
			if(quote)
			{
				fprintf(stderr, "tdl: unbalanced '\"' in dag value `%s'\n", vptr);
				return 0;
			}
			if(regex)
			{
				fprintf(stderr, "tdl: regex not balanced in ^...$ in dag value '%s'\n", vptr);
				return 0;
			}
		}
		else
		{
			while(*ptr && *ptr!='$')switch(*ptr++)
			{
				case	'\\':	if(*ptr)ptr++;	break;	//skip a char on escape
			}
			if(*ptr != '$')
			{
				fprintf(stderr, "tdl: regex not balanced in ^...$ in dag value '%s'\n", vptr);
				return 0;
			}
			ptr++;
		}
		*ptr = 0;
		ptr = trim_string(ptr+1);

		//printf("label %s, value %s\n", label, vptr);
		depth = 0;
		do
		{
			dot = strchr(label, '.');
			if(dot)*dot = 0;
			R->current_path[R->current_pathlen++] = lookup_fname(trim_string(label));
			depth++;
			label = dot+1;
		} while(dot);
		value = rdagify(R, vptr);
		R->current_pathlen-=depth;
		if(!value)
		{
			fprintf(stderr, "hint: structify -> rdagify failed\n");
			return 0;
		}
		// something might already be at this path, in which case we are supposed to unify this with that
		struct dg	*previous = dg;
		int j;
		for(j=0;previous && j<depth;j++)
			previous = dg_hop(previous, R->current_path[R->current_pathlen + j]);
		if(previous) unify_dg_infrom(previous, value);
		else dg = add_dg_path(dg, R->current_path+R->current_pathlen, depth, value);
	}

	return dg;
}

static struct dg	*rdagify(struct dagify_record	*R, char	*str)
{
	int	bracket = 0, inquote = 0;
	char	*ptr;
	struct dg	*lhs, *rhs, *res;

	str = trim_string(str);
	if(!*str)
	{
		fprintf(stderr, "tdl: expected a dag definition\n");
		return 0;
	}
	ptr = str;
	while(*ptr && (bracket>0 || inquote || *ptr!='&'))switch(*ptr++)
	{
		case	'<': case	'[':	bracket++;	break;
		case	'>': case	']':	bracket--;	break;
		case	'\\': if(*ptr)ptr++;	break;	// skip a char
		case	'"': inquote = !inquote;		break;
	}
	if(*ptr=='&')
	{
		// ptr = first '&' in the dag
		*ptr = 0;
		lhs = structify(R, str);
		if(!lhs)return 0;
		rhs = rdagify(R, ptr+1);
		if(!rhs)return 0;
		lhs = dereference_dg(lhs);
		rhs = dereference_dg(rhs);
		/*if(building_type)
		{
			lhs->type = rhs->type = building_type;
			lhs->xtype = rhs->xtype = building_type;
		}*/
		if(loud_noises)
		{
			//if(building_type)printf("building %s!\n", building_type->name);
			printf("lhs: "); print_dg(lhs); printf("\n");
			printf("rhs: "); print_dg(rhs); printf("\n");
		}
		// up to 0.9.21 this was copy_dg(lhs) and copy_dg(rhs); why? will I regret skipping that?
		// answer: copying aggressively was reducing the need for p_dereference_dg() calls other places.
		// also, there's a mysterious crash in lexical lookup on OSX (but not linux) without it
		if(0 != unify_dg_infrom(res = copy_dg(lhs), copy_dg(rhs)))
		//if(0 != unify_dg_infrom(res = lhs, rhs))
		{
			fprintf(stderr, "tdl: requested unification failed\n");
#ifdef	UNIFY_PATHS
			unify_backtrace();
#endif
			printf("lhs: "); print_dg(lhs); printf("\n");
			printf("rhs: "); print_dg(rhs); printf("\n");
			return 0;
		}
		res = p_dereference_dg(res);
		if(loud_noises)
		{
			printf("res: "); print_dg(res); printf("\n");
		}
		return res;
	}
	else return structify(R, str);
}

struct dg	*dagify(char	*str, struct type	*building_type)
{
	struct dg	*dg;
	int	i;
	struct dagify_record	R;

	bzero(&R, sizeof(R));

	_current_building_type = building_type;
	dg = rdagify(&R, str);
	if(!dg)
	{
		_current_building_type = NULL;
		return 0;
	}
	if(building_type)
	{
		dg->type = dg->xtype = building_type;
	}
	//printf(" pre-coref: "); print_dg(dg); printf("\n");

	if(patch_coreferences(&R, dg))
	{
		fprintf(stderr, "dagify: failed to patch in coreferences\n");
#ifdef	UNIFY_PATHS
		unify_backtrace();
#endif
		dg = NULL;
	}
	_current_building_type = NULL;
	dg = p_dereference_dg(dg);

	for(i=0;i<R.ncorefs;i++)
	{
		if(R.corefs[i].path)
			free(R.corefs[i].path);
		free(R.corefs[i].name);
	}
	if(R.corefs)free(R.corefs);

	/*if(R.ntcopies)
	{
		saved_tcopies = R.tcopies;
		saved_ntcopies = R.ntcopies;
	}
	else
	{
		saved_tcopies = NULL;
		saved_ntcopies = 0;
	}*/

	return dg;
}

int	lexify_tdl_line(struct tdl_line	*line, void	*ref)
{
	char	*lhs = line->lhs, *rhs = line->rhs;
	struct dg	*dg;
	char	*type, *amp, *dag;
	struct type	*ty;
	extern int	study_lexeme(char	*name, struct dg	*dg, struct type	*t);

	amp = strchr(rhs, '&');
	if(!amp)
	{
		//fprintf(stderr, "lexeme `%s': no & found\n", lhs); return -1;
		dag = strdup("[ ]");
	}
	else
	{
		*amp = 0;
		dag = trim_string(amp+1);
	}

	type = trim_string(rhs);

	dg = dagify(dag, 0);
	if(!dg) { fprintf(stderr, "hint: dagify failed\n"); return -1; }

	ty = lookup_type(type);
	if(!ty) { fprintf(stderr, "lexeme `%s' has nonextant type `%s'\n", lhs, type); return -1; }
	return study_lexeme(lhs, dg, ty);
}

int	dagify_tdl_line(struct tdl_line	*line, void	*ref)
{
	char	*lhs = line->lhs, *rhs = strdup(line->rhs);
	struct dg	*dg;
	struct type	*bt = 0;
	int		(*callback)(char	*name, struct dg	*dg, struct tdl_line	*line) = ref;

	if(enable_out_of_order)
	{
		bt = lookup_type(lhs);
		if(!bt)
		{
			fprintf(stderr, "tdl: no such type to constrain `%s'\n", lhs);
			return -1;
		}
	}

	//if(!strcmp(bt->name, "prep_nomod_phr_synsem"))loud_noises = 1;
	//else loud_noises = 0;

	//printf("constrain `%s' by `%s'\n", lhs, rhs);

	//char	*type_of_interest = "pres-tense-lex-rule";
	//char	*type_of_interest = "verb-tense-lex-rule";
	//char	*type_of_interest = "add-only-no-ccont-rule";

	/*if(!strcmp(lhs, type_of_interest))
	{
		printf("authored constraints on '%s'\n", lhs);
		printf("string: %s\n", rhs);
	}*/

	dg = dagify(rhs, bt);
	if(!dg) { fprintf(stderr, "hint: dagify failed\n"); return -1; }

	/*if(!strcmp(lhs, type_of_interest))
	{
		printf("built constraints on '%s'\n", lhs);
		print_dg(dg);
		printf("\n");
	}*/

	return callback(lhs, dg, line);
}

int	typify_tdl_line(struct tdl_line	*line, void	*ref)
{
	char	*lhs = line->lhs, *rhs_save = line->rhs;
	struct type	**parents = 0;
	int		nparents = 0, done = 0;
	int		depth = 0, quote = 0;
	int		res;
	char		*rhs = strdup(rhs_save);
	char		*p, *chunk = rhs;

	for(p=rhs;!done;p++)
	{
		if((*p=='&' && depth==0 && quote==0) || *p==0)
		{
			if(depth!=0 || quote!=0)
			{
				fprintf(stderr, "unbalanced brackets or quotes!\n");
				return -1;
			}
			if(!*p)done = 1;
			*p = 0;
			if(!(*chunk=='<' || *chunk=='#' || *chunk=='['))
			{
				char	*name = trim_string(chunk);
				if(*name=='"')
				{
					// string 'name' is a comment on type 'lhs'
					// do nothing with it.
				}
				else if(!strcmp(name, "__ace__unique_corefs"))
				{
					// we artificially insert this to mark the boundary between addenda.
					// it is not a parent type; ignore it for our current purpose.
				}
				else
				{
					nparents++;
					parents = realloc(parents, sizeof(struct type*)*nparents);
					parents[nparents-1] = find_type(name, 0);
					if(!parents[nparents-1])
					{
						printf("couldn't find type '%s'\n", name);
						free(parents);
						return -1;
					}
				}
			}
			if(!done)chunk = trim_string(p+1);
		}
		else if(!quote && (*p == '[' || *p=='<'))depth++;
		else if(!quote && (*p == ']' || *p=='>'))depth--;
		else if(*p == '"')quote = !quote;
		else if(*p == '\\' && p[1])p++;
	}
	res = add_type_only(lhs, nparents, parents, 0);
	if(parents)free(parents);
	free(rhs);

	return res;
}

int	g_loaded = 0;
extern int	nlexemes, nrules, norules, ninstances, glb_type_count, debug_level, nfnames;

void run_task(char *task, int (*worker)())
{
	int ret;
	struct timeval tv1, tv2;

	show_task_name(task);
	gettimeofday(&tv1, 0);
	ret = worker();
	gettimeofday(&tv2, 0);
	if(ret)
	{
		fprintf(stderr, "\033[33;1mFAIL\033[0m\n");
		exit(-1);
	}
	else
	{
		float s = (tv2.tv_sec - tv1.tv_sec) + 0.000001 * (tv2.tv_usec - tv1.tv_usec);
		if(s > 0.1) printf("%.2f sec\n", s);
		else printf("%d ms\n", (int)(1000*s));
	}
}

void	load_version(char *path)
{
	if(!path)
	{
		grammar_version = "unknown";
		return;
	}
	load_lisp(path);
	char	*v = get_lisp_parameter("*grammar-version*");
	if(!v)grammar_version = "unknown";
	else
	{
		grammar_version = v;
		show_task_name("grammar version");
		printf("%s\n", grammar_version);
	}

	/*
	FILE	*f = fopen(path, "r");
	char	record[1024], *p = record, in = 0;

	if(!f)
	{
		fprintf(stderr, "couldn't load version from `%s'\n", path);
		grammar_version = strdup("couldn't load version file");
		return;
	}
	while(!feof(f))
	{
		*p = fgetc(f);
		if(*p=='"')in = !in;
		else if(in)p++;
	}
	*p = 0;
	if(!record[0])grammar_version = "unknown";
	else
	{
		grammar_version = strdup(record);
		show_task_name("grammar version");
		printf("%s\n", grammar_version);
	}
	*/
}

void	recursive_bleach(struct dg	*dg, struct type	*top)
{
	dg = dereference_dg(dg);
	assert(dg != NULL);
	dg->type = dg->xtype = top;
	int i;
	struct dg	**arcs = DARCS(dg);
	for(i=0;i<dg->narcs;i++)
		recursive_bleach(arcs[i], top);
}

int	mtrify_tdl_line(struct tdl_line	*line, void	*ref)
{
	char	*lhs = line->lhs, *rhs = line->rhs;
	int	(*process_mtr)(char	*lhs, struct dg	*main_dg, struct dg	*output_override) = ref;

	// first, split off the rule type
	char	*type, *amp, *dag;

	amp = strchr(rhs, '&');
	if(!amp)
	{
		//fprintf(stderr, "transfer rule `%s': no & found\n", lhs); return -1;
		dag = strdup("[ ]");
	}
	else
	{
		*amp = 0;
		dag = trim_string(amp+1);
	}
	type = trim_string(rhs);
	struct dg	*tydg = type_dg(type);
	if(!tydg) { fprintf(stderr, "transfer rule `%s' has nonextant type `%s'\n", lhs, type); return -1; }

	//printf("transfer rule '%s'\n", lhs);
	//printf("unparsed rhs: %s\n", dag);

	struct dagify_record	R;
	bzero(&R, sizeof(R));
	struct dg	*main_dg = rdagify(&R, dag);
	if(!main_dg)return -1;

	//printf("main dg before type or bleaching:\n"); print_dg(main_dg);printf("\n");

	// copy OUTPUT as output_override, and then bleach out main_dg/OUTPUT types to *top*

	struct dg	*main_out = dg_hop(main_dg, lookup_fname("OUTPUT"));
	struct dg	*output_override;
	if(!main_out)main_out = atomic_dg(top_type);	// some rules have no output and the MTR file doesn't bother to mention one
	output_override = copy_dg(main_out);
	recursive_bleach(main_out, lookup_type(top_type));
	//printf("bleached main_out:\n"); print_dg(main_out); printf("\n");

	// now apply coreferences
	if(patch_coreferences(&R, main_dg))
	{
		fprintf(stderr, "mtrify: failed to patch in coreferences\n");
#ifdef	UNIFY_PATHS
		unify_backtrace();
#endif
		return -1;
	}
	main_dg = p_dereference_dg(main_dg);
	int i;
	for(i=0;i<R.ncorefs;i++)
	{
		if(R.corefs[i].path)
			free(R.corefs[i].path);
		free(R.corefs[i].name);
	}
	if(R.corefs)free(R.corefs);

	// unify rule type into main_dg (but not into output_override)
	if(0 != unify_dg_infrom(main_dg, tydg))
	{
		fprintf(stderr, "mtr: `%s' couldn't unify with rule type `%s'\n", lhs, type);
#ifdef	UNIFY_PATHS
		unify_backtrace();
#endif
		return -1;
	}
	main_dg = dereference_dg(main_dg);

	//printf("transfer rule '%s'\n", lhs);
	//printf("main dg with bleached OUTPUT:\n"); print_dg(main_dg);printf("\n");
	//printf("output_override dg:\n"); print_dg(output_override);printf("\n");

	return process_mtr(lhs, main_dg, output_override);
}

int	process_mtr_status(char	*status, int	(*process)(char	*lhs, struct dg	*main_dg, struct dg	*output_override))
{
	return process_tdl_status(status, mtrify_tdl_line, process);
}

void	load_triggers(char	*path)
{
	if(!path)return;
	tdl_push_status("trigger-rule");
	load_tdl(path);
	tdl_pop_status();
	process_mtr_status("trigger-rule", study_trigger_rule);
}

void	load_idioms(char	*path)
{
	char	*nir = get_conf("non-idiom-root");
	if(!nir)non_idiom_root = NULL;
	else non_idiom_root = strdup(nir);
	//printf("CONF: non_idiom_root = '%s'\n", non_idiom_root);
	if(!path)return;
	tdl_push_status("idiom-rule");
	load_tdl(path);
	tdl_pop_status();
	process_mtr_status("idiom-rule", study_idiom_rule);
}

void	load_fixup_rules(char	*path)
{
	if(!path)return;
	tdl_push_status("fixup-rule");
	load_tdl(path);
	tdl_pop_status();
	g_transfer = 1;
	process_mtr_status("fixup-rule", study_fixup_rule);
	g_transfer = 0;
}

void	load_cleanup_rules(char	*path)
{
	if(!path)return;
	tdl_push_status("cleanup-rule");
	load_tdl(path);
	tdl_pop_status();
	g_transfer = 1;
	process_mtr_status("cleanup-rule", study_cleanup_rule);
	g_transfer = 0;
}

char	*grammar_dir;

int	load_grammar_top(char *toptdl)
{
	if(!toptdl)
	{
		fprintf(stderr, "ERROR: config file did not specify grammar-top tdl file\n");
		exit(-1);
	}

	grammar_dir = strdup(toptdl);
	if(strrchr(grammar_dir, '/') > grammar_dir)
		*strrchr(grammar_dir, '/') = 0;
	else grammar_dir = ".";

	load_tdl(toptdl);
#ifdef SLEX
	tdlstatus = "lex-entry";
	load_tdl("special-lex.tdl");
	tdlstatus = 0;
#endif

	if(g_transfer)
	{
		char	buffer[1024];
		extern char	**fnames;
		sprintf(buffer, "[ %s %s ]", fnames[instloc_feature], top_type);
		tdlstatus = "type";
		add_tdlline(semarg_type, '+', strdup(buffer), NULL, 0, "internal");
		tdlstatus = NULL;
	}

	if(load_types())exit(-1);
	if(g_transfer == 0)
	{
		run_task("processing rules", load_rules);
		run_task("processing lex-rules", load_lrules);
		if(load_all_irregulars())exit(-1);
		if(load_lexicon())exit(-1);
		if(load_instances())exit(-1);
		if(load_token_mapping_rules())exit(-1);
		if(load_lexical_filtering_rules())exit(-1);
		if(load_post_generation_mapping_rules())exit(-1);
	}
	else
	{
		run_task("processing transfer rules", load_transfer_rules);
	}

	number_strings();

	if(g_transfer == 0)
		fprintf(stderr, "%d types (%d glb), %d lexemes, %d rules, %d orules, %d instances, %d strings, %d features\n",
				default_type_hierarchy()->ntypes, glb_type_count, nlexemes, nrules, norules, ninstances, default_type_hierarchy()->nstrings, nfnames);
	else fprintf(stderr, "%d types (%d glb) %d transfer rules, %d strings, %d features\n",
				default_type_hierarchy()->ntypes, glb_type_count, ntransfer_rules, default_type_hierarchy()->nstrings, nfnames);
	return 0;
}

int	load_quickcheck()
{
	char	*qccode_path = get_conf_file_path("quickcheck-code");
	if(!qccode_path)
	{
		char	*qcinst_name = get_conf("quickcheck-instance");
		if(!qcinst_name)
		{
			fprintf(stderr, "Neither `quickcheck-code' nor `quickcheck-instance' was configured.\n");
			exit(-1);
		}
		struct dg	*qcinst = find_instance(qcinst_name);
		if(!qcinst)
		{
			fprintf(stderr, "Couldn't find quickcheck instance `%s'\n", qcinst_name);
			exit(-1);
		}

		// make a temporary file and write QC code to it
		char	*tmpdir = getenv("TMPDIR")?:"/tmp";
		char	target_path[1280];
		sprintf(target_path, "%s/qcex.txt-XXXXXX", tmpdir);
		int	fd = mkstemp(target_path);
		FILE	*f = fopen(target_path, "w");
		if(!f) { perror(target_path); exit(-1); }
		write_qccode_from_pet_instance(qcinst, f);
		fclose(f);

		// compile the code and remove the temporary file
		compile_qc(target_path);
		unlink(target_path);
		close(fd);
	}
	else
	{
		compile_qc(qccode_path);
	}
}

int load_grammar(char	*path)
{
	extern int g_mode;

	g_mode = -1;

	clear_slab();
	tdl_hash = hash_new("tdl type definitions");

	tdl_push_status("config");
	int result = load_tdl(path);
	if(result == -1)exit(-1);
	tdl_pop_status();

	init_fnames();
	load_conf();
	load_version(get_conf_file_path("version"));

	if(!g_transfer)
	{
		load_preprocessor();

		// before grammar loading so the semindex knows how to build
		load_expedients(get_conf_file_path("generation-ignore-signs"));
		load_expedients(get_conf_file_path("generation-ignore-lexemes"));
		load_expedients(get_conf_file_path("generation-ignore-rules"));
	}

	init_type_hierarchy();
	// want the SEM-I loaded before the grammar so that semantic indexing can take place during lexicon loading
	if(!g_transfer)load_semi(get_conf_file_path("semantic-interface-2016"));
	else load_semi(NULL);

	load_grammar_top(get_conf_file_path("grammar-top"));

	if(!g_transfer)
	{
		load_triggers(get_conf_file_path("generation-trigger-rules"));
		load_fixup_rules(get_conf_file_path("generation-fixup-rules"));
		load_cleanup_rules(get_conf_file_path("cleanup-rules"));
		load_idioms(get_conf_file_path("idiom-rules"));

		load_parser_vpm(get_conf_file_path("variable-property-mapping"));

		int do_load_mem() { load_mem(get_conf_file_path("maxent-model")); return 0; }
		run_task("loading maxent model", do_load_mem);

		// XXX this won't be necessary if we can convince people to use a tdl-status for their parse-node-labels files...
		tdl_push_status("tree-node-label");
		load_tdl(get_conf_file_path("parse-node-labels"));
		tdl_pop_status();
		if(load_labels())exit(-1);

		load_quickcheck();
		setup_rule_filter();
		//prepare_qc_rules();
	}
	else
	{
		if(get_conf("input-vpm"))
		{
			load_transfer_input_vpm(get_conf_file_path("input-vpm"));
			load_transfer_output_vpm(get_conf_file_path("output-vpm"));
		}
		else load_transfer_bidir_vpm(get_conf_file_path("bidir-vpm"));
	}

	// make sure we have complete restrictor sets in case recent activity has added new features...
	load_restrictors();

#ifdef	POST
	if(enable_post)
	{
		char	*post_model_path = get_conf_file_path("post-model-path");
		if(!post_model_path)post_model_path = "post/english-postagger.hmm";
		//post_train_from("../post/brown.train.txt");
		int post_load_result = post_load_from_text_dump(post_model_path);
		if(post_load_result != 0)
		{
			fprintf(stderr, "unable to read `%s'.\n", post_model_path);
			fprintf(stderr, "disabling built-in POS tagger (TNT support is still available).\n");
			fprintf(stderr, "to re-enable the built-in POS tagger, either:\n");
			fprintf(stderr, "  - make sure `%s' exists (e.g. run ACE from the ace-" ACE_VERSION "/ directory), or", post_model_path);
			fprintf(stderr, "  - set the `post-model-path' configuration variable appropriately\n");
			enable_post = 0;
		}
	}
#endif

	if(get_conf("ubertag-emission-path") || get_conf("übertag-emission-path"))
		run_task("loading übertagger", load_ubertagging);

	// make sure none of the grammar is auto-freed when the first parse is over
	//free_tdl();	 // actually, don't free the TDL; want to be able to freeze some of it into the .dat file.
	commit_slab();

	// make sure all string types have numbers
	number_strings();

	return 0;
}
