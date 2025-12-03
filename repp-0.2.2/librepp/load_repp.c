#define	UNICODE
#define	REPP_INTERNAL
#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<wchar.h>
#include	<boost/regex.h>

#include	"unicode.h"
#include	"librepp.h"

#define	REGEX_FLAGS	REG_PERL

//#define	DEBUG	printf
#define	DEBUG(fmt, ...)	do {} while(0)

static int	load_repp_module_from_file_with_name(struct preprocessor	*repp, char	*fname, wchar_t	*name);

wchar_t	*_repp_freeze_wcs(wchar_t	*win, void*	(*alloc)(int len))
{
	if(!win)return NULL;
	int	len = wstrlen(win);
	wchar_t	*wout = alloc(sizeof(wchar_t)*(len+1));
	return wstrcpy(wout, win);
}

void	*_repp_freeze_block(void	*block, int	len, void*	(*alloc)(int len))
{
	void	*out = alloc(len);
	memcpy(out, block, len);
	return out;
}

struct preprocessor_module	*freeze_repp_module(struct preprocessor_module	*mod, void*	(*alloc)(int len))
{
	struct preprocessor_module	*f_mod = alloc(sizeof(struct preprocessor_module));
	bzero(f_mod, sizeof(*f_mod));
	int i;
	f_mod->name = _repp_freeze_wcs(mod->name, alloc);
	f_mod->nrules = mod->nrules;
	f_mod->is_iterative = mod->is_iterative;
	f_mod->is_enabled = mod->is_enabled;
	f_mod->rules = _repp_freeze_block(mod->rules, sizeof(struct pprule)*mod->nrules, alloc);
	for(i=0;i<f_mod->nrules;i++)
	{
		f_mod->rules[i].pat = _repp_freeze_wcs(mod->rules[i].pat, alloc);
		f_mod->rules[i].rep = _repp_freeze_wcs(mod->rules[i].rep, alloc);
	}
	return f_mod;
}

struct preprocessor	*repp_clone(struct preprocessor	*repp, void*	(*alloc)(int	len))
{
	int	i;
	struct preprocessor	*f_repp = alloc(sizeof(struct preprocessor));
	bzero(f_repp, sizeof(*f_repp));
	f_repp->nmodules = repp->nmodules;
	f_repp->delim_pat = _repp_freeze_wcs(repp->delim_pat, alloc);
	f_repp->modules = alloc(sizeof(struct preprocessor_module*) * f_repp->nmodules);
	for(i=0;i<repp->nmodules;i++)
	{
		f_repp->modules[i] = freeze_repp_module(repp->modules[i], alloc);
		if(repp->modules[i] == repp->main_module)
			f_repp->main_module = f_repp->modules[i];
	}
	return f_repp;
}

void	repp_print_rules(struct preprocessor	*repp)
{
	int	i, j;

	printf("repp tokenization pattern: %S\n", repp->delim_pat);
	for(i=0;i<repp->nmodules;i++)
	{
		struct preprocessor_module	*mod = repp->modules[i];
		printf("repp module '%S':\n", mod->name);
		for(j=0;j<mod->nrules;j++)
		{
			if(mod->rules[j].type == rtReplace)
				printf("  repl:  pat=`%S', rep=`%S'\n", mod->rules[j].pat, mod->rules[j].rep);
			else printf("  call:  %S\n", mod->rules[j].pat);
		}
	}
}

void	repp_compile_rules(struct preprocessor	*repp)
{
	int		i, j, err;

	err = regcomp(&repp->delim, repp->delim_pat, REGEX_FLAGS);
	if(err)
	{
		wchar_t buf[1024];
		regerror(err, &repp->delim, buf, 1023);
		fprintf(stderr, "preprocessor: while compiling `%S': %S\n", repp->delim_pat, buf);
		exit(-1);
	}
	for(i=0;i<repp->nmodules;i++)
	{
		struct preprocessor_module	*mod = repp->modules[i];
		for(j=0;j<mod->nrules;j++)
		{
			if(mod->rules[j].type == rtReplace)
			{
				err = regcomp(&mod->rules[j].re, mod->rules[j].pat, REGEX_FLAGS);
				if(err)
				{
					wchar_t buf[1024];
					regerror(err, &mod->rules[j].re, buf, 1023);
					fprintf(stderr, "preprocessor: while compiling `%S': %S\n", mod->rules[j].pat, buf);
					exit(-1);
				}
			}
		}
	}
}

struct preprocessor_module	*repp_find_module(struct preprocessor	*repp, wchar_t	*name)
{
	int	i;
	for(i=0;i<repp->nmodules;i++)
		if(!wstrcmp(repp->modules[i]->name, name))return repp->modules[i];
	return NULL;
}

static int	load_repp_module(struct preprocessor	*repp, int	nlines, wchar_t	**lines, char	*basepath, wchar_t	*name)
{
	wchar_t	subpath[1024];
	wchar_t	*line, typec, pattern[1024], rep[1024], *p, *s;
	int	lnum;

	struct preprocessor_module	*mod = repp_find_module(repp, name);
	if(!mod)
	{
		mod = calloc(sizeof(*mod), 1);
		mod->name = wstrdup(name);
		repp->nmodules++;
		repp->modules = realloc(repp->modules, sizeof(void*)*repp->nmodules);
		repp->modules[repp->nmodules-1] = mod;
	}

	for(lnum=0;lnum<nlines;lnum++)
	{
		line = lines[lnum];
		if(line[0]==0)continue;
		if(line[0]==';')continue;

		typec = line[0];
		p = line+1;
		s = pattern;
		while(*p && *p != '\t')*s++ = *p++;
		*s = 0;

		switch(typec)
		{
			case	'@':	/*fprintf(stderr, "date: %S\n", pattern);*/	continue;
			case	':':	repp->delim_pat = wide_unescape(pattern);		continue;
			case	'<':
				swprintf(subpath, 1023, L"%s/%S", basepath, pattern);
				load_repp_module_from_file_with_name(repp, tombs(subpath), name);
				continue;
			case	'>':
				// external group call
				mod->nrules++;
				mod->rules = realloc(mod->rules, sizeof(struct pprule) * mod->nrules);
				mod->rules[mod->nrules-1].type = rtGroupCall;
				if(wide_is_number(pattern))
				{
					swprintf(subpath, 1023, L"%S/%S", name, pattern);
					mod->rules[mod->nrules-1].pat = wstrdup(subpath);
				}
				else mod->rules[mod->nrules-1].pat = wstrdup(pattern);
				mod->rules[mod->nrules-1].rep = NULL;
				continue;
			case	'#':
				assert(wide_is_number(pattern));
				swprintf(subpath, 1023, L"%S/%S", name, pattern);
				DEBUG("studying internal group '%S'\n", subpath);
				int	lstart = lnum+1, group_depth = 1;
				for(lnum=lstart;lnum<nlines;lnum++)
					if(lines[lnum][0]=='#')
					{
						if(lines[lnum][1])group_depth++;
						else group_depth--;
						if(group_depth == 0)break;
					}
				if(lnum==nlines)
				{
					fprintf(stderr, "internal group '%S' never closed\n", subpath);
					exit(-1);
				}
				load_repp_module(repp, lnum - lstart, lines+lstart, basepath, subpath);
				struct preprocessor_module	*submod = repp_find_module(repp, subpath);
				submod->is_enabled = 1;
				submod->is_iterative = 1;
				continue;
			case	'!':
				if(*p != '\t')
				{
					fprintf(stderr, "format error at %S:%d: replace rule needs two fields.\n", name, lnum);
					exit(-1);
				}
				while(*p=='\t')p++;
				wstrcpy(rep, p);

				mod->nrules++;
				mod->rules = realloc(mod->rules, sizeof(struct pprule) * mod->nrules);
				mod->rules[mod->nrules-1].type = rtReplace;
				mod->rules[mod->nrules-1].pat = wide_unescape(pattern);
				mod->rules[mod->nrules-1].rep = wstrdup(rep);
				continue;
			default:	fprintf(stderr, "format error: unknown type `%c'.\n", typec); continue; //exit(-1);
		}
	}
	return 0;
}

static int	load_repp_module_from_file_with_name(struct preprocessor	*repp, char	*fname, wchar_t	*name)
{
	if(!fname)return 0;

	FILE	*f = fopen(fname, "r");

	if(!f)
	{
		perror(fname);
		exit(-1);
	}

	char	line[1024], basepath[1024];

	strcpy(basepath, fname);
	char	*p = strrchr(basepath, '/');
	if(!p)strcpy(basepath, ".");
	else *p = 0;

	int	nlines = 0;
	wchar_t	**lines = NULL;

	while(fgets(line, 1024, f))
	{
		if(!*line)break;
		//if(line[0]==';')continue;
		//if(line[0]=='\n')continue;
		line[strlen(line)-1] = 0;

		nlines++;
		lines = realloc(lines, sizeof(wchar_t*)*nlines);
		lines[nlines-1] = towide(line);
	}

	load_repp_module(repp, nlines, lines, basepath, name);

	fclose(f);
	return 0;
}

int			repp_load_module(struct preprocessor	*repp, char	*fname, char	*module_name, int	enable)
{
	wchar_t	*mod_name;

	if(module_name)mod_name = towide(module_name);
	else
	{
		char	*basename = strrchr(fname, '/');
		if(!basename)basename = fname;
		else basename++;
		basename = strdup(basename);
		if(strchr(basename, '.'))*strchr(basename, '.') = 0;
		mod_name = towide(basename);
	}

	int	r = load_repp_module_from_file_with_name(repp, fname, mod_name);
	struct preprocessor_module	*mod = repp_find_module(repp, mod_name);
	mod->is_enabled = enable;
	return r;
}

void			repp_enable_module(struct preprocessor_module	*m, int	enable)
{
	m->is_enabled = enable;
}

struct preprocessor	*repp_load(char	*fname)
{
	struct preprocessor	*repp = calloc(sizeof(*repp),1);
	int	r = load_repp_module_from_file_with_name(repp, fname, L"main");
	if(r != 0)
	{
		fprintf(stderr, "unable to load main repp module '%s'\n", fname);
		exit(-1);
	}
	struct preprocessor_module	*main_mod = repp_find_module(repp, L"main");
	main_mod->is_enabled = 1;
	repp->main_module = main_mod;
	//repp_print_rules(repp);
	return repp;
}
