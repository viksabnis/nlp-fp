#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<librepp.h>

#include	"dag.h"
#include	"tdl.h"

struct preprocessor	*repp;

int	load_repp_module_from_file(char	*fname)
{
	return repp_load_module(repp, fname, NULL, 1);
}

int	load_repp(char	*fname)
{
	repp = repp_load(fname);
	return repp?0:-1;
}

void	*freeze_repp()
{
	if(!repp)return NULL;
	return repp_clone(repp, slab_alloc);
}

void	recover_repp(void	*ptr)
{
	repp = ptr;
	if(!repp)return;
	repp_compile_rules(repp);
}

void	preprocess_line(char	*mbstring, int	*Nwords, char	***Words, int	**CFrom, int	**CTo)
{
	if(!repp)
	{
		fprintf(stderr, "This grammar was compiled with no REPP preprocessor.\n");
		fprintf(stderr, "Either add a REPP preprocessor or provide input pre-tokenized in YY format (-y).\n");
		exit(-1);
	}
	int	result = repp_preprocess(repp, mbstring, Nwords, Words, CFrom, CTo);
	assert(result == 0);
}

void	load_preprocessor()
{
	char	*path = get_conf_file_path("preprocessor");
	if(!path)return;
	char	*dir = get_conf_parent_dir("preprocessor");
	load_repp(path);
	int	repp_module_callback(char	*path) {
		char	*modpath;
		asprintf(&modpath, "%s/%s", dir, path);
		return load_repp_module_from_file(modpath); }
	iterate_conf_list("preprocessor-modules", repp_module_callback);
	free(dir);
}
