#ifndef	REPP_H
#define	REPP_H

#ifdef	REPP_INTERNAL
enum
{
	rtReplace = 1,
	rtGroupCall = 2,
};

struct pprule
{
	int		type;
	wchar_t	*pat, *rep;
	regex_t	re;
};

struct preprocessor_module
{
	wchar_t			*name;
	int				is_enabled, is_iterative;
	int				nrules;
	struct pprule	*rules;
};

struct preprocessor
{
	int				nmodules;
	struct preprocessor_module	**modules;
	struct preprocessor_module	*main_module;
	wchar_t			*delim_pat;
	regex_t			delim;
};
#else
struct preprocessor_module;
struct preprocessor;
#endif

struct preprocessor	*repp_load(char	*file_path);
struct preprocessor	*repp_clone(struct preprocessor	*repp, void*	(*alloc)(int	len));
int			repp_load_module(struct preprocessor	*p, char	*file_path, char	*module_name, int	enable);
void			repp_enable_module(struct preprocessor_module	*m, int	enable);

struct preprocessor_module	*repp_find_module(struct preprocessor	*repp, wchar_t	*name);
void	repp_print_rules(struct preprocessor	*repp);
void	repp_compile_rules(struct preprocessor	*repp);

int	repp_preprocess(struct preprocessor	*repp, char	*mbstring, int	*Nwords, char	***Words, int	**CFrom, int	**CTo);

#endif
