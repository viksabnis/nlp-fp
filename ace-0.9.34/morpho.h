#ifndef	_MORPHO_H
#define	_MORPHO_H

#include	<wchar.h>
#include	"lexicon.h"
#include	"rule.h"

struct orule
{
	struct rule	*rule;
	enum { or_suffix = 1, or_prefix = 2 } type;
	int		nsub;
	struct orule_sub
	{
		wchar_t		*pat;
		int			patl;
		wchar_t		*rep;
		int			repl;
	}		*sub;

	struct hash	*irregs_stem_to_form;
	struct hash	*irregs_form_to_stem;

	/*int		nirregs;
	struct irreg
	{
		wchar_t	*form, *stem;
	}	*irregs_f, *irregs_s;*/
};

// letterset membership is represented by a lookup table for 8-bit characters and a list for other chars
struct letterset
{
	char	lower[256];	
	int		nhigher;
	wchar_t	*higher;
};

struct morpho_globals
{
	struct letterset	*lsets[256];
};

extern int		norules;
extern struct orule	**orules;

struct edge;
struct token;
struct lattice;
int	lexical_lookup(struct lattice	*tc, void	(*edge_handler)(struct edge	*e, struct token	**tokens));
char	*inflect(struct orule	*or, char	*str);
void	setup_morpho(char	*line);
int		load_lrules();
void	add_orule(struct rule	*rule, char	*def);

struct orule	*freeze_orule(struct orule	*orin);
struct morpho_globals	*freeze_morpho_globals();

int	unify_orthography(struct dg	*d, struct dg	*dtr, struct lexeme	*lex, struct rule	*r);

#endif
