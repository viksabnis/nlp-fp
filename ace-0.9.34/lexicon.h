#ifndef	_LEXICON_H
#define	_LEXICON_H

#include	"dag.h"

struct lexeme
{
	char		*word;
	struct dg	*dg;

	int		stemlen:16, onset:16;
	struct type	**stem;
	struct type	*lextype;

	struct type	*pred;		// this lexeme provides relation 'pred'
};

#include	"rule.h"
#include	"morpho.h"

struct generic_le_info
{
	int		for_generation;
	char	part_of_speech_trigger[8];
};

int	visit_lexicon(char	*stem, int (*visitor)(struct lexeme *lex));
void	dump_parts_of_speech();
int		load_lexicon();
struct dg	*expand_lexeme(struct lexeme	*l);
struct edge	*lexical_edge(struct lexeme	*lex, int	i, int	len, struct dg	*rels);
struct dg	*lexical_dg(struct lexeme *lex, struct dg	*rels);
struct lexeme	*get_lex_by_name(char *name);
struct lexeme	*get_lex_by_name_hash(char	*name);

extern int nlexemes;
extern struct lexeme	**lexemes;
extern int		ngeneric_les;
extern struct lexeme	**generic_les;
extern struct generic_le_info	*generic_le_infos;

// semantic index
void	add_semantic_index(struct lexeme *l, struct dg *full, int which);
int		add_lexemes_for_relation(int	x, char	*rel, int (*skolemize)(struct edge	*e, struct lexeme	*lex));
int		add_rules_for_relation(char	*rel, int (*skolemize)(struct edge	*e, struct rule	*rule));
void	*freeze_semantic_index();
void	recover_semantic_index(void *frozen_hash);

struct lexeme	*instantiate_gle(struct lexeme	*gle, char	*surface, char	*carg);

#endif
