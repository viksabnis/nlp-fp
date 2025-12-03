#include	"tree.h"

#include	"hash.h"
#include	"dag.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"mrs.h"

enum
{
	reconsNoSuchLexeme,
	reconsIncompatibleToken,
	reconsNoSuchRule,
	reconsRuleGLB,
	reconsRuleCycle
};

struct reconstruction_error
{
	int		type;
	struct tree	*node;
	int		daughter;
	char		*path;
	char		*type1, *type2;
	char		*comment;
};

struct dg	*reconstruct_tree_or_error(struct tree	*t, void	(*callback)(struct tree	*t, struct dg	*d), struct reconstruction_error	*err);
struct dg	*reconstruct_tree(struct tree	*t, void	(*callback)(struct tree	*t, struct dg	*d));
void	free_mrs_stuff(struct mrs	*m);
struct lexeme	*get_lex_by_name_hash(char	*name);

extern int	reconstruction_noise_level;
