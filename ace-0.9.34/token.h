#ifndef	TOKEN_H
#define	TOKEN_H

#include	"lattice-mapping.h"

struct token
{
	char	*string;
	int	npostags;
	struct postag
	{
		char	*tag;
		char	*prob;
	}	*postags;
	int	nids, *ids;
	int		cfrom, cto;
	struct dg	*dg;

	struct ochart	*oc;

	int	eid;	// edge id when we pretend tokens are edges
	int	used;	// starts at 0 and is set to 1 when we reach it from a root
};

struct lattice	*build_token_chart(int	nwords, char	**words, int	*cfrom, int	*cto);
void	build_token_dag(struct token	*t);
void	print_token_chart(struct lattice	*tc);
char	*get_token_carg(struct token	*t);

struct edge;
int		install_tokens_in_le(struct edge	*le, struct token	**tokens);

#endif
