#ifndef	DAG_PROVENANCE_H
#define	DAG_PROVENANCE_H

#include	"conf.h"

struct dg_provenance
{
	enum { FROM_VACUUM, FROM_LUI_EDGE, FROM_LUI_TREE, FROM_TREE, FROM_EDGE, FROM_TYPE, FROM_TYPE_LOCAL, FROM_LEX, FROM_LEX_LOCAL, FROM_RULE, FROM_RULE_LOCAL, FROM_UNIFY }	kind;
	char	*arg0id, *arg1id;
	void	*arg0ptr, *arg1ptr;
	char	*arg0path, *arg1path;
};

int	show_provenance(struct path	path, struct dg_provenance	*p);
int	show_provenance_from_unification(struct path	path, struct dg	*left, struct dg_provenance	*leftp, int	nright, struct dg	**right, struct dg_provenance	**rightp, int	*rightarg);

struct hypothesis	*lui_find_tree(char	*id);
struct edge	*lui_find_edge(char	*id);

struct dg_provenance	make_provenance(int	kind, void	*ptr);

#endif
