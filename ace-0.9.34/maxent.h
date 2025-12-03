#ifndef	MAXENT_H
#define	MAXENT_H

#define	MAX_GRANDPARENTING	3

struct scoring_ancestry
{
	int		nparent_types;
	int		rooted;
	//char	**parent_types;
	signed short	gprnum[MAX_GRANDPARENTING];
	unsigned int	hash;
};

int		load_mem(char *fname);
void	*freeze_stochastic_model();
void	recover_stochastic_model(void *frozen);
float	maxent_score(char *lhs, char *rhs1, char *rhs2, int rtl, struct scoring_ancestry	*anc);
float	maxent_score_ro(int lhs, int rhs1, int rhs2, struct scoring_ancestry	*anc);

#endif
