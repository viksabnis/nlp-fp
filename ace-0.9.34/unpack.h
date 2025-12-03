#include	"maxent.h"

struct decomposition
{
	struct edge *edge;
	struct edge **rhs;

	int	*seen_indices;
	int	nsi, asi;

	float	local_score;
	double	all_unpackings_z;
	int		is_scored;

	int		checked;	// bitfield for whether local unification has been verified
	int		failed;		// bitfield for whether local unification verification failed
};

struct hypothesis
{
	// internal to a hypothesis as a tree
	// even if there are several ways of scoring a tree (different grandparents),
	// this portion remains constant and can be a shared structure in theory...
	struct decomposition *dec;
	struct edge			*edge;	// redundant, but allows struct hypothesis to be used when we aren't doing decompositions.
	int					arity;
	struct hypothesis	**rhslist;
	struct dg			*dg;		// reconstructed
	char				*string;	// surface yield
	int					checkup;

	int	eid;	// assign each unique subtree/hypothesis an edge id in unpacking, to make it look like we aren't doing any packing.  with --packed-edge-ids, this gets edge->id instead.
	int	toklen;	// how many tokens this tree spans

	// internal to a hypothesis as a scored tree
	// this part will be different for different ancestry contexts
	int					*indexlist;
	float				score;
	struct scoring_ancestry	ancestry;
};

struct hypagenda_item
{
	struct hypothesis	*h;

	// as an element of an agenda
	struct hypagenda_item *left, *right;
};

struct unpack_info	// used by hypothesize_edge() to keep track of what hypothesis is ranked next, and to cache
{
	struct context_unpack_info
	{
		struct hypagenda_item *agenda;
		struct hypothesis **hypotheses;
		int	nhypotheses, ahypotheses;
		int	ndecs;
		struct decomposition	*decs;

		struct scoring_ancestry	ancestry;
	}	**cuis;
	int	ncuis;
	// could also include a list of (struct hypothesis*) for reuse...
};

struct mrs;
int iterate_cell_root_hypotheses(struct chart_cell *cell, int (*process)(struct hypothesis *hyp, struct mrs *mrs, double	probability), int nbest);
struct hypothesis *hypothesize_edge(struct edge *e, int rank, struct scoring_ancestry	ancestry, struct hypagenda_item	**customAgenda);
char	*hypothesis_to_dstring(struct hypothesis	*h);
char	*hypothesis_to_dstring_from(struct hypothesis	*h, int	_from);
char	*hypothesis_to_labelled_tree_string(struct hypothesis	*h);
struct hypothesis	*cheap_hypothesis(struct edge	*e, int	with_dg);
