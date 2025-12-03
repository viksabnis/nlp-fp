#ifndef	LATTICE_MAPPING_H
#define	LATTICE_MAPPING_H

#define		REGEX_FLAGS	REG_PERL
#define		UNICODE
#include	<boost/regex.h>
#include	"conf.h"

struct token;

struct lattice_edge
{
	struct lattice_vertex	*from, *to;
	struct token			*token;
	struct edge			*edge;
};

struct lattice_vertex
{
	int	id;
	int	nfollowers;
	struct lattice_edge	**followers;
	int	mark;
};

struct lattice
{
	int	lattice_vertex_id_gen;
	int				nedges;
	struct lattice_edge		**edges;
	int				nvertices;
	struct lattice_vertex	**vertices;
	struct lattice_vertex	*start, *end;
};

struct lattice_rule
{
	char	*name;
	struct dg	*dg;
	int	ncontext, ninput, noutput;
	struct lattice_regex_constraints
	{
		int	count;
		struct path	*paths;
		wchar_t	**regexs;
		regex_t	*re;
	}	*regex_constraints;
	int	nposition_constraints;
	struct lattice_position_constraint
	{
		int	lhs_what, lhs_which;
		int	rhs_what, rhs_which;
		enum	lattice_position_constraint_type {
			lpcPreceeds=1,
			lpcFollows,
			lpcImmediatelyPreceeds,
			lpcImmediatelyFollows,
			lpcCovers
		}	type;
	}	*position_constraints;
	int	jump_on_match;
};

struct lattice_rule_set
{
	int			nrules;
	struct lattice_rule	**rules;
};

void	sort_lattice(struct lattice	*tc);
int	lattice_vertex_follows(struct lattice	*tc, struct lattice_vertex	*a, struct lattice_vertex	*b);
int	load_token_mapping_rules();
struct lattice_rule_set	*freeze_lattice_rule_set(struct lattice_rule_set	*rs);
void	compile_lattice_rule_set(struct lattice_rule_set	*rs);
void	apply_post_generation_mapping_rules(struct lattice	*lat);
struct lattice	*edge_list_to_lattice(int	n, void	**list);
struct lattice	*duplicate_lexical_lattice(struct lattice	*lat);

#endif
