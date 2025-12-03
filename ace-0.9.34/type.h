#ifndef	_TYPE_H
#define	_TYPE_H

#include	<stdlib.h>
#include	"dag-provenance.h"

struct type_hierarchy
{
	char	*id;
	int			ntypes;
	struct type	**types;
	int			nstrings;
	struct type	**strings;
	struct type	*top, *strtype;
	struct hash	*thash;
};

struct type_hierarchy	*new_type_hierarchy(char	*id, char	*topname);
struct type_hierarchy	*default_type_hierarchy();
void					set_default_type_hierarchy(struct type_hierarchy	*th);
struct type	*th_lookup_type(struct type_hierarchy	*th, char	*name);

struct type
{
	char		*name;
	struct dg	*dg;	// indefeasible constraints
	int		ndescendents;	// this could get long-ish! :-P
	unsigned short	*descendents;	// we should probably do a bit vector

	int		tnum;	// my type number

	// immediate parents and daughters
	int			nparents, ndaughters;
	struct type	**parents, **daughters;

	struct tdl_line	*tdl;
};

struct type	*get_top();
struct type	*lookup_type(char	*name);
struct type	*add_string(char	*name);
char	*trim_string(char	*str);
int	descendent_of(int	dec, struct type	*of);
void	inval_thash();
void	setup_glb_lut();
int	add_type_only(char	*name, int	npar, struct type	**par, int	overwrite);
void	number_strings();
int		load_types();
int	constrain_type(char	*name, struct dg	*dg, struct tdl_line	*tdl);
int	wellform(struct dg	*d, char	*typename);
void	print_glb_stats();
struct type	*temporary_string_type(char *string);
struct dg	*type_dg(char		*name);
struct dg	*atomic_top();

struct type	*most_general_type_for_feat(struct type_hierarchy	*th, int	feat);
struct type	*most_general_type_for_dg(struct dg	*d);

int make_glbs();

void recover_typehash(void *frozen);
void *freeze_typehash();

struct type	*glb(struct type	*a, struct type	*b);
struct type	*lub(struct type	*a, struct type	*b);

struct dg	*find_instance(char	*name);
char	*type_to_string(struct type	*ty);
struct type	*string_to_type(char	*str);

#endif
