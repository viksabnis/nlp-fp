#ifndef	MRS_H
#define	MRS_H

#include <stdio.h>

struct mrs_var
{
	char		*name, *type;
	struct mrs_var_property
	{
		char	*name;
		char	*value;
	}			*props;
	short		nprops:15, is_const:1;
	short		refs;
	int			vnum;	// in contexts where multiple MRSes are floating around, they may share mrs_var structures.  in this case, the vnum fields will not be reliable indicators of the index of the variable in the MRS's vlist.

	union
	{
		struct dg		*dg;
		struct dbid		*dbid;
	};
	struct dg		*semi_dg;
};

struct mrs_ep
{
	char			*pred;
	struct mrs_var	*lbl;
	struct mrs_ep_role
	{
		char			*name;
		struct mrs_var	*value;
	}	*args;
	int			nargs:15;
	int			active:1;	// used in semantic lookup enumeration stage
	unsigned	epnum:16;	// so we can just pass mrs_ep's around and know their ids
	struct dg	*dg;
	int	cfrom, cto;
};

struct mrs_hcons
{
	struct mrs_var	*hi, *lo;
	enum mrs_hcons_type
	{
		hcons_qeq,
		hcons_leq,
		hcons_geq
	}	type:31;
	int active:1;
};

struct mrs_icons
{
	struct mrs_var	*left, *right;
	char	*type;
};

struct mrs_vlist
{
	int				nvars;
	struct mrs_var	**vars;
};

struct mrs
{
	struct mrs_var	*ltop, *index, *xarg;
	struct mrs_ep	*rels;
	int				nrels;
	struct mrs_hcons *hcons;
	int				nhcons;
	struct mrs_vlist vlist;
	int				nicons;
	struct mrs_icons *icons;
	char			**triggers;
	int				ntriggers;
};

void		print_mrs(struct mrs	*mrs);
void		print_mrs_var(struct mrs_var	*var);
void		print_mrs_var_props(struct mrs_var	*var);
struct mrs	*parse_mrs(char	*buffer);
char		*read_mrs_string_or_line(FILE	*f, char	*line, int	maxlen);
struct mrs	*read_mrs(FILE	*f);
int			snprint_mrs(char	*str, int	len, struct mrs	*mrs);
int	snprint_mrs_var_props(char	*str, int	len, struct mrs_var	*var);
void		free_mrs(struct mrs	*m);
struct mrs_var	*mrs_find_ep_role(struct mrs_ep	*ep, char	*role);
void		semantic_lookup(struct mrs	*mrs);
int			mrs_subsumes(struct mrs	*in, struct mrs	*out);
struct mrs	*extract_mrs(struct dg	*root);
struct mrs	*cont_to_mrs(struct dg	*cont);
int		dagify_mrs_var(struct mrs_var	*var, struct dg	*skolem);
int		dagify_mrs_ep(struct mrs_ep *ep);
struct dg	*dagify_rels_from_eps(int neps, struct mrs_ep	*eps[]);
void		*freeze_vpm();
void		recover_vpm(void *vpm);
struct mrs_var	*internal_to_external_mrs_var(struct mrs_var	*vin);
struct mrs_var	*external_to_internal_mrs_var(struct mrs_var	*vin);
char		*internal_to_external_var_type(char	*in);
char		*external_to_internal_var_type(char	*in);
struct mrs	*apply_transfer_input_vpm(struct mrs	*min);
struct mrs	*apply_transfer_output_vpm(struct mrs	*min);

char	*normalize_predicate(char	*p, char	*storage);

struct mrs_var	*dg_to_mrs_var(struct dg	*dg, struct mrs_vlist *vlist);
void	dg_to_mrs_ep(struct dg *dg, struct mrs_vlist *vlist, struct mrs_ep	*ep);

// MRS copiers
struct mrs	*copy_mrs(struct mrs	*m);
struct mrs	*slab_copy_mrs(struct mrs	*min, int share_strings);
struct mrs	*external_to_internal_mrs(struct mrs	*min);
struct mrs	*internal_to_external_mrs(struct mrs	*min);

struct mrs	*ace_surface_to_mrs(char	*line);

void	mrs_crange_for_x(struct mrs	*m, struct mrs_var	*x, int	quantified, int	*From, int	*To);

int pred_subsumes(char *in, char *out);

// transforms the ->dg links on the Eps and vars in 'm' to be semi-formatted
void	semi_reformat_mrs(struct mrs	*m, int	do_forward);

#endif
