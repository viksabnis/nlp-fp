#ifndef	CONF_H
#define	CONF_H

struct path
{
	int		count;
	int		*fnums;
};

struct path	freeze_path(struct path	p);

extern struct path	lex_stem_path, lex_rels_path, rule_rels_path, extract_mrs_path, lex_carg_path, lex_pred_path;
extern char			*semarg_type;
extern char			*g_cons_type;
extern char			*g_list_type;
extern char			*g_null_type;
extern char			*g_diff_list_type;
extern char			*top_type;
extern char			*semi_top_type;

extern char			*handle_type;

extern int instloc_feature;

extern struct path	*chart_dependencies_from, *chart_dependencies_to;
extern int			nchart_dependencies;

extern int			enable_token_avms;
extern int			enable_simple_form_lexicon;
extern int			enable_index_accessibility_filtering;
extern int			extra_erg_dag_stash;
extern int			enable_post;

extern int			ortho_max_rules, ortho_warn_max_rules;
extern int			freezer_megabytes;

extern int			reduce_chart_before_lexical_parsing;
extern int			enable_post_generation_mapping;

extern char			*token_type;
extern struct path	token_form_path, token_from_path, token_to_path, token_id_path, token_postags_path, token_posprobs_path;
extern struct path	lex_tokens_list_path, lex_tokens_last_path;

extern struct path	lattice_mapping_input_path, lattice_mapping_output_path, lattice_mapping_context_path, lattice_mapping_position_path;

extern int	mrs_enable_icons;
extern int	icons_left_feature, icons_right_feature;

extern struct path	rels_list_path, hcons_list_path, icons_list_path, hook_path;
extern struct path	recursive_label_path_in_sign, recursive_label_path_in_label;
extern struct path	label_path;

struct path	robustness_marker_path;
char		*robustness_marker_type;

struct dg	*dg_path(struct dg	*dg, struct path	p);
struct dg	*dg_path_add(struct dg	*dg, struct path	p, struct dg	*add);
int			pathcmp(const struct path	*p1, const struct path	*p2);
void		print_path(struct path	p);
struct path	make_path(int count, ...);
struct path	string_to_path(char	*str);
struct path	pathdup(struct path	p);
void iterate_conf_list(char	*key, int	(*callback)(char	*word));
void	load_chart_dependencies(char	*depstring);
struct path slab_string_to_path(char	*str);

int	safe_snprintf(char	*str, int	len, char	*fmt, ...);

#endif
