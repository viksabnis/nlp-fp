#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<stdarg.h>

#include	"dag.h"
#include	"conf.h"
#include	"rule.h"
#include	"chart.h"
#include	"freeze.h"
#include	"tdl.h"

int	g_transfer = 0;

struct path	lex_stem_path, lex_rels_path, rule_rels_path, extract_mrs_path, lex_carg_path, lex_pred_path;
char		*semarg_type;
char		*handle_type;
char		*g_cons_type;
char		*g_list_type;
char		*g_null_type;
char		*g_diff_list_type;

char	*top_type;
char	*semi_top_type;

char	*transfer_input_relation_prefix;

struct path	*chart_dependencies_from, *chart_dependencies_to;
int			nchart_dependencies;
int			reduce_chart_before_lexical_parsing;

int enable_post = 0;
int instloc_feature = -1;
int			enable_post_generation_mapping = 0;

int	mrs_enable_icons = 0;
int	icons_left_feature = -1, icons_right_feature = -1;

struct path	token_form_path, token_from_path, token_to_path, token_id_path, token_postags_path, token_posprobs_path;
struct path	lex_tokens_list_path, lex_tokens_last_path;
struct path	lattice_mapping_input_path, lattice_mapping_output_path, lattice_mapping_context_path, lattice_mapping_position_path;

struct path	rels_list_path, hcons_list_path, icons_list_path, hook_path;

struct path	robustness_marker_path;
char		*robustness_marker_type;

char		*token_type;

int			ortho_max_rules = 7;
int			ortho_warn_max_rules = 1;
extern int invent_ltop;
extern int g_normalize_predicates;
extern int g_generics_overwrite_orth;
char		*top_hcons_type = NULL;

// options configured but not saved in the freezer:
struct path	label_path;
int			freezer_megabytes = 256;

struct path	recursive_label_path_in_sign, recursive_label_path_in_label;

extern int	transfer_enable_qeq_bridge;

struct dg	*dg_path(struct dg	*dg, struct path	p)
{
	int i;

	for(i=0;i<p.count;i++)
		if(dg)dg = dg_hop(dg, p.fnums[i]);
	return dg;
}

struct dg	*dg_path_add(struct dg	*dg, struct path	p, struct dg	*add)
{
	return add_dg_path(dg, p.fnums, p.count, add);
}

void print_path(struct path	p)
{
	extern char	**fnames;
	int 		i;

	for(i=0;i<p.count;i++)
		printf("%s%s", (i==0)?"":" ", fnames[p.fnums[i]]);
}

int			pathcmp(const struct path	*p1, const struct path	*p2)
{
	if(p1->count != p2->count)return p1->count - p2->count;
	return memcmp(p1->fnums, p2->fnums, sizeof(int)*p1->count);
}

struct path	pathdup(struct path	q)
{
	struct path p;
	p.count = q.count;
	p.fnums = malloc(sizeof(int)*p.count);
	memcpy(p.fnums, q.fnums, sizeof(int)*p.count);
	return p;
}

struct path	make_path(int count, ...)
{
	struct path	p;
	va_list	va;
	int		i;

	va_start(va, count);
	p.count = count;
	p.fnums = malloc(sizeof(int)*count);
	for(i=0;i<count;i++)
		p.fnums[i] = lookup_fname(va_arg(va, char*));
	va_end(va);

	return p;
}

struct path slab_string_to_path(char	*str)
{
	struct path	p;

	p.count = 0;
	p.fnums = NULL;

	for(str = strtok(freeze_string(str), " \t");str;str = strtok(NULL, " \t"))
	{
		p.count++;
		p.fnums = slab_realloc(p.fnums, sizeof(int)*(p.count-1), sizeof(int) * p.count);
		p.fnums[p.count-1] = lookup_fname(str);
	}
	return p;
}

struct path	string_to_path(char	*str)
{
	struct path	p;

	p.count = 0;
	p.fnums = NULL;

	str = strdup(str);
	for(str = strtok(str, " \t");str;str = strtok(NULL, " \t"))
	{
		p.count++;
		p.fnums = realloc(p.fnums, sizeof(int) * p.count);
		p.fnums[p.count-1] = lookup_fname(str);
	}
	free(str);
	return p;
}

static struct path try_get_conf_path(char	*lhs, char	*deflt)
{
	char		*str = get_conf(lhs);
	if(!str)return string_to_path(deflt);
	else return string_to_path(str);
}

static struct path get_conf_path(char	*lhs)
{
	char		*str = get_conf(lhs);
	if(!str)
	{
		fprintf(stderr, "avm path `%s' not specified in configuration!\n", lhs);
		exit(-1);
	}
	return string_to_path(str);
}

struct conf
{
	int	transfer;

	char		*top_type, *semi_top_type;
	char		*semarg_type;
	char		*handle_type;
	char		*cons_type;
	char		*list_type;
	char		*null_type;
	char		*diff_list_type;
	struct path	lex_stem_path;
	struct path	lex_rels_path;
	struct path	lex_carg_path;
	struct path	lex_pred_path;
	struct path	rule_rels_path;
	struct path	extract_mrs_path;
	int	invent_ltop;
	char	*top_hcons_type;
	int	instloc_feature;

	struct path	*chart_dependencies_to, *chart_dependencies_from;
	int			nchart_dependencies;
	int			reduce_chart_before_lexical_parsing;

	char	*token_type;
	struct path	token_form_path, token_from_path, token_to_path,
		token_id_path, token_postags_path, token_posprobs_path;
	struct path	lex_tokens_list_path, lex_tokens_last_path;
	struct path	lattice_mapping_input_path, lattice_mapping_output_path, lattice_mapping_context_path, lattice_mapping_position_path;

	char	*deleted_daughters;
	char	*parsing_packing;
	char	*generating_packing;
	char	*ep_drop;
	int		restrictor_size;

	int		enable_token_avms;
	int		enable_simple_form_lexicon;
	int		enable_index_accessibility_filtering;
	int		enable_post;
	int		enable_generalize_edge_top_types;
	int		extra_erg_dag_stash;

	int		ortho_max_rules, ortho_warn_max_rules;

	int	mrs_enable_icons, icons_left_feature, icons_right_feature;
	struct path	rels_list_path, hcons_list_path, icons_list_path, hook_path;
	int		enable_post_generation_mapping;
	struct path	recursive_label_path_in_sign,
				recursive_label_path_in_label;

	char	*transfer_input_relation_prefix;
	int		transfer_enable_qeq_bridge;

	int	normalize_predicates;
	int	generics_overwrite_orth;

	struct path	robustness_marker_path;
	char		*robustness_marker_type;
};

struct path	freeze_path(struct path	p)
{
	p.fnums = freeze_block(p.fnums, sizeof(int)*p.count);
	return p;
}

extern int reload_restrictors, restrictor_size, nfnames;
extern char	*deleted_daughters, *parsing_packing, *generating_packing, *ep_drop;

void	*freeze_conf()
{
	struct conf	*c = slab_alloc(sizeof(*c));
	c->transfer = g_transfer;
	c->instloc_feature = instloc_feature;
	c->top_type = freeze_string(top_type);
	c->semi_top_type = freeze_string(semi_top_type);
	c->semarg_type = freeze_string(semarg_type);
	c->handle_type = freeze_string(handle_type);
	c->cons_type = freeze_string(g_cons_type);
	c->list_type = freeze_string(g_list_type);
	c->null_type = freeze_string(g_null_type);
	c->diff_list_type = freeze_string(g_diff_list_type);
	c->invent_ltop = invent_ltop;
	c->top_hcons_type = freeze_string(top_hcons_type);

	c->hook_path = freeze_path(hook_path);
	c->rels_list_path = freeze_path(rels_list_path);
	c->hcons_list_path = freeze_path(hcons_list_path);
	c->icons_list_path = freeze_path(icons_list_path);
	c->icons_left_feature = icons_left_feature;
	c->icons_right_feature = icons_right_feature;
	c->mrs_enable_icons = mrs_enable_icons;

	c->deleted_daughters = freeze_block(deleted_daughters, restrictor_size);
	c->parsing_packing = freeze_block(parsing_packing, restrictor_size);
	c->generating_packing = freeze_block(generating_packing, restrictor_size);
	c->restrictor_size = restrictor_size;
	c->ep_drop = freeze_block(ep_drop, restrictor_size);
	c->transfer_enable_qeq_bridge = transfer_enable_qeq_bridge;
	c->normalize_predicates = g_normalize_predicates;
	c->generics_overwrite_orth = g_generics_overwrite_orth;

	if(!g_transfer)
	{
		c->lex_stem_path = freeze_path(lex_stem_path);
		c->lex_rels_path = freeze_path(lex_rels_path);
		c->lex_carg_path = freeze_path(lex_carg_path);
		c->lex_pred_path = freeze_path(lex_pred_path);
		c->rule_rels_path = freeze_path(rule_rels_path);
		c->extract_mrs_path = freeze_path(extract_mrs_path);
		c->lex_tokens_list_path = freeze_path(lex_tokens_list_path);
		c->lex_tokens_last_path = freeze_path(lex_tokens_last_path);
		c->token_form_path = freeze_path(token_form_path);
		c->token_from_path = freeze_path(token_from_path);
		c->token_to_path = freeze_path(token_to_path);
		c->token_id_path = freeze_path(token_id_path);
		c->token_postags_path = freeze_path(token_postags_path);
		c->token_posprobs_path = freeze_path(token_posprobs_path);
		c->token_type = freeze_string(token_type);

		c->lattice_mapping_input_path = freeze_path(lattice_mapping_input_path);
		c->lattice_mapping_output_path = freeze_path(lattice_mapping_output_path);
		c->lattice_mapping_context_path = freeze_path(lattice_mapping_context_path);
		c->lattice_mapping_position_path = freeze_path(lattice_mapping_position_path);

		int i;
		for(i=0;i<nchart_dependencies;i++)
		{
			chart_dependencies_from[i] = freeze_path(chart_dependencies_from[i]);
			chart_dependencies_to[i] = freeze_path(chart_dependencies_to[i]);
		}
		c->chart_dependencies_from = freeze_block(chart_dependencies_from, sizeof(struct path)*nchart_dependencies);
		c->chart_dependencies_to = freeze_block(chart_dependencies_to, sizeof(struct path)*nchart_dependencies);
		c->nchart_dependencies = nchart_dependencies;
		c->reduce_chart_before_lexical_parsing = reduce_chart_before_lexical_parsing;

		c->enable_token_avms = enable_token_avms;
		c->enable_simple_form_lexicon = enable_simple_form_lexicon;
		c->enable_index_accessibility_filtering = enable_index_accessibility_filtering;
		c->enable_generalize_edge_top_types = enable_generalize_edge_top_types;
		c->enable_post = enable_post;
		c->enable_post_generation_mapping = enable_post_generation_mapping;
		c->extra_erg_dag_stash = extra_erg_dag_stash;

		c->ortho_max_rules = ortho_max_rules;
		c->ortho_warn_max_rules = ortho_warn_max_rules;
		c->recursive_label_path_in_label = freeze_path(recursive_label_path_in_label);
		c->recursive_label_path_in_sign = freeze_path(recursive_label_path_in_sign);
		c->robustness_marker_path = freeze_path(robustness_marker_path);
		c->robustness_marker_type = freeze_string(robustness_marker_type);
	}
	else
	{
		c->transfer_input_relation_prefix = freeze_string(transfer_input_relation_prefix);
	}

	return c;
}

void	recover_conf(void	*vc)
{
	struct conf	*c = vc;
	g_transfer = c->transfer;
	top_type = c->top_type;
	instloc_feature = c->instloc_feature;
	semi_top_type = c->semi_top_type;
	semarg_type = c->semarg_type;
	handle_type = c->handle_type;
	g_cons_type = c->cons_type;
	g_list_type = c->list_type;
	g_null_type = c->null_type;
	g_diff_list_type = c->diff_list_type;
	invent_ltop = c->invent_ltop;
	top_hcons_type = c->top_hcons_type;

	hook_path = c->hook_path;
	rels_list_path = c->rels_list_path;
	hcons_list_path = c->hcons_list_path;
	icons_list_path = c->icons_list_path;
	icons_left_feature = c->icons_left_feature;
	icons_right_feature = c->icons_right_feature;
	mrs_enable_icons = c->mrs_enable_icons;

	deleted_daughters = c->deleted_daughters;
	parsing_packing = c->parsing_packing;
	generating_packing = c->generating_packing;
	restrictor_size = c->restrictor_size;
	ep_drop = c->ep_drop;
	reload_restrictors = (restrictor_size != nfnames);
	transfer_enable_qeq_bridge = c->transfer_enable_qeq_bridge;
	g_normalize_predicates = c->normalize_predicates;
	g_generics_overwrite_orth = c->generics_overwrite_orth;

	if(!g_transfer)
	{
		lex_stem_path = c->lex_stem_path;
		lex_rels_path = c->lex_rels_path;
		lex_carg_path = c->lex_carg_path;
		lex_pred_path = c->lex_pred_path;
		rule_rels_path = c->rule_rels_path;
		extract_mrs_path = c->extract_mrs_path;

		nchart_dependencies = c->nchart_dependencies;
		chart_dependencies_from = c->chart_dependencies_from;
		chart_dependencies_to = c->chart_dependencies_to;
		reduce_chart_before_lexical_parsing = c->reduce_chart_before_lexical_parsing;

		lex_tokens_list_path = c->lex_tokens_list_path;
		lex_tokens_last_path = c->lex_tokens_last_path;
		token_form_path = c->token_form_path;
		token_from_path = c->token_from_path;
		token_to_path = c->token_to_path;
		token_id_path = c->token_id_path;
		token_postags_path = c->token_postags_path;
		token_posprobs_path = c->token_posprobs_path;
		token_type = c->token_type;

		lattice_mapping_position_path = c->lattice_mapping_position_path;
		lattice_mapping_input_path = c->lattice_mapping_input_path;
		lattice_mapping_output_path = c->lattice_mapping_output_path;
		lattice_mapping_context_path = c->lattice_mapping_context_path;

		enable_token_avms = c->enable_token_avms;
		enable_simple_form_lexicon = c->enable_simple_form_lexicon;
		enable_index_accessibility_filtering = c->enable_index_accessibility_filtering;
		enable_generalize_edge_top_types = c->enable_generalize_edge_top_types;
		enable_post = c->enable_post;
		enable_post_generation_mapping = c->enable_post_generation_mapping;
		extra_erg_dag_stash = c->extra_erg_dag_stash;

		ortho_max_rules = c->ortho_max_rules;
		ortho_warn_max_rules = c->ortho_warn_max_rules;
		recursive_label_path_in_label = c->recursive_label_path_in_label;
		recursive_label_path_in_sign = c->recursive_label_path_in_sign;

		robustness_marker_path = c->robustness_marker_path;
		robustness_marker_type = c->robustness_marker_type;
	}
	else
	{
		transfer_input_relation_prefix = c->transfer_input_relation_prefix;
	}
}

int	get_conf_int(char	*name, int dflt)
{
	char	*str = get_conf(name);
	if(!str)return dflt;
	return atoi(str);
}

int	get_conf_bool(char	*name, int dflt)
{
	char	*str = get_conf(name);
	if(!str)return dflt;
	if(!strcasecmp(str, "enabled"))return 1;
	if(!strcasecmp(str, "on"))return 1;
	if(!strcasecmp(str, "yes"))return 1;
	if(!strcasecmp(str, "true"))return 1;
	if(!strcasecmp(str, "t"))return 1;
	return 0;
}

load_transfer_conf()
{
	transfer_input_relation_prefix = get_conf_unq("input-relation-prefix");
}

load_syntax_conf()
{
	lex_stem_path = get_conf_path("orth-path");
	lex_rels_path = get_conf_path("lex-rels-path");
	lex_carg_path = get_conf_path("lex-carg-path");
	lex_pred_path = get_conf_path("lex-pred-path");
	rule_rels_path = get_conf_path("rule-rels-path");
	extract_mrs_path = get_conf_path("semantics-path");
	label_path = try_get_conf_path("label-path", "LNAME");
	recursive_label_path_in_label = try_get_conf_path("recursive-label-path-in-label", "SYNSEM LOCAL");
	recursive_label_path_in_sign = try_get_conf_path("recursive-label-path-in-sign", "SYNSEM NONLOC SLASH LIST FIRST");

	load_chart_dependencies(get_conf("chart-dependencies"));
	reduce_chart_before_lexical_parsing = get_conf_bool("process-chart-dependencies-before-lexical-parsing", 0);

	enable_token_avms = get_conf_bool("token-mapping", 0);
	if(enable_token_avms)
	{
		lex_tokens_list_path = get_conf_path("lexicon-tokens-path");
		lex_tokens_last_path = get_conf_path("lexicon-last-token-path");
		token_form_path = get_conf_path("token-form-path");
		token_from_path = get_conf_path("token-from-path");
		token_to_path = get_conf_path("token-to-path");
		token_id_path = get_conf_path("token-id-path");
		token_postags_path = get_conf_path("token-postags-path");
		token_posprobs_path = get_conf_path("token-posprobs-path");
		token_type = get_conf("token-type")?:"token";
	}

	lattice_mapping_input_path = try_get_conf_path("lattice-mapping-input-path", "+INPUT");
	lattice_mapping_output_path = try_get_conf_path("lattice-mapping-output-path", "+OUTPUT");
	lattice_mapping_context_path = try_get_conf_path("lattice-mapping-context-path", "+CONTEXT");
	lattice_mapping_position_path = try_get_conf_path("lattice-mapping-position-path", "+POSITION");

	enable_simple_form_lexicon = get_conf_bool("simplify-lexicon", 0);
	enable_index_accessibility_filtering = get_conf_bool("index-accessibility-filtering", 0);
	enable_generalize_edge_top_types = get_conf_bool("generalize-edge-top-types", 0);
	enable_post = get_conf_bool("english-pos-tagger", 0);
	extra_erg_dag_stash = get_conf_bool("extra-erg-dag-stash", 0);

	ortho_max_rules = get_conf_int("ortho-max-rules", 7);
	ortho_warn_max_rules = get_conf_bool("ortho-warn-on-max-rules", 1);

	robustness_marker_path = try_get_conf_path("robustness-marker-path", "");
	robustness_marker_type = get_conf("robustness-marker-type");
}

int	load_conf()
{
	g_transfer = get_conf_bool("transfer", 0);
	if(g_transfer)load_transfer_conf();
	else load_syntax_conf();

	freezer_megabytes = get_conf_int("freezer-megabytes", 256);

	top_type = get_conf("top-type")?:"*top*";
	instloc_feature = lookup_fname(get_conf("skolem-feature")?:"INSTLOC");
	semi_top_type = get_conf("semantic-interface-top-type")?:"top";
	semarg_type = get_conf("semarg-type")?:"semarg";
	handle_type = get_conf("handle-type")?:"h";
	g_cons_type = get_conf("cons-type")?:"cons";
	g_list_type = get_conf("list-type")?:"list";
	g_null_type = get_conf("null-type")?:"null";
	g_diff_list_type = get_conf("diff-list-type")?:"diff-list";

	invent_ltop = get_conf_bool("invent-ltop", 1);	// msg-less grammars tend to want their TOP to be floating
	top_hcons_type = get_conf("top-hcons-type")?:"qeq";	// what sort of hcons should be introduced between the TOP and the LTOP?
	if(!strcasecmp(top_hcons_type, "qeq")){}
	else if(!strcasecmp(top_hcons_type, "leq")){}
	else
	{
		fprintf(stderr, "unknown value `%s' for parameter `top-hcons-type'\n", top_hcons_type);
		fprintf(stderr, "defaulting to `none'; known values are `qeq', `leq', and `none'.\n");
		top_hcons_type = "none";
	}

	hook_path = try_get_conf_path("hook-path", "HOOK");
	rels_list_path = try_get_conf_path("mrs-rels-list", "RELS LIST");
	hcons_list_path = try_get_conf_path("mrs-hcons-list", "HCONS LIST");

	mrs_enable_icons = get_conf_bool("enable-icons", 0);
	if(mrs_enable_icons)
	{
		icons_list_path = try_get_conf_path("mrs-icons-list", "ICONS LIST");
		icons_left_feature = lookup_fname(get_conf("icons-left")?:"IC-LEFT");
		icons_right_feature = lookup_fname(get_conf("icons-right")?:"IC-RIGHT");
	}

	transfer_enable_qeq_bridge = get_conf_bool("transfer-qeq-bridge", 1);

	g_generics_overwrite_orth = get_conf_bool("generics-overwrite-orth", 0);

	recover_conf(freeze_conf());
}

int check_conf_list(char	*key, char	*word)
{
	char	*list = get_conf(key), *p;
	if(!list)return 0;
	list = strdup(list);
	for(p=strtok(list, " \t\n");p;p=strtok(0, " \t\n"))
		if(!strcasecmp(word,p))break;
	free(list);
	return p?1:0;
}

void iterate_conf_list(char	*key, int	(*callback)(char	*word))
{
	int	hits = 0;
	char	*list = get_conf(key), *p, *saveptr=NULL;
	if(!list)return;
	list = strdup(list);
	for(p=strtok_r(list, " \t\n", &saveptr);p;p=strtok_r(NULL, " \t\n", &saveptr))
		if(callback(p))break;
	free(list);
}

void	configure_rule(struct rule	*r)
{
	r->gen_ignore = 0;
	if(temporary_expedient(r->name)) r->gen_ignore = 1;
	else add_semantic_index((struct lexeme*)r, r->dg, 1);

	r->span_only = check_conf_list("spanning-only-rules", r->name);
	r->frag_only = check_conf_list("fragment-only-rules", r->name);
	r->hyper = check_conf_list("hyper-active-rules", r->name);
	r->pad = 0;
}

void	load_chart_dependencies(char	*depstring)
{
	char	*strings[1024];
	int		nstrings = 0;

	if(!depstring)return;

	depstring = trim_string(depstring);
	while(depstring && *depstring)
	{
		char	*str = depstring;
		if(*str != '"')
		{
			fprintf(stderr, "chart-dependencies parameter must be a list of path-strings\n");
			exit(-1);
		}
		depstring = strchr(str+1, '"');
		if(!depstring)
		{
			fprintf(stderr, "chart-dependencies parameter had mismatched quotes\n");
			exit(-1);
		}
		*depstring = 0;
		depstring = trim_string(depstring+1);
		strings[nstrings++] = trim_string(str+1);
	}

	if(nstrings % 2 != 0)
	{
		fprintf(stderr, "chart-dependencies parameter paths must be in pairs\n");
		exit(-1);
	}

	nchart_dependencies = nstrings/2;
	chart_dependencies_from = malloc(sizeof(struct path)*nchart_dependencies);
	chart_dependencies_to = malloc(sizeof(struct path)*nchart_dependencies);
	int	i;
	for(i=0;i<nchart_dependencies;i++)
	{
		chart_dependencies_from[i] = string_to_path(strings[2*i + 0]);
		chart_dependencies_to[i] = string_to_path(strings[2*i + 1]);
		/*printf("chart dep:  ");
		print_path(chart_dependencies_from[i]);
		printf(" => ");
		print_path(chart_dependencies_to[i]);
		printf("\n");*/
	}
}
