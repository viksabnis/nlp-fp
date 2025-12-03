#include	<stdio.h>
#include	<locale.h>
#include	<assert.h>

#include	"chart.h"
#include	"unpack.h"
#include	"mrs.h"
#include	"dag.h"
#include	"rule.h"
#include	"freeze.h"

int disable_generalization = 0;
int disable_subsumption_test = 0;
int tsdb_notes = 0;
int timeout_seconds = 0;
int	form_to_relation = 0;
int	debug_level = 0, export_parts = 0, do_itsdb = 0, do_itsdb_stdout = 0;
int show_gen_chart = 0;
char	*save_grammar_path = 0;
char	*load_grammar_path = 0;
char	*sentence_path = 0, *master_addr = 0;
int	question = 0, exhaustive = 1, lui_mode = 0, inhibit_pack = 0, best_only = 0;
int	dont_unspecialize = 0;
int show_realization_trees = 0, show_realization_mrses = 0, report_labels = 0;
int	max_chart_megabytes = 1200, max_unpack_megabytes = 1500;

int	preprocess_only = 0;
extern char mrs_line_breaks;

int g_mode = PARSING, print_trees = 1;
int	die = 0;
int input_from_lui = 0;
int preexisting_lui_fd = -1;

extern int	g_loaded, inhibit_results, trace;

void	ace_load_grammar(char	*path)
{
	setlocale(LC_ALL, "");
	setup_carcs_stack();
	init_glb_cache();
	load_frozen_grammar(path);
	setup_extra_type_dgs();
	g_loaded = 1;
}

struct mrs	*ace_surface_to_mrs(char	*line)
{
	struct mrs	*first_mrs = NULL;
	extern void	(*parse_callback)(struct hypothesis	*hyp, struct mrs	*mrs);
	void my_callback(struct hypothesis	*h, struct mrs	*m)
	{
		if(!first_mrs)
			first_mrs = copy_mrs(m);
	}
	parse_callback = my_callback;
	inhibit_results = 1;
	parse_line(line);
	parse_callback = NULL;
	return first_mrs;
}

void	linenoiseEnableRaw() {}
void	linenoiseDisableRaw() {}
