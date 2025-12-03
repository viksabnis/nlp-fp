#include	<stdio.h>
#include	<errno.h>
#include	<stdarg.h>
#include	<signal.h>
#include	<sys/time.h>
#include	<getopt.h>
#include	<unistd.h>
#include	<string.h>
#include	<ctype.h>
#include	<locale.h>
#include	<sys/fcntl.h>
#include	"chart.h"
#include	"net.h"
#include	"freeze.h"
#include	"conf.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"mrs.h"
#include	"transfer.h"
#include	"version.h"
#include	"tnt.h"

#include	"timeout.h"
#include	"timer.h"
#include	"profiler.h"
#include	"timeout.h"

#include	"linenoise.h"

int	debug_level = 0, export_parts = 0, do_itsdb = 0, do_itsdb_stdout = 0;
extern int itsdb_dump_chart;
extern int	show_probability;
extern int	enable_dublin;
extern int	derivations_include_roots;
extern int	format_udx;
char	*save_grammar_path = 0;
char	*load_grammar_path = 0;
char	*sentence_path = 0, *master_addr = 0;
int	question = 0, exhaustive = 1, lui_mode = 0, inhibit_pack = 0, best_only = 0;
int show_gen_chart = 0;
int timeout_seconds = 0;
extern int	enable_ubertagging;
extern double	ubertagging_threshold;

int	disable_generalization = 0;

int	dont_unspecialize = 0;

int	output_edge_vectors = 0;
char	*generation_server_lang = NULL;

int	preprocess_only = 0;
extern char mrs_line_breaks;

int g_mode = PARSING, print_trees = 1;
int	die = 0;

extern int enable_tnt;
char	*tnt_model_path = NULL;
int		tnt_max_tags = 2;

extern int	g_loaded, inhibit_results, trace;
extern int yy_mode;
extern int do_improve_characterization;
extern long long	accum_ram_usage;
extern char			*use_roots, *disable_signs;
extern int do_forest;
extern int g_profiling;
extern int use_packed_edge_ids;
extern int give_up_threshold;
extern int gen_qc;
float	stdin_time = 0;

int	form_to_relation = 0;
int	show_realization_trees = 0;
int	show_realization_mrses = 0;
int	disable_subsumption_test = 0;
int report_labels = 0;
extern int equivalence_packing_only;

extern char	*transfer_config_path;

int	max_chart_megabytes = 1200, max_unpack_megabytes = 1500;
int preexisting_lui_fd = -1;
int input_from_lui = 0;

int	tsdb_notes = 0;	// if 1, print NOTEs with `parse' relation data and `run' relation data
extern int	yy_rule_mode;

extern float timer();

int	parse_line(char	*line);
extern char	*csaw_grammar_path;

char	*override_maxent_path = NULL;

FILE	*open_sentence_source()
{
	FILE	*fin;
	assert(sentence_path != 0);
	if(!strcmp(sentence_path, "-"))
	{
		if(master_addr && strcmp(master_addr, "-"))
			connect_to_master(master_addr);
		fin = stdin;
	}
	else
	{
		assert(master_addr == 0 || !sentence_path);
		fin = fopen(sentence_path, "r");
	}
	if(!fin) { perror(sentence_path); exit(-1); }
	return fin;
}

void broken_pipe_handler(int sig) { cancel_task = die = 1; }

void	setup_signal_handlers()
{
	signal(SIGSEGV, print_current_sentence);
	signal(SIGBUS, print_current_sentence);
	signal(SIGPIPE, broken_pipe_handler);
}

void	parse_args(int	argc, char	*argv[])
{
	char	*prog = argv[0], *tla;
	extern int nofragments;
	unsigned char ch;

	tla = prog + strlen(prog) - 3;
	if(tla >= prog)
	{
		if(!strcmp(tla, "ape"))g_mode = PARSING;
		if(!strcmp(tla, "age"))g_mode = GENERATING;
	}

	struct option long_options[] = {
		{"disable-generalization", 0, &disable_generalization, 1},
		{"disable-subsumption-test", 0, &disable_subsumption_test, 1},
		{"show-realization-trees", 0, &show_realization_trees, 1},
		{"show-realization-mrses", 0, &show_realization_mrses, 1},
		{"show-probability", 0, &show_probability, 1},
		{"equivalence-packing", 0, &equivalence_packing_only, 1},
		{"packed-edge-ids", 0, &use_packed_edge_ids, 1},
		{"itsdb-forest", 0, &itsdb_dump_chart, 1},
		{"report-labels", 0, &report_labels, 1},
		{"input-from-lui", 0, &input_from_lui, 1},
		{"show-gen-chart", 0, &show_gen_chart, 1},
		{"yy-rules", 0, &yy_rule_mode, 1},
		{"tsdb-notes", 0, &tsdb_notes, 1},
		{"rooted-derivations", 0, &derivations_include_roots, 1},
#define	MAX_UNPACK_MEGABYTES_OPTION	1000
		{"max-unpack-megabytes", 1, NULL, MAX_UNPACK_MEGABYTES_OPTION},
#define	MAX_CHART_MEGABYTES_OPTION	1001
		{"max-chart-megabytes", 1, NULL, MAX_CHART_MEGABYTES_OPTION},
#define GENERATION_SERVER_OPTION	1002
		{"generation-server", 1, NULL, GENERATION_SERVER_OPTION},
#define LUI_FD_OPTION			1003
		{"lui-fd", 1, NULL, LUI_FD_OPTION},
#define	TNT_MODEL_OPTION		1004
#define	TNT_MAX_TAGS_OPTION		1005
		{"tnt-model", 1, NULL, TNT_MODEL_OPTION},
		{"tnt-max-tags", 1, NULL, TNT_MAX_TAGS_OPTION},
#define	TIMEOUT_OPTION			1006
		{"timeout", 1, NULL, TIMEOUT_OPTION},
#define	TRANSFER_CONFIG_OPTION	1007
		{"transfer-config", 1, NULL, TRANSFER_CONFIG_OPTION},
#define	UBERTAG_OPTION			1008
		{"ubertagging", 2,NULL, UBERTAG_OPTION},
		{"uebertagging", 2,NULL, UBERTAG_OPTION},
		{"übertagging", 2,NULL, UBERTAG_OPTION},
#define	DUBLIN_OPTION	1009
		{"pcfg", 2, NULL, DUBLIN_OPTION},
#define	MAXENT_OPTION	1010
		{"maxent", 2, NULL, MAXENT_OPTION},
#define	LICENSE_INFO_OPTION		1011
		{"license-info", 0, NULL, LICENSE_INFO_OPTION},
#define GIVE_UP_THRESHOLD_OPTION	1012
		{"max-words", 1, NULL, GIVE_UP_THRESHOLD_OPTION},
#define	TSDB_STDOUT_OPTION	1013
		{"tsdb-stdout", 0, NULL, TSDB_STDOUT_OPTION},
#define	UDX_OPTION			1014
		{"udx", 2,NULL, UDX_OPTION},
		{"gen-qc", 0,&gen_qc, 1},
		{"improve-characterization", 0,&do_improve_characterization, 1},
		{NULL,0,NULL,0}
		};

#define	REQUIRE_POSITIVE(option)	do { if(atoi(optarg)<1) { \
									fprintf(stderr, "ERROR: option %s requires a positive integer\n", option); \
									exit(-1); } } while(0);

	int	gorv;
	while(1)
	{
		gorv = getopt_long(argc, argv, "VhvpfEPL:lXg:G:m:qtTRe1n:r:jFOsiy", long_options, NULL);
		if(gorv == -1)break;
		switch(gorv) {
		case	'V':	printf("ACE version %s\n", ACE_VERSION);
						printf("compiled at " __TIME__ " on "  __DATE__ "\n");
						exit(0);
		case	'h':	usage: printf("usage: %s [-1 | -n COUNT] [-R] [-f] [-e] [-g grammar-to-load] [-G grammar-to-save] [sentences-file] [--license-info] \n", prog); exit(0);
		case	'v':	if(debug_level)trace++; debug_level++;	break;
		case	'y':	yy_mode = 1; break;
		case	'g':	load_grammar_path = optarg;	break;
		case	'G':	save_grammar_path = optarg;	break;
		case	'O':	do_forest++;	break;
		case	'E':	preprocess_only = 1;		break;
		case	'P':	export_parts = 1;		break;
		case	'm':	master_addr = optarg;	break;
		case	'q':	question = 1;			break;
		case	'X':	exhaustive = 0;			break;
		case	'1':	best_only = 1;			break;
		case	'n':	best_only = atoi(optarg);	REQUIRE_POSITIVE("-n"); break;
		case	'r':	use_roots = optarg;	if(strstr(use_roots, "root_frag"))nofragments = 0;	break;
		case	'l':	lui_mode = 1;			break;
		case	'f':	mrs_line_breaks = '\n';		break;
		case	'p':	inhibit_pack = 1;		break;
		case	'R':	inhibit_results = 1;		break;
		case	't':	do_itsdb = 1;			break;
		case	'T':	print_trees = 0;		break;
		case	'e':	g_mode = GENERATING;	break;
		case	'L':	disable_signs = optarg;	break;
		case	'j':	output_edge_vectors = 1;	break;
		case	'F':	form_to_relation = 1;	break;
		case	's':	dont_unspecialize = 1;	break;
		case	'i':	g_profiling = 1;		break;
		case	'?':	goto usage;

		case	MAX_UNPACK_MEGABYTES_OPTION:	max_unpack_megabytes = atoi(optarg);	REQUIRE_POSITIVE("--max-unpack-megabytes"); break;
		case	MAX_CHART_MEGABYTES_OPTION:		max_chart_megabytes = atoi(optarg);		REQUIRE_POSITIVE("--max-chart-megabytes"); break;
		case	GENERATION_SERVER_OPTION:	generation_server_lang = optarg;	break;
		case	LUI_FD_OPTION:	preexisting_lui_fd = atoi(optarg);	REQUIRE_POSITIVE("--lui-fd"); break;
		case	GIVE_UP_THRESHOLD_OPTION:	give_up_threshold = atoi(optarg)+1; REQUIRE_POSITIVE("--max-words"); break;
		case	TNT_MODEL_OPTION:	enable_tnt = 1; tnt_model_path = optarg; break;
		case	TNT_MAX_TAGS_OPTION: tnt_max_tags = atoi(optarg); REQUIRE_POSITIVE("--tnt-max-tags"); break;
		case	TIMEOUT_OPTION: timeout_seconds = atoi(optarg); REQUIRE_POSITIVE("--timeout"); break;
		case	TRANSFER_CONFIG_OPTION: transfer_config_path = optarg; break;
		case	TSDB_STDOUT_OPTION: do_itsdb = do_itsdb_stdout = tsdb_notes = 1; { extern char* mrs_end; mrs_end = ""; } break;
		case	UBERTAG_OPTION:
			if(optarg)ubertagging_threshold = atof(optarg);
			if(ubertagging_threshold<=0 || ubertagging_threshold >1)
			{
				fprintf(stderr, "ERROR: übertagging threshold must be greater than 0 and not more than 1\n");
				exit(-1);
			}
			enable_ubertagging = 1;
			break;
		case	DUBLIN_OPTION: csaw_grammar_path = optarg; enable_dublin = 1; break;
		case	MAXENT_OPTION: override_maxent_path = optarg; break;
		case	UDX_OPTION:
			if(optarg && !strcasecmp(optarg, "all"))format_udx = 2;
			else format_udx = 1;
			break;
		case	LICENSE_INFO_OPTION: show_long_license_info(); break;
		case	0:	continue;	// auto-handled long option
	} }
	if(optind<argc-1)goto usage;
	if(!load_grammar_path)goto usage;
	if(optind<argc)sentence_path = argv[optind];
	else if(!save_grammar_path)sentence_path = "-";
	if(generation_server_lang)
		g_mode = GENERATING;
	if(enable_tnt)assert(0 == tnt_init(tnt_model_path, tnt_max_tags));

	if(do_itsdb_stdout)
	{
		extern int tsdb_maxderivations, tsdb_maxanalyses;
		tsdb_maxderivations = tsdb_maxanalyses = best_only;
	}
}

struct job_stats
{
	int			success, fail, count;
	long long	ram;
	float		time;
};

show_hierarchy(char	*type)
{
	struct type	*t = lookup_type(type);
	if(!t) { printf("no such type '%s'\n", type); return -1; }

	int i;
	printf("parents:");
	for(i=0;i<t->nparents;i++)printf(" %s", t->parents[i]->name);
	printf("\n");
	printf("daughters:");
	for(i=0;i<t->ndaughters;i++)printf(" %s", t->daughters[i]->name);
	printf("\n");
}

show_glb(char	*input)
{
	struct type	*t = get_top();
	char	*p;
	for(p=strtok(input, " ");p && t;p=strtok(NULL, " "))
	{
		struct type	*t2 = lookup_type(p);
		if(!t2) { printf("no such type '%s'\n", p); return -1; }
		t = glb(t, t2);
	}
	printf("glb = %s\n", t?t->name:"BOTTOM");
}

struct job_stats	arbiter_input_loop(FILE	*fin)
{
	struct job_stats	st = {.success = 0, .fail = 0, .count = 0, .time = 0};
	struct timeval		tv1, tv2;
	struct timeval		jtv1, jtv2;
	float				stdin_time = 0;

	if(tsdb_notes)tsdb_run_note();	// now that we are connected to arbiter

	extern int arbiter_fd, arbiter_processing;
	extern char	*current_arbiter_job_id;
	arbiter_fd = 0;
	gettimeofday(&tv1, 0);
	while(!die && !feof(fin))
	{
		char	*arbiter_next_input();
		char	*next_input = arbiter_next_input();
		if(!next_input)break;
		arbiter_status("start work job=%s", current_arbiter_job_id);
		arbiter_processing = 1;
		gettimeofday(&jtv1, 0);
		int num_results;
		clear_slab();
		if(g_mode == PARSING)
			num_results = parse_line(next_input);
		else
		{
			clear_mrs();
			clear_slab();
			struct mrs	*mrs = parse_mrs(next_input);
			if(g_mode == GENERATING)
				num_results = generate(mrs);
			else num_results = transfer(mrs);
			free_mrs(mrs);
		}
		free(next_input);
		gettimeofday(&jtv2, 0);
		jtv2.tv_sec -= jtv1.tv_sec;
		jtv2.tv_usec -= jtv1.tv_usec;
		double	dt = jtv2.tv_sec + 0.000001 * jtv2.tv_usec;
		int slab_size_in_bytes();
		arbiter_processing = 0;
		arbiter_status("stop work job=%s time=%f ram=%d results=%d", current_arbiter_job_id, dt, slab_size_in_bytes(), num_results);
		free(current_arbiter_job_id);
		current_arbiter_job_id = NULL;
		if(num_results>0)st.success++;
		else if(num_results==0)st.fail++;
		if(num_results>=0)st.count++;
		fflush(stderr);
	}
	restore_stderr();
	//fprintf(stderr, "die = %d ; feof(fin) = %d\n", die, feof(fin));
	if(fin==stdin)stdin_time += timer();
	gettimeofday(&tv2, 0);

	tv2.tv_sec -= tv1.tv_sec;
	tv2.tv_usec -= tv1.tv_usec;
	clear_slab();
	st.ram = accum_ram_usage;
	st.time = (float)tv2.tv_sec + (float)tv2.tv_usec/1000000 - stdin_time;
	return st;
}

handle_lui_colon_command(char	*line)
{
	int	l = strlen(line);
	if(l>3 && line[l-1]=='\n')line[l-1] = 0;
	if(line[1]=='r' && line[2]==' ')
		lui_rule(line+3, 1);
	if(line[1]=='l' && line[2]==' ')
		lui_lex(line+3, 1);
	if(line[1]=='i' && line[2]==' ')
		lui_instance(line+3, 1);
	if(line[1]=='t' && line[2]==' ')
		lui_type(line+3, 1);
	if(line[1]=='h' && line[2]==' ')
		show_hierarchy(line+3);
	if(line[1]=='H' && line[2]==' ')
		lui_hierarchy(line+3);
	if(line[1]=='g' && line[2]==' ')
		show_glb(line+3);
	if(line[1]=='c')
		show_last_parse_chart();
	if(!strncmp(line, ":trigger", 8))
		debug_trigger_rules(line+8);
	if(!strncmp(line, ":break", 6))
		debug_lattice_mapping(line+6);
}

struct job_stats	main_input_loop(FILE	*fin)
{
	struct job_stats	st = {.success = 0, .fail = 0, .count = 0, .time = 0};
	struct timeval		tv1, tv2;
	float				stdin_time = 0;
//	int	tid = new_timer((g_mode==PARSING)?"parsing":"generating");

//	if(g_mode == GENERATING)	// Stephan suggested this, but it's actually slower.
//		configure_rules_head_driven();

	if(tsdb_notes)tsdb_run_note();
	char	linenoise_history_path[10240];
	if(getenv("HOME"))sprintf(linenoise_history_path, "%s/.ace_history", getenv("HOME"));
	else sprintf(linenoise_history_path, "/home/%s/.ace_history", getlogin());
	if(lui_mode)
	{
		linenoiseHistoryLoad(linenoise_history_path);
		extern void lui_linenoise_completion(const char*, linenoiseCompletions*);
		linenoiseSetCompletionCallback(lui_linenoise_completion);
	}

	gettimeofday(&tv1, 0);
	while(!die && !feof(fin))
	{
		int num_results;
		char	line[10240], *lineptr;
		if(g_mode == PARSING)
		{
			if(fin==stdin)timer();
			if(lui_mode)
			{
				lineptr = linenoise("");
				if(!lineptr)break;
				linenoiseHistoryAdd(lineptr);
				linenoiseHistorySave(linenoise_history_path);
			}
			else
			{
				if(!fgets(line, 10240, fin))break;
				lineptr = line;
			}
			if(fin==stdin)stdin_time += timer();
			//start_timer(tid);
			if(lui_mode && lineptr[0]==':')
			{
				handle_lui_colon_command(lineptr);
				num_results = -2;
			}
			else
			{
				if(!lui_mode)clear_slab();
				num_results = parse_line(lineptr);
				st.count++;
			}
			if(lui_mode)free(lineptr);
			//double et = stop_timer(tid, 1);
			//printf("%f seconds\n", et);
		}
		else
		{
			if(fin==stdin)timer();
			char	*mrs_string = read_mrs_string_or_line(fin, line, 10230);
			if(fin==stdin)stdin_time += timer();
			if(!mrs_string)
			{
				if(lui_mode && line[0]==':')
					handle_lui_colon_command(line);
				num_results = -2;
			}
			else
			{
				clear_mrs();
				if(!lui_mode)clear_slab();
				//struct mrs	*mrs = read_mrs(fin);
				struct mrs	*mrs = parse_mrs(mrs_string);
				free(mrs_string);
				if(!mrs && feof(fin))break;
				if(g_mode == GENERATING)
					num_results = generate(mrs);
				else num_results = transfer(mrs);
				st.count++;
				free_mrs(mrs);
			}
		}
		if(num_results==-1 || num_results==-2)
			{ if(num_results==-1 && !do_itsdb_stdout)fprintf(stderr, "NOTE: ignore\n"); }
		else if(num_results>0)st.success++;
		else if(num_results==0)st.fail++;
		fflush(stderr);
	}
	if(fin==stdin)stdin_time += timer();
	gettimeofday(&tv2, 0);

	tv2.tv_sec -= tv1.tv_sec;
	tv2.tv_usec -= tv1.tv_usec;
	clear_slab();
	st.ram = accum_ram_usage;
	st.time = (float)tv2.tv_sec + (float)tv2.tv_usec/1000000 - stdin_time;
	return st;
}

void	initialize_engine()
{
	setup_carcs_stack();
	init_glb_cache();

	if(!save_grammar_path)
	{
		load_frozen_grammar(load_grammar_path);
		if(csaw_grammar_path)csaw_init(load_grammar_path, csaw_grammar_path);
		if(override_maxent_path)load_mem(override_maxent_path);
	}
	else
	{
		struct timeval	tv1, tv2;
		if(!load_grammar_path)
			load_grammar_path = "../erg/ace/config.tdl";

		if(strstr(save_grammar_path, ".tdl"))
		{
			fprintf(stderr, "CAUTION: refusing to write grammar file to a pathname containing `.tdl'.\nDid you swap the -G and -g options?\n");
			exit(-1);
		}
		int fd = open(save_grammar_path, O_CREAT | O_TRUNC | O_RDWR, 0600);
		if(fd == -1)
		{
			perror(save_grammar_path);
			exit(-1);
		}

		gettimeofday(&tv1, 0);
		load_grammar(load_grammar_path);
		gettimeofday(&tv2, 0);
		tv2.tv_sec -= tv1.tv_sec;
		tv2.tv_usec -= tv1.tv_usec;
		if(override_maxent_path)load_mem(override_maxent_path);
		fprintf(stderr, "loaded grammar in %.5fs\n", (float)tv2.tv_sec + (float)tv2.tv_usec/1000000);

		close(fd);
		setup_save_frozen_grammar(save_grammar_path);
		freeze_grammar();
		exit(0);
	}

	setup_extra_type_dgs();
	g_loaded = 1;

	if(g_transfer)g_mode = TRANSFER;

	if(g_mode != TRANSFER)
		install_rf(inhibit_pack?0:((g_mode == PARSING)?1:2));
	init_rstats();

	if(export_parts)
	{
		dump_parts_of_speech();
		exit(0);
	}

	//print_rule("hspec");
	//lui_type("j-head");
	//print_rule("adjh_i_ques");
	//print_type("adj_head_int_ques_phrase");
	//print_type("n_mass_count_le");
	//print_type("n_intr_le");
	//print_lexeme("delete_v2");

	//check_unary_chains();
	//decompose_rules();
	clear_slab();

	extern void *the_ubertagger;
	if(enable_ubertagging && !the_ubertagger)
		fprintf(stderr, "WARNING: cannot enable übertagging; no model present in this grammar image.\n");
}

void	report_stats(struct job_stats	stats)
{
	if(stats.count)
		fprintf(stderr, "NOTE: %s %d / %d sentences, avg %dk, time %.5fs\n", (g_mode==PARSING)?"parsed":(g_mode==GENERATING?"generated":"transfered"),
			stats.success, stats.count, (int)(stats.ram / stats.count / 1024), (float)stats.time);

	rule_stats();
	report_unpacking();
	if(debug_level)print_glb_stats();
	final_chart_stats();
	//show_me();
}

void	logon_generation_server(char	*langcode)
{
	int	done = 0;
	void quitme(int sig) { done = 1; }
	char	path[10240];
	// LKB pretty much explicitly uses ~/tmp/
	sprintf(path, "%s/tmp/.transfer.%s.%s", getenv("HOME"), getlogin(), langcode);
	fprintf(stderr, "NOTE: generation server watching path: %s\n", path);
	signal(SIGINT, quitme);
	while(!done)
	{
		// this "protocol" is pretty hokey...
		FILE	*f = fopen(path, "r");
		if(!f) { usleep(100000); continue; }
		clear_mrs();
		clear_slab();
		struct mrs	*m = read_mrs(f);
		if(m)
		{
			int	nresults = generate(m);
		}
		else
		{
			fprintf(stderr, "NOTE: ignoring unreadable MRS\n");
		}
		fclose(f);
		unlink(path);
	}
	exit(0);
}

int	main(int	argc, char	*argv[])
{
	struct job_stats	stats;

	setlocale(LC_ALL, "");
	setlocale(LC_NUMERIC, "POSIX");

	parse_args(argc, argv);
	initialize_engine();

	if(do_itsdb && !do_itsdb_stdout) itsdb_mode();
	setup_signal_handlers();
	if(preexisting_lui_fd != -1)
	{
		lui_initialize();
		if(input_from_lui)
		{
			input_from_lui_mode();
			return 0;
		}
	}

	//generalization_experiments();
	/*extern int nstrings;
	extern struct type	**strings;
	printf("%d strings\n", nstrings);
	int i;
	for(i=0;i<nstrings;i++)printf("%d	= %s\n", i, strings[i]->name);*/

	/*int i;
	extern int nfnames;
	extern char **fnames;
	for(i=0;i<nfnames;i++)printf("%s\n", fnames[i]);*/

	//treebank_control(); return 0;

	//lexicon_glb_type_experiment();

	if(master_addr && strcmp(master_addr, "-"))
		stats = arbiter_input_loop(open_sentence_source());
	else if(!generation_server_lang)
		stats = main_input_loop(open_sentence_source());
	else logon_generation_server(generation_server_lang);

	shutdown_net();
	report_stats(stats);
	if(g_profiling)
	{
		if(g_mode == PARSING)
			report_profiler(parse_profiler);
		if(g_mode == GENERATING)
		{
			report_profiler(generation_profiler);
			report_profiler(transfer_profiler);
		}
		if(g_mode == TRANSFER)
			report_profiler(transfer_profiler);
	}
	if(debug_level)freport_timers(stderr);
	if(lui_mode)
	{
		quit_lui();
		wait_for_lui();
	}
	if(enable_tnt)tnt_kill();

	if(stats.success<=0 && stats.count>0)return -1;
	else return 0;
}

/*lexicon_glb_type_experiment()
{
	extern struct lexeme	**lexemes;
	int i;
	for(i=0;i<nlexemes;i++)
	{
		struct type	*pred = lexemes[i]->pred;
		if(!pred)continue;
		int j;
		for(j=0;j<pred->ndescendents;j++)
		{
			struct type	*desc = default_type_hierarchy()->types[pred->descendents[j]];
			if(!strncmp(desc->name, "g(", 2))
			{
				int k;
				printf("predicate '%s' has GLB subtype '%s'", pred->name, desc->name);
				printf("  = %s", desc->parents[0]->name);
				for(k=1;k<desc->nparents;k++)printf(" & %s", desc->parents[k]->name);
				printf("    with daughters:   %s", desc->daughters[0]->name);
				for(k=1;k<desc->ndaughters;k++)printf(", %s", desc->daughters[k]->name);
				printf("\n");
			}
		}
	}
}*/
