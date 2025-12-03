#include	<sys/fcntl.h>
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<time.h>
#include	<sys/time.h>
#include	<stdarg.h>

#ifdef	TSDB
#include	<itsdb.h>
#else
#define capi_printf	printf
//#define capi_printf(fmt,...)
#endif

extern int do_itsdb_stdout;

int captured_capi_printf(const char	*format, ...)
{
	va_list	v, v2;
	va_start(v, format);
	va_copy(v2, v);
	int q = vsnprintf(NULL, 0, format, v);
	char	*buffer = malloc(q+2);
	vsnprintf(buffer, q+1, format, v2);
	if(!do_itsdb_stdout)
		capi_printf("%s", buffer);
	else printf("%s", buffer);
	free(buffer);
	va_end(v);
	va_end(v2);
	return q;
}

#undef	capi_printf
#define	capi_printf	captured_capi_printf

/* notes:

There are 4 top-level entry points where the ITSDB communication loop calls back to ACE:

create_test_run()
	reports the name of the engine back to ITSDB

process_item()
	either parses or generates from text input, for one item.
		parse_line(blah) ... calls back to:
			itsdb_report_parse() ... which reports various stats and calls:
				capi_print_derivations() .. which calls the unpacker to call:
					capi_print_tree() .. which reports individual results
		generate(blah) ... calls back to:
			itsdb_start_results()
			itsdb_report_genresult()
			itsdb_end_results()
			itsdb_report_gen()
	measures and reports :total = :tcpu (clock()) and :treal (wallclock), and possibly :error

reconstruct_item()
	we don't support this at the moment

complete_test_run()
	uncertain what this is supposed to do.


questions:
	- what is complete_test_run() supposed to do?
	- what is reconstruct_item() supposed to do?
	- how is ITSDB supposed to tell us whether to parse or to generate (or to transfer)?
		currently, we get that info from the commandline invocation, but it would be nice to be able to present a single CPU definition and have ITSDB tell us which operation it is interested in.
	- are we reporting the right memory usage?
	- what is the correct interpretation of each of the time reports?
	- how do we send back MRSes?
	- how do we send back a tree for generation?

*/

#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"mrs.h"
#include	"unpack.h"
#include	"lattice-mapping.h"
#include	"token.h"
#include	"unicode.h"

//#define	capi_printf(fmt...)	fprintf(stderr, fmt)

void tsdb_report_derivation(struct hypothesis	*hyp);
void tsdb_report_mrs(struct mrs	*mrs);
void tsdb_report_labels(struct hypothesis	*hyp);

extern int inhibit_results;
int itsdb_dump_chart = 0;

const int itsdb_wants_mrs = 1;

void	create_tsdb_run_note(char	*str, int	protocol_version)
{
	char platform [1024];
#if defined(__GNUC__) && defined(__GNUC_MINOR__)
	sprintf(platform, "gcc %d.%d", __GNUC__, __GNUC_MINOR__);
#else
	sprintf(platform, "unknown");
#endif

	str += sprintf(str, "(:application . \"answer\") (:platform . \"%s\")",
			platform);
	extern char	*grammar_version;
	str += sprintf(str, " (:grammar . \"%s\")", grammar_version?:"unknown");
	if(protocol_version >= 2)
		str += sprintf(str, " (:protocol . %d)", protocol_version);
	int	nlrules = 0, i;
	for(i=0;i<nrules;i++)if(rules[i]->lexical)nlrules++;
	str += sprintf(str, " (:avms . %d) (:lexicon . %d) (:lrules . %d) (:rules . %d)",
			default_type_hierarchy()->ntypes,
			nlexemes, nlrules, nrules-nlrules);
}

void tsdb_run_note()
{
	char	buffer[10240];
	create_tsdb_run_note(buffer, 1);
	printf("NOTE: tsdb run: %s\n", buffer);
	fflush(stdout);
}

static int create_test_run(const char *data, int run_id, const char *comment,
		int interactive, int protocol_version, const char *custom)
{
	if(protocol_version > 0)// && protocol_version <= 2)
	{
		char	runnote[10240];
		create_tsdb_run_note(runnote, protocol_version);
		capi_printf("%s", runnote);

		if(protocol_version == 2)
			itsdb_dump_chart = 1;
		else itsdb_dump_chart = 0;
	}
	return 0;
}

extern int exhaustive, inhibit_pack;
extern long top_unifies, top_unifies_wellform, top_copies;

extern int report_labels;
extern int best_only;

int	tsdb_i_id = -1;

int tsdb_nanalyses, tsdb_maxanalyses, tsdb_nderivations, tsdb_maxderivations=1;

#define	ERROR_BUFFER_LENGTH	1024
static char	the_itsdb_error_buffer[ERROR_BUFFER_LENGTH];
static char	*the_itsdb_error;

void itsdb_error(char	*error)
{
	extern int do_itsdb, tsdb_notes;
	if(!do_itsdb && !tsdb_notes)return;
	if(the_itsdb_error)
	{
		int	l2 = strlen(the_itsdb_error) + strlen(error) + 10;
		if(l2 > ERROR_BUFFER_LENGTH - 5)
		{
			fprintf(stderr, "ERROR: not enough room for that many itsdb errors!\n");
			return;
		}
		sprintf(the_itsdb_error_buffer, "%s, %s", the_itsdb_error, error);
	}
	else
	{
		int	l2 = strlen(error);
		the_itsdb_error = the_itsdb_error_buffer;
		if(l2 > ERROR_BUFFER_LENGTH - 5)
		{
			fprintf(stderr, "ERROR: not enough room for that many itsdb errors!\n");
			strcpy(the_itsdb_error, "I have discovered a truly beautiful error, which sadly the margin is too small to contain.");
			return;
		}
		strcpy(the_itsdb_error, error);
	}
}

static char	*the_itsdb_comment;

void itsdb_comment(char	*comment)
{
	extern int do_itsdb, tsdb_notes;
	if(!do_itsdb && !tsdb_notes)return;
	the_itsdb_comment = strdup(comment);
}

static struct timeval	pnstart;
static int cpustart;
tsdb_parse_note_start()
{
	gettimeofday(&pnstart, NULL);
	cpustart = clock();
}

create_tsdb_parse_note(char	*str)
{
	struct timeval	tv2;
	int	c1;
	gettimeofday(&tv2, 0);
	c1 = clock();

	int	wallclock_msec = 1000*(tv2.tv_sec - pnstart.tv_sec) + 0.001*(tv2.tv_usec - pnstart.tv_usec);
	int	cpuclock_msec = (int)((long long)(c1-cpustart)*1000 / CLOCKS_PER_SEC);
	str += sprintf(str, " (:total . %d) (:treal . %d)", cpuclock_msec, wallclock_msec);
	str += sprintf(str, " (:tcpu . %d)", cpuclock_msec);

	str += sprintf(str, " (:others . %lld)", slab_usage());

	if(the_itsdb_error)
	{
		str += sprintf(str, " (:error . \"%s\")", the_itsdb_error);
		the_itsdb_error = NULL;
	}
	if(the_itsdb_comment)
	{
		str += sprintf(str, " (:comment . \"%s\")", the_itsdb_comment);
		free(the_itsdb_comment);
		the_itsdb_comment = NULL;
	}
}

tsdb_parse_note_end()
{
	char	buffer[10240];
	create_tsdb_parse_note(buffer);
	if(do_itsdb_stdout)printf(" %s\n", buffer);
	else printf("NOTE: tsdb parse: %s\n", buffer);
	fflush(stdout);
}

static int process_item(int i_id, const char *i_input, int parse_id, 
		int edges, int nanalyses, int nderivations, int interactive, const char	*custom)
{
	extern int total_edges, real_edges, passive_edges;
	int readings;

	the_itsdb_error = NULL;
	the_itsdb_comment = NULL;
	//fprintf(stderr, "process_item asked for: %d = nanalyses, %d = nderivations\n", nanalyses, nderivations);
	tsdb_maxanalyses = nanalyses;
	tsdb_maxderivations = nderivations;
	tsdb_nanalyses = 0;
	tsdb_nderivations = 0;

	inhibit_results = 1;
	best_only = nanalyses;//nderivations;
	tsdb_i_id = i_id;

	if(custom && *custom)
	{
		assert(strlen(custom)<1024);
		char	Lhs[1024], Rhs[1024];
		if(2==sscanf(custom,"%[^:]:=%[^.].", Lhs, Rhs))
		{
			char	*lhs = trim_string(Lhs);
			char	*rhs = trim_string(Rhs);
			if(!strcasecmp(lhs,"start-symbols"))
			{
				disable_all_roots();
				char	*root;
				for(root=strtok(rhs," \t\n");root;root=strtok(NULL," \t\n"))
					enable_root((*root=='$')?(root+1):root);
			}
		}
	}

	top_copies = top_unifies_wellform = top_unifies = 0;

	extern int want_mrs;
	want_mrs = itsdb_wants_mrs;

	tsdb_parse_note_start();
	clear_mrs();
	clear_slab();
	if(g_mode == PARSING)
		readings = parse_line(i_input);
	else
	{
		//fprintf(stderr, "mrs input: `%s'\n", i_input);
		char	*mutable_input = strdup(i_input);
		struct mrs *m = parse_mrs(mutable_input);
		if(!m)
		{
			readings = -1;
			itsdb_error("unable to parse MRS input");
		}
		else
		{
			//print_mrs(m);
			readings = generate(m);
			free_mrs(m);
		}
		free(mutable_input);
	}
	char	buffer[10240];
	create_tsdb_parse_note(buffer);
	capi_printf("%s", buffer);
}

void	itsdb_dump_tokens(char	*name, char	*countname, struct lattice	*tokens)
{
	capi_printf("(%s . %d) ", countname, tokens->nedges);
	capi_printf("(%s . \"", name);
	int i;
	for(i=0;i<tokens->nedges;i++)
	{
		// (id, start, end, [link,] path+, form [surface], ipos, lrule+[, {pos p}+])
		struct lattice_edge	*e = tokens->edges[i];
		struct token	*t = e->token;
		char	tokstr[10240], *tsp = tokstr;
		tsp += sprintf(tsp, "(%d, %d, %d, <%d:%d>, 1, \"%s\", 0, \"null\"",
			t->eid, e->from->id, e->to->id, t->cfrom, t->cto, slab_escape(t->string));
		int j;
		if(t->npostags)tsp += sprintf(tsp, ",");
		for(j=0;j<t->npostags;j++)
			tsp += sprintf(tsp, " \"%s\" %s", slab_escape(t->postags[j].tag), t->postags[j].prob);
		tsp += sprintf(tsp, ")");
		capi_printf("%s%s", i?" ":"", slab_escape(tokstr));
	}
	capi_printf("\") ");
}

int itsdb_report_parse(struct lattice	*tokens, struct lattice	*lexical_chart, int	status, int	tforest)
{
	extern int total_edges, real_edges, passive_edges;

	if(status == 0 || status == -2)
	{
		capi_printf("(:copies . %ld) (:unifications . %ld) ", top_copies, top_unifies + top_unifies_wellform);
		//capi_printf("(:tcpu . %d) ", tforest);
		if(tokens)itsdb_dump_tokens(":p-tokens", ":ntokens", tokens);

		int readings;
		if(itsdb_dump_chart)
			capi_print_chart(tokens, lexical_chart, status);
		if(status == 0)
		{
			// when requesting the chart, nanalyses=0 means don't actually report any derivations.
			if(itsdb_dump_chart && tsdb_maxanalyses == 0)
				readings = 0;
			// otherwise, enumerate some derivations!
			else readings = capi_print_derivations();

			capi_printf("(:readings . %d) (:pedges . %d) (:aedges . %d) ",
	//			readings,
				tsdb_nanalyses,
				passive_edges, real_edges - passive_edges);
		}
		else
		{
			capi_printf("(:readings . 0) (:pedges . 0) (:aedges . 0) ");
			readings = -2;
		}
		return readings;
	}
	else
	{
		capi_printf("(:copies . 0) (:unifications . 0) (:tcpu . 0) (:readings . 0) (:pedges . 0) (:aedges . 0) (:others . 0) ");
		return -1;
	}
}

void	itsdb_report_gen(int readings, double	fixup_time)
{
	extern int total_edges, real_edges, passive_edges;

	capi_printf("(:readings . %d) (:pedges . %d) (:aedges . %d) ",
//		readings,
		tsdb_nanalyses,
		passive_edges, real_edges - passive_edges);

	capi_printf("(:tgc . %d) ", (int)(fixup_time * 1000));

	capi_printf("(:copies . %ld) (:unifications . %ld) ", top_copies, top_unifies + top_unifies_wellform);
}

itsdb_start_results() { capi_printf("(:results . ("); }
itsdb_end_results() { capi_printf(")) "); }

void	itsdb_report_genresult(struct hypothesis *hyp, struct mrs *mrs, int id)
{
	char		*esc = malloc(strlen(hyp->string)*2+1), *p, *q;

	tsdb_nanalyses++;

	if(tsdb_nderivations >= tsdb_maxderivations && !(do_itsdb_stdout && tsdb_maxderivations==0))return;
	tsdb_nderivations++;

	capi_printf("((:result-id . %d)", id++);

	for(q=esc,p=hyp->string;*p;p++)
	{
		if(*p=='"' && *p=='\\')*q++ = '\\';
		*q++ = *p;
	}
	*q=0;
	capi_printf("(:surface . \"%s\") ", esc);
	//capi_printf("(:tree . \"%s\") ", esc);
	//fprintf(stderr, "ITSDB output '%s'\n", esc);

	// report the derivation and the MRS as well
	tsdb_report_derivation(hyp);
	if(itsdb_wants_mrs)
		tsdb_report_mrs(mrs);
	if(report_labels)
		tsdb_report_labels(hyp);

	free(esc);
	capi_printf("(:score . %f)) ", hyp->score);
}

char	*heap_escape(char	*str)
{
	int	len = strlen(str) * 2 + 1;
	char	*esc = malloc(len), *ep = esc;
	while(*str)
	{
		if(*str=='\\' || *str=='"')
			*ep++ = '\\';
		*ep++ = *str++;
	}
	*ep = 0;
	return esc;
}

void capi_escape_and_print_long_string(char	*unesc)
{
	char	*hesc = heap_escape(unesc), *esc = hesc;
	// capi_printf can only handle 1kb chunks at a time... :blink:
	// if we blindly split text up at 1kb boundaries,
	// we stand a chance of splitting in the middle of a multibyte character.
	// capi_printf() apparently has a problem with that...
	// soooo... be more careful?
	while(strlen(esc) > 1000)
	{
		// figure out how many characters less than 1000
		// we have to send to avoid stopping in the middle of a multibyte sequence.
		// this code assumes characters in the middle of a multibyte sequence
		// are >= 128. (true for UTF-8)
		int	snark = 0;
		while(0x80 & esc[1000-snark])
			snark--;
		capi_printf("%.*s", 1000-snark, esc);
		esc += 1000-snark;
	}
	capi_printf("%s", esc);
	free(hesc);
}

void tsdb_report_derivation(struct hypothesis	*hyp)
{
	capi_printf(" (:derivation .\"");
	char	*derivation = hypothesis_to_dstring(hyp);
	capi_escape_and_print_long_string(derivation);
	free(derivation);
	capi_printf("\")");
}

void tsdb_report_labels(struct hypothesis	*hyp)
{
	capi_printf(" (:tree .\"");
	char	*derivation = hypothesis_to_labelled_tree_string(hyp);
	capi_escape_and_print_long_string(derivation);
	free(derivation);
	capi_printf("\")");
}

void tsdb_report_mrs(struct mrs	*mrs)
{
	capi_printf(" (:mrs .\"");
	static char	*buffer = NULL;
	#define	MRS_BUFFER_LEN	(1024*32)
	if(!buffer)buffer = malloc(MRS_BUFFER_LEN);
	int l = snprint_mrs(buffer, MRS_BUFFER_LEN-1, mrs);
	if(l < MRS_BUFFER_LEN-1)capi_escape_and_print_long_string(buffer);
	else
	{
		char	*tmp = malloc(l+10);
		snprint_mrs(tmp, l+10, mrs);
		capi_escape_and_print_long_string(tmp);
		free(tmp);
	}
	capi_printf("\")");
}

char	*this_edge_is_root(struct edge	*edge)
{
	if(edge->from != 0)return NULL;
	if(edge->to != chart_size-1)return NULL;
	if( (g_mode!=GENERATING || edge->neps == require_neps) && !edge->frozen)
	{
		char	*r = is_root(edge->dg);
		return r;
	}
	return NULL;
}

void	reset_unpacking_e(struct edge	*e)
{
	e->unpack = NULL;
	if(!e->lex)return;
	if(e->have)reset_unpacking_e(e->daughters[0]);
	int i;
	for(i=0;i<e->npack;i++)reset_unpacking_e(e->pack[i]);
}

void	reset_unpacking()
{
	int i, j, k, l;
	for(i=0;i<chart_size;i++)
		for(j=0;j<chart_size;j++)
			for(k=0;k<cells[j*chart_size + i].p_nedges;k++)
			{
				struct edge	*e = cells[j*chart_size + i].p_edges[k];
				e->unpack = NULL;
				if(e->lex)	// lexical edges can contain daughters that are not in the chart. recurse.
					reset_unpacking_e(e);
				for(l=0;l<e->npack;l++)
				{
					struct edge	*E = e->pack[l];
					E->unpack = NULL;
					if(E->lex)reset_unpacking_e(E);
				}
			}
}

#define	TOKEN_EDGE_TYPE		0
#define	LEXEME_EDGE_TYPE	1
#define	LEXRULE_EDGE_TYPE	2
#define	SYNRULE_EDGE_TYPE	3
#define	ROOT_EDGE_TYPE		4

#define	RESULT_EDGE_STATUS	1
#define	ACTIVE_EDGE_STATUS	2
#define	PACKED_EDGE_STATUS	4
#define	FROSTED_EDGE_STATUS	8
#define	FROZEN_EDGE_STATUS	16

int	nlexr_edges, nsynr_edges;

void	capi_print_chart_edge(struct edge	*e, struct lattice	*tokens, int	was_packed)
{
	if(e->unpack)return;
	e->unpack = (void*)0x1;
	char	*sign = e->rule?e->rule->name:e->lex->word;
	int	i;
	capi_printf(" ((:e-id . %d) (:e-label . \"%s\") (:e-start . %d) (:e-end . %d) (:e-status . %d)", e->id, sign, e->from, e->to, RESULT_EDGE_STATUS | (was_packed?PACKED_EDGE_STATUS:0));
	if(!e->rule)
	{
		// lexeme edge
		capi_printf(" (:e-type . %d)", LEXEME_EDGE_TYPE);
		capi_printf(" (:e-daughters . (");
		for(i=0;i<e->lex->stemlen;i++)capi_printf(" %d", ((struct token*)e->daughters[i])->eid);
		capi_printf(" ))");
	}
	else
	{
		// rule edge
		capi_printf(" (:e-daughters . (");
		for(i=0;i<e->have;i++)capi_printf(" %d", e->daughters[i]->id);
		capi_printf(" ))");

		if(e->rule->lexical)
		{
			capi_printf(" (:e-type . %d)", LEXRULE_EDGE_TYPE);
			nlexr_edges++;
		}
		else
		{
			capi_printf(" (:e-type . %d)", SYNRULE_EDGE_TYPE);
			nsynr_edges++;
		}
	}
	capi_printf(" (:e-alternates . (");
	for(i=0;i<e->npack;i++)capi_printf(" %d", e->pack[i]->id);
	capi_printf(")))");
	for(i=0;i<e->npack;i++)
		capi_print_chart_edge(e->pack[i], tokens, 1);
	for(i=0;i<e->have;i++)
		capi_print_chart_edge(e->daughters[i], tokens, 0);
}

void	capi_print_root_edge(char	*name, int	daughter_id, int	start, int	end)
{
	int	my_id = next_eid();
	capi_printf(" ((:e-id . %d) (:e-label . \"%s\") (:e-start . %d) (:e-end . %d) (:e-status . %d) (:e-type . %d) (:e-daughters . (%d)) (:e-alternates . ()))",
		my_id, name, start, end, RESULT_EDGE_STATUS, ROOT_EDGE_TYPE, daughter_id);
}

int capi_print_chart(struct lattice	*tokens, struct lattice	*lexical_chart, int	status)
{
	capi_printf("(:chart . (");
	int i, nroots = 0;

	nlexr_edges = 0;
	nsynr_edges = 0;
	if(status == 0)
	{
		struct chart_cell	*root_cell = &cells[chart_size-1];
		reset_unpacking();
		for(i=0;i<root_cell->p_nedges;i++)
		{
			struct edge	*edge = root_cell->p_edges[i];
			char	*r = this_edge_is_root(edge);
			if(r)
			{
				nroots++;
				capi_print_root_edge(r, edge->id, edge->from, edge->to);
				capi_print_chart_edge(edge, tokens, 0);
			}
		}
		reset_unpacking();
	}

	// output pseudo-edges for the token chart
	extern int yy_mode;
	if(!yy_mode)improve_token_lattice_characterization(tokens);
	int	ntokedges = 0;
	for(i=0;i<tokens->nedges;i++)
	{
		struct lattice_edge	*le = tokens->edges[i];
		struct token	*t = le->token;
		capi_printf(" ((:e-id . %d) (:e-start . %d) (:e-end . %d)", t->eid, le->from->id, le->to->id);
		char	token_str[10240];
		if(enable_token_avms)
		{
			extern int dag_print_style;
			dag_print_style = 1;
			snprint_dg(token_str, 10239, t->dg);
			dag_print_style = 0;
		}
		else
		{
			//sprintf(token_str, "%s", t->string);
			char	*formesc = heap_escape(t->string);
			sprintf(token_str, "token [ +FROM \"%d\" +TO \"%d\" +FORM \"%s\" ]", t->cfrom, t->cto, formesc);
			free(formesc);
		}
		char	*labelesc = heap_escape(token_str);
		capi_printf(" (:e-status . %d) (:e-type . %d) (:e-label . \"%s\") (:e-daughters . ()) (:e-alternates . ()))",
			t->used?RESULT_EDGE_STATUS:0, TOKEN_EDGE_TYPE, labelesc);
		free(labelesc);
		ntokedges++;
	}

	capi_printf("))");
	if(status == 0)
	{
		// fields 'ninputs', 'ntokens', 'tedges' as per 10/30/2012 email w/ oe:
		// ninputs = tokens produced by REPP
		// ntokens = tokens *after* chart mapping
		// tedges = count of 'edge' relation tuples with type TOKEN_EDGE_TYPE
		//capi_printf("(:ninputs . %d) ", nrepptokens);
		//capi_printf("(:ntokens . %d) ", tokens->nedges);
		capi_printf("(:tedges . %d) ", ntokedges);
		capi_printf("(:eedges . %d) ", lexical_chart->nedges);
		capi_printf("(:ledges . %d) ", nlexr_edges);
		capi_printf("(:sedges . %d) ", nsynr_edges);
		capi_printf("(:redges . %d) ", nroots);
		/*extern int noriginaltokens, nmappingtokens;
		capi_printf("(:ninputs . %d) ", noriginaltokens);
		capi_printf("(:ninputs . %d) ", nmappingtokens);*/
	}
}

int	capi_print_derivations()
{
	int id;

	tsdb_nderivations = 0;
	tsdb_nanalyses = 0;
	id = 0;
	int capi_print_tree(struct hypothesis	*hyp, struct mrs	*mrs, double	prob)
	{
		tsdb_nanalyses++;
		if(tsdb_nderivations >= tsdb_maxderivations && !(do_itsdb_stdout && tsdb_maxderivations==0))return 1;
		tsdb_nderivations++;

		capi_printf("((:result-id . %d)", id++);

		tsdb_report_derivation(hyp);

		if(itsdb_wants_mrs)
			tsdb_report_mrs(mrs);
		if(report_labels)
			tsdb_report_labels(hyp);

		//capi_printf(" (:score .%f))", hyp->score);
		capi_printf(" (:flags ((:ascore . %f) (:probability . %f))))", hyp->score, prob);
		return 1;
	}
	itsdb_start_results();
	int	n = iterate_cell_root_hypotheses(&cells[chart_size-1], capi_print_tree, best_only);
	itsdb_end_results();
	return n;
}

static int complete_test_run(int run_id, const char *custom)
{
	return 0;
}

static int reconstruct_item(const char *derivation)
{
	return 0;
}

void itsdb_mode()
{
	int fd;
	close(1);
	char	logfilepath[256] = "/dev/null";
	//sprintf(logfilepath, "/tmp/answer.itsdb");
	dup2(fd = open(logfilepath, O_WRONLY | O_CREAT, 0600), 1);
#ifdef TSDB
	if(!capi_register(create_test_run, process_item, reconstruct_item, complete_test_run))
		slave();
#endif
	close(fd);
}
