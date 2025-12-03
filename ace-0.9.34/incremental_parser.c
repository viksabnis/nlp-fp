/* XXX note
 * 	in rank_moves(),
 * 		for a lexical edge, may be able to seriously reduce space of possible moves sometimes using ->orth_routes
 * 		*/
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<signal.h>
#include	<time.h>

#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"morpho.h"
#include	"mrs.h"
#include	"unpack.h"

struct parser_input
{
	int	nwords;
	char	**forms, **lemmas;
	char	*sentence;

	int			nlexical_edges;
	struct edge	**lexical_edges;
};

struct situation
{
	double		score;
	int			nstack;
	struct edge	**stack;
	int			word;

	struct move	*moves;
	int			nmoves;

	int	moves_from_start;
};

struct move
{
	double	score, local_score;
	struct situation	*sit;
	struct edge	*e;
	struct move	*left, *right;
};


// parse strategy:
// view parsing as search on the space of (SR parsing situations)
// one formulation:  in this version, moves are scored locally and situations are scored as a combination of the moves leading to them
// initialize with main_agenda = the base situation
// each situation has an agenda of moves
//
// while(s = agenda_get(&main_agenda))
//     m = agenda_get(&s->moves);
//     s2 = make_move(s, m);
//     if(s2 represents a complete analysis)
//        all done parsing
//     score_situation(s2);
//     agenda_put(&main_agenda, s2);
//     if(s still has moves)
//        score_situation(s);
//        agenda_put(&main_agenda, s);

// alternate formulation:  in this version, moves have backpointers to their situations and are scored cumulatively
// while(m = agenda_get(&move_agenda))
//     s = m->from_situation;
//     s2 = make_move(s, m);
//     if(s2 represents a complete analysis)
//         all done parsing
//     for each m2 from s2
//         score_move(m2, s2);
//         agenda_put(&move_agenda, m2);
// advantages: closer to traditional chart parsing agenda system, maybe easier to combine with a chart for speed,
//  less agendas, a situation's ->score field doesn't change around confusingly
// disadvantages: weird initial condition, move ->score isn't a locally meaningful field


extern int	question, exhaustive, lui_mode, inhibit_pack, inhibit_results, do_itsdb, best_only;

struct parser_input	prepare_parser_input(int	nwords, char	**lemmas, char	**forms, char	*sentence)
{
	struct parser_input	in = {.nwords = nwords, .lemmas = lemmas, .forms = forms, .sentence = sentence};
	in.nlexical_edges = 0;
	in.lexical_edges = NULL;

	void	lex_edge_adder(struct edge	*le)
	{
		in.nlexical_edges++;
		in.lexical_edges = realloc(in.lexical_edges, sizeof(struct edge*)*in.nlexical_edges);
		in.lexical_edges[in.nlexical_edges-1] = le;
	}
	lexical_lookup(nwords, lemmas, forms, lex_edge_adder);

	return in;
}

struct situation	*parser_move(struct situation	*sit, struct move	*m);
struct move	*best_move(struct situation	*sit);
struct move	*agenda_get(struct move	**A);
void	agenda_put(struct move	**W, struct move	*m);
void	rank_moves(struct situation	*sit, struct parser_input	*in);
void	print_situation(struct situation	*sit, struct parser_input	*in);
void	print_move(struct move	*m);

int	situation_is_root_analysis(struct situation	*sit, struct parser_input	*in)
{
	if(sit->word < in->nwords)return 0;
	if(sit->nstack != 1)return 0;
	if(!is_root(sit->stack[0]->dg))return 0;
	return 1;
}

void	add_situation_moves(struct situation	*sit, struct move	**agenda, struct parser_input	*in)
{
	rank_moves(sit, in);
	struct move	*m;
	while(m = best_move(sit))
		agenda_put(agenda, m);
}

void	report_root_analysis(struct situation	*sit)
{
	struct dg	*dg = sit->stack[0]->dg;
	struct mrs	*m = extract_mrs(dg);

	printf("found a complete parse.\n");
	//printf("found a complete parse.  explored %d situations; actually needed %d moves.\n", n_moves, nhistory);
	//printf("  %d situations had at least one move; of those, avg # moves = %.1f\n", moveable_situations, (float)total_possible_moves / moveable_situations);
	/*int i;
	for(i=0;i<nhistory;i++)
	{
		printf("move %d at word %d\n", i, history[i]->word);
		history[i]->nmoves = 0;
		history[i]->moves = NULL;
		rank_moves(history[i], &in);
		print_moves(history[i]->moves, 1);
	}
	printf("\n");*/
	if(!inhibit_results)
	{
		print_mrs(m);
		printf("\n");
	}
}

int	i_parse(int	nwords, char	**lemmas, char	**forms, char	*sentence)
{
srand(time(0));
	struct parser_input	in;
	in = prepare_parser_input(nwords, lemmas, forms, sentence);

	struct move	*agenda = NULL, *m;
	struct situation	initial_situation;
	bzero(&initial_situation, sizeof(initial_situation));

	add_situation_moves(&initial_situation, &agenda, &in);
	while((m = agenda_get(&agenda)) != NULL)
	{
		struct situation	*s2 = parser_move(m->sit, m);
		print_situation(s2, &in);
		if(situation_is_root_analysis(s2, &in))
		{
			report_root_analysis(s2);
			return 1;
		}
		add_situation_moves(s2, &agenda, &in);
	}
	return 0;
}


void	print_situation(struct situation	*sit, struct parser_input	*in)
{
	int i;
	printf("situation: stack [");
	for(i=0;i<sit->nstack;i++)printf(" %s", sit->stack[i]->rule?sit->stack[i]->rule->name:sit->stack[i]->lex->word);
	printf(" ] remainder [");
	for(i=sit->word;i<in->nwords;i++)printf(" %s", in->forms[i]);
	printf(" ]   score = %f\n", sit->score);
}

void	print_move(struct move	*m)
{
	printf("move: ");
	if(m->e->rule)printf("reduce %d by %s", m->e->rule->ndaughters, m->e->rule->name);
	else printf("shift %s", m->e->lex->word);
	printf("   score %f\n", m->score);
}

struct edge	*combine_edges(struct rule	*r, struct edge	**rhs)
{
	int i;
	struct dg	*d = r->dg;
	for(i=0;i<r->ndaughters;i++)
	{
		if(unify_dg_tmp(rhs[i]->dg, d, i) != 0)
		{
			forget_tmp();
			return NULL;
		}
	}
	d = finalize_tmp(d, 1);
	if(!d)return NULL;

	struct edge	*e = calloc(sizeof(*e),1);
	e->dg = d;
	e->rule = r;
	e->id = next_eid();
	e->daughters = malloc(sizeof(void*)*e->rule->ndaughters);
	for(i=0;i<e->rule->ndaughters;i++)
		e->daughters[i] = rhs[i];
	e->have = e->need = e->rule->ndaughters;
	e->from = e->daughters[0]->from;
	e->to = e->daughters[e->have-1]->to;

	if(e->rule->lexical)
		setup_lexrule_edge(e);

	return e;
}

void	agenda_put(struct move	**W, struct move	*m)
{
	struct move	*w = *W;
	if(w && w->score >= m->score)
	{
		if(!w->left || (w->right && rand()%2))agenda_put(&w->left, m);
		else agenda_put(&w->right, m);
	}
	else
	{
		m->left = m->right = NULL;
		*W = m;
		if(w)
		{
			m->left = w->left;
			m->right = w->right;
			w->left = NULL;
			w->right = NULL;
			agenda_put(W, w);
		}
	}
}

struct move	*agenda_get(struct move	**A)
{
	struct move	*m = (*A), *l, *r;

	if(!m)return NULL;

	for(l=(*A)->left,r=(*A)->right;l && r;)
	{
		struct move *tmp;
		if(l->score > r->score)
		{
			// promote left
			*A = l;
			tmp = l->right;
			l->right = r;
			A = &l->left;
			l = l->left;
			r = tmp;
		}
		else
		{
			// promote right
			*A = r;
			tmp = r->left;
			r->left = l;
			A = &r->right;
			r = r->right;
			l = tmp;
		}
	}
	if(l)*A = l;
	else *A = r;
	return m;
}

static inline char* edge_sign(struct edge *e)
{
	if(!e)return NULL;
	if(!e->have)return e->lex->lextype->name;
	else return e->rule->name;
}

int	parsing_oracle(int	step, char	**reduce, char	**shift);
int	parsing_step = 0;

#define	ORACLE_ACCURACY	0.99

struct move	*rank_one_move(struct situation	*sit, struct edge	*e, struct parser_input	*in, int	use_oracle)
{
	struct move	*m = malloc(sizeof(*m));
	m->e = e;
	m->local_score = 2 * ((double)rand() / RAND_MAX - 0.5);

	if(use_oracle)
	{
		char	*reduce, *shift;
		if(parsing_oracle(sit->moves_from_start, &reduce, &shift) == 0)
		{
			if(e->have == 0)
			{
				if(shift && !strcmp(shift, e->lex->word))m->local_score = -1 + 2 * ORACLE_ACCURACY;
			}
			else
			{
				if(reduce && !strcmp(reduce, e->rule->name))m->local_score = -1 + 2 * ORACLE_ACCURACY;
			}
		}
	}

	m->score = sit->score + m->local_score;
	return m;
}

int	total_possible_moves, moveable_situations;

void	rank_moves(struct situation	*sit, struct parser_input	*in)
{
	int	use_oracle = 1;//((double)(rand()%1000) / 1000 < ORACLE_ACCURACY)?1:0;
	int	nmoves = 0;
	void	agendize_edge(struct edge	*e)
	{
		struct move	*m = rank_one_move(sit, e, in, use_oracle);
		m->sit = sit;
		agenda_put(&sit->moves, m);
		nmoves++;
	}

	int	i, j;
	for(i=0;i<nrules;i++)
	{
		if(rules[i]->ndaughters > sit->nstack)continue;
		if(rules[i]->span_only && sit->word != in->nwords)continue;
		for(j=0;j<rules[i]->ndaughters;j++)
		{
			struct edge	*rhs = sit->stack[sit->nstack - rules[i]->ndaughters + j];
			if(check_lexical_rule_constraints(rules[i], rhs))break;
			if(rhs->rule && !check_rf(rules[i], rhs->rule, j))break;
		}
		if(j < rules[i]->ndaughters)continue;
		struct edge	*e = combine_edges(rules[i], sit->stack+(sit->nstack - rules[i]->ndaughters));
		if(e)agendize_edge(e);
	}

	if(sit->word < in->nwords)
	{
		int i;
		if(sit->nstack)
		{
			struct edge	*buried = sit->stack[sit->nstack-1];
			// if shifting would bury an edge which still needs to be orthographemically altered
			if(buried->lex)
			{
				for(i=0;i<buried->north_routes;i++)
					if(buried->orth_routes[i].len == 0)break;
				if(i==buried->north_routes)goto skip_shifts;
			}
		}
		for(i=0;i<in->nlexical_edges;i++)
		{
			struct edge	*e = in->lexical_edges[i];
			if(e->from != sit->word)continue;
			agendize_edge(e);
		}
	}
	skip_shifts:;

	sit->nmoves = nmoves;
	if(nmoves) { total_possible_moves += nmoves; moveable_situations++; }
}

print_moves(struct move	*m, int	indent)
{
	int i;
	for(i=0;i<indent;i++)printf("  ");
	print_move(m);
	if(m->left)print_moves(m->left, indent+1);
	if(m->right)print_moves(m->right, indent+1);
}

struct move	*best_move(struct situation	*sit)
{
//	printf(" possible moves:\n");
//	if(sit->moves)print_moves(sit->moves, 0);
	return agenda_get(&sit->moves);
}

struct situation	*parser_move(struct situation	*sit, struct move	*m)
{
	struct situation	*ns = calloc(sizeof(struct situation),1);
	if(m->e->rule)
	{
		int	n = m->e->rule->ndaughters, i;
		ns->nstack = sit->nstack - n + 1;
		ns->stack = malloc(sizeof(struct edge*) * ns->nstack);
		for(i=0;i<ns->nstack-1;i++)
			ns->stack[i] = sit->stack[i];
		ns->stack[ns->nstack-1] = m->e;
		ns->word = sit->word;
	}
	else
	{
		ns->nstack = sit->nstack + 1;
		ns->stack = malloc(sizeof(struct edge*) * ns->nstack);
		memcpy(ns->stack, sit->stack, sizeof(struct edge*) * sit->nstack);
		ns->stack[ns->nstack-1] = m->e;
		ns->word = sit->word + m->e->lex->stemlen;
	}
	ns->score = m->score;
	ns->moves_from_start = sit->moves_from_start + 1;
	return ns;
}

int	old_i_parse(int	nwords, char	**lemmas, char	**forms, char	*sentence)
{
srand(time(0));
	int	noisy = !inhibit_results;
	total_possible_moves = moveable_situations = 0;

	int					nhistory = 0;
	struct situation	**history = NULL;
	struct situation	*sit;

	struct parser_input	in = {.nwords = nwords, .lemmas = lemmas, .forms = forms, .sentence = sentence};
	in.nlexical_edges = 0;
	in.lexical_edges = NULL;

	void	lex_edge_adder(struct edge	*le)
	{
		in.nlexical_edges++;
		in.lexical_edges = realloc(in.lexical_edges, sizeof(struct edge*)*in.nlexical_edges);
		in.lexical_edges[in.nlexical_edges-1] = le;
	}
	lexical_lookup(nwords, lemmas, forms, lex_edge_adder);

	nhistory = 0;
	history = NULL;
	sit = calloc(sizeof(struct situation),1);
	parsing_step = nhistory;
	rank_moves(sit, &in);

	int	n_moves = 0;

	while(!situation_is_root_analysis(sit, &in))
	{
		if(noisy)print_situation(sit, &in);
		struct move	*m = best_move(sit);
		if(!m)
		{
			// not finished parsing and no valid moves... uh-oh.
			if(nhistory == 0)
			{
				if(noisy)
					printf("ran out of places to backtrack to.\n");
				return 0;
			}
			// time to back-track.  go to the previous move in our history with the crummiest best_move_score
			int	i, worsti = 0;
			/*double	worst = 1E99;
			for(i=0;i<nhistory;i++)
				if(history[i]->best_move_score < worst)
					{ worst = history[i]->best_move_score; worsti = i; }*/
			worsti = nhistory-1;
			sit = history[worsti];
			nhistory = worsti;
			if(noisy)
				printf("backtracked; nhistory = %d\n", nhistory);
			continue;
		}
		// save where we were before making a move
		nhistory++;
		history = realloc(history, sizeof(void*)*nhistory);
		history[nhistory-1] = sit;

		// make the move
		if(noisy)print_move(m);
		parsing_step = nhistory;
		sit = parser_move(sit, m);
		rank_moves(sit, &in);
		n_moves++;
		if(nhistory > 200)
		{
			fprintf(stderr, "HUMPH we weren't supposed to get here.\n");
			return 0;
		}
	}

	struct dg	*dg = sit->stack[0]->dg;
	struct mrs	*m = extract_mrs(dg);

	printf("found a complete parse.  explored %d situations; actually needed %d moves.\n", n_moves, nhistory);
	printf("  %d situations had at least one move; of those, avg # moves = %.1f\n", moveable_situations, (float)total_possible_moves / moveable_situations);
	/*int i;
	for(i=0;i<nhistory;i++)
	{
		printf("move %d at word %d\n", i, history[i]->word);
		history[i]->nmoves = 0;
		history[i]->moves = NULL;
		rank_moves(history[i], &in);
		print_moves(history[i]->moves, 1);
	}
	printf("\n");*/
	if(!inhibit_results)
	{
		print_mrs(m);
		printf("\n");
	}
	return 1;
}
