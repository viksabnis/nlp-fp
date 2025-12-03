#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<math.h>
#include	<assert.h>
#include	<stdarg.h>

#include	"../hash.h"
#include	"csaw.h"
#include	"../tree.h"
#include	"../dag.h"

/* caveat: this parser does not process unary rules until a fixedpoint.  instead, it iterates unary rules 5 times. this is BROKEN BEHAVIOR! */

/* todo: consider greedy search; consider pruning techniques */

/* to read the top derivation off, start from the start symbol.
at each node (top-down), need to pick (1) a rule and (2) split points such that maximum probability is preserved.
as long as such a choice can be made, optimality cannot be comprimised by subsequent choices.
with no back pointers, finding such a split amounts to iterating through all rules and split points once per node of the derivation -- an O(n^2) operation which should be dwarfed by the O(n^3) overall parsing job. storing back-pointers would double space requirements...

one wrinkle with this plan is that it assumes perfect floating point math, which is a pipe dream.
need to be willing to surrender an epsilon here or there. */

/* empirical timings (parsing only, with unpacking, but excluding grammar loading)
grammar: aquaintboth-gp2.pcfg -- 5k terminals, 130k nonterminals, 3362k rules

3 words		9	27		0.8s	k = 0.3		c = 0.089
5 words		25	125		2.4s	k = 0.19	c = 0.096
8 words		64	512		8.5s	k = 0.166	c = 0.133
empirically not quite cubic, but worse than quadratic
also: unpacking time is completely negligible (order of 1ms)
*/

/* empirical shape of the grammar:
0.5m unary rules
2.8m binary rules
20k quad rules
... would it be worthwhile to binarize the grammar?
eliminate recursion... possibly faster search.
easier to convert to hash tables
*/

/* index the rules by the first element of RHS;
then, when applying rules to [from,to], can go straight to applicable rules.
(required also keeping track of a startingAt[] boolean array for each token position)
(got a slowdown when the index pointed to in-place rule array; speedup when the rules are copied into the index's own arrays.  memory bandwidth limited!)

3 words		0.24s
5 words		1.2s
8 words		5.6s
*/

/* tested on WSJ item 22002005.lt.  completed in 138s.  comparison: bitpar took 280s on the aquaint1 grammar; extrapolating, this ridiculously simple parser is 3x faster than bitpar.  how is that possible!?  no unary chains.
*/

/* // real probabilities
#define	TERM_PROB	1.0
#define	ZERO_PROB	0.0
#define	COMBINE_PROB(x,y)	(x*y)
#define	ENCODE_PROB(x)	(x)
*/

// log probabilities
//#define	TERM_PROB	0
#define	ZERO_PROB	((float)-1E100)
#define	COMBINE_PROB(x,y)	(x+y)
#define	ENCODE_PROB(x)	(log(x))
#define	DECODE_PROB(x)	(exp(x))

static struct rule
{
	int	lhs, arity;
	float	p;
	int	*rhs;
}	*rules;
static int	nrules;

static struct ruleset
{
	struct rule	*rules;
	int			nrules, arules;
}	*u_rules_for_nonterm, *u_rules_for_term, *b_rules_for_nonterm, *b_rules_for_term, *h_rules_for_nonterm, *h_rules_for_term;

static struct hash	*termwordfreqhash;

static int csaw_reconstruct(int	from, int	to, int	lhs, int (*dprintf)(const char*,...));

static char	**terminals;
static long long	*termfreq;
static int		nterminals;
static struct hash	*termhash;

static char	**nonterminals;
static long long	*ntfreq;
static int		nnonterminals;
static int	start_symbol;

static int	ctimer;
static int	utimer;
static int	unarytimer, binarytimer, highertimer;

static make_pcfg_timers()
{
	ctimer = new_timer("chart");
	unarytimer = new_timer("unary");
	binarytimer = new_timer("binary");
	highertimer = new_timer("higher");
	utimer = new_timer("unpack");
}

static void add_to_ruleset(struct ruleset	*rs, struct rule	*r)
{
	rs->nrules++;
	if(rs->nrules>rs->arules)
	{
		rs->arules = rs->nrules*2;
		rs->rules = realloc(rs->rules, sizeof(struct rule)*rs->arules);
	}
	rs->rules[rs->nrules-1] = *r;
}

csaw_load_pcfg(char	*path)
{
	FILE	*f = fopen(path, "r");
	int i;
	char	buffer[1024];
	if(!f){perror(path);exit(-1);}

	assert(1 == fscanf(f, "terminals %d\n", &nterminals));
	terminals = malloc(sizeof(char*)*nterminals);
	termhash = hash_new("terminals");
	termfreq = malloc(sizeof(long long)*nterminals);
	for(i=0;i<nterminals;i++)
	{
		assert(2 == fscanf(f, "%lld %[^\n ]\n", &termfreq[i], buffer));
		terminals[i] = strdup(buffer);
		int	*ip = malloc(sizeof(i));
		*ip = i;
		hash_add(termhash, terminals[i], ip);
	}

	assert(1 == fscanf(f, "nonterminals %d\n", &nnonterminals));
	nonterminals = malloc(sizeof(char*)*nnonterminals);
	ntfreq = malloc(sizeof(long long)*nnonterminals);
	for(i=0;i<nnonterminals;i++)
	{
		assert(2 == fscanf(f, "%lld %[^\n ]\n", &ntfreq[i], buffer));
		nonterminals[i] = strdup(buffer);
		if(!strcasecmp(nonterminals[i], "^/^/TOP"))
		{
			start_symbol = i;
			//fprintf(stderr, "found start symbol: %d = %s\n", i, nonterminals[i]);
		}
	}

	assert(1 == fscanf(f, "rules %d\n", &nrules));
	rules = malloc(sizeof(struct rule)*nrules);
	termwordfreqhash = hash_new("termwordfreq");
	u_rules_for_nonterm = calloc(sizeof(struct ruleset), nnonterminals);
	u_rules_for_term = calloc(sizeof(struct ruleset), nterminals);
	b_rules_for_nonterm = calloc(sizeof(struct ruleset), nnonterminals);
	b_rules_for_term = calloc(sizeof(struct ruleset), nterminals);
	h_rules_for_nonterm = calloc(sizeof(struct ruleset), nnonterminals);
	h_rules_for_term = calloc(sizeof(struct ruleset), nterminals);
	int	nrealrules = 0, nlexmodelrules = 0;
	for(i=0;i<nrules;i++)
	{
		long long	rfreq;
		assert(2 == fscanf(f, "%lld %[^\n]\n", &rfreq, buffer));
		int	lhs = atoi(buffer);
		if(lhs<0)
		{
			lhs = -1-lhs;
			assert(lhs>=0 && lhs<nterminals);
			float	*p = malloc(sizeof(float));
			*p = ENCODE_PROB((double)rfreq / termfreq[lhs]);
			hash_add(termwordfreqhash, strdup(buffer), p);
			nlexmodelrules++;
			continue;
		}
		struct rule	*r = &rules[nrealrules++];
		r->lhs = lhs;
		assert(r->lhs>=0 && r->lhs<nnonterminals);
		double	prob = (double)rfreq / ntfreq[r->lhs];
		r->p = ENCODE_PROB(prob);
		int	rhs[10], arity=0;
		char	*p;
		strtok(buffer, " ");	// consume LHS
		while(p = strtok(NULL," "))rhs[arity++] = atoi(p);
		r->arity = arity;
		r->rhs = malloc(sizeof(int)*arity);
		memcpy(r->rhs, rhs, sizeof(int)*arity);
		switch(arity)
		{
			case	1:
				if(r->rhs[0]>=0)add_to_ruleset(&u_rules_for_nonterm[r->rhs[0]], r);
				else add_to_ruleset(&u_rules_for_term[-1-r->rhs[0]], r);
				break;
			case	2:
				if(r->rhs[0]>=0)add_to_ruleset(&b_rules_for_nonterm[r->rhs[0]], r);
				else add_to_ruleset(&b_rules_for_term[-1-r->rhs[0]], r);
				break;
			default:
				if(r->rhs[0]>=0)add_to_ruleset(&h_rules_for_nonterm[r->rhs[0]], r);
				else add_to_ruleset(&h_rules_for_term[-1-r->rhs[0]], r);
				break;
		}
	}
	nrules = nrealrules;

extern int debug_level;
	if(debug_level)fprintf(stderr, "CSAW: loaded %d terminals (%d word-terminal counts), %d nonterminals, and %d rules\n", nterminals, nlexmodelrules, nnonterminals, nrules);
	make_pcfg_timers();
}

char	*csaw_trim(char	*buffer)
{
	while(*buffer==' ' || *buffer=='\t' || *buffer=='\n')buffer++;
	int	l = strlen(buffer);
	char	*q = buffer+l-1;
	while(q>=buffer && (*q=='\n' || *q==' ' || *q=='\t'))*q--=0;
	return buffer;
}

static struct token
{
	int	from, to;
	int		term;
	char	*deriv;
	float	prob;
}	*tokens;
static int	ntokens;

static struct token	***mwefrom;
static int				*nmwefrom;
static struct token	***mweto;
static int				*nmweto;

static float	**termprobs;
static int		chart_size;
static float	**chart;
static char	*startingAt;
static char	*endingAt;

static int	nonzeros = 0, increases = 0;

void	csaw_reset_pcfg_tokens() { ntokens = 0; }

#define	UNK_MASS		0.01
#define	SMOOTH_LEX(q)	((1-UNK_MASS) * (q))

void	csaw_add_pcfg_token(int	from, int	to, char	*term, char	*deriv, char	*surface)
{
	int	*tidp = hash_find(termhash, term);
	if(!tidp)return;
	char	lookup[1024];
	snprintf(lookup, 510, "%d %s", -1-*tidp, surface);
	float	*probp = hash_find(termwordfreqhash, lookup);
	struct token	T;
	T.from = from;
	T.to = to;
	T.term = *tidp;
	T.deriv = strdup(deriv);
	if(probp)
	{
		//printf("P(%s | %s) = %g\n", surface, term, *probp);
		T.prob = ENCODE_PROB(SMOOTH_LEX(DECODE_PROB(*probp)));
	}
	else
	{
		//printf("P(%s | %s) = 0 ; using unknown mass\n", surface, term);
		T.prob = ENCODE_PROB(UNK_MASS);
	}
	tokens = realloc(tokens, sizeof(struct token)*(ntokens+1));
	tokens[ntokens++] = T;
}

static csaw_setup_terminals()
{
	int	i, j;
	chart_size = 0;
	for(i=0;i<ntokens;i++)
		if(tokens[i].to+1 > chart_size)chart_size = tokens[i].to+1;
	//fprintf(stderr, "loaded %d tokens ; chart_size = %d = 1+biggest 'to'\n", ntokens, chart_size);
	termprobs = malloc(sizeof(float*)*chart_size);
	for(i=0;i<chart_size;i++)
	{
		termprobs[i] = malloc(sizeof(float)*nterminals);
		for(j=0;j<nterminals;j++)
			termprobs[i][j] = ZERO_PROB;
	}
	mwefrom = calloc(sizeof(struct token*),chart_size);
	nmwefrom = calloc(sizeof(int),chart_size);
	mweto = calloc(sizeof(struct token*),chart_size);
	nmweto = calloc(sizeof(int),chart_size);
	for(i=0;i<ntokens;i++)
	{
		int	f = tokens[i].from;
		int	t = tokens[i].to;
		if(t==f+1)
			termprobs[f][tokens[i].term] = tokens[i].prob;
		else
		{
			mwefrom[f] = realloc(mwefrom[f], sizeof(struct token**)*(nmwefrom[f]+1));
			mwefrom[f][nmwefrom[f]] = &tokens[i];
			nmwefrom[f]++;
			mweto[t] = realloc(mweto[t], sizeof(struct token**)*(nmweto[t]+1));
			mweto[t][nmweto[t]] = &tokens[i];
			nmweto[t]++;
			//printf("MWE from %d to %d\n", tokens[i].from, tokens[i].to);
		}
	}
}

static csaw_setup_chart()
{
	chart = malloc(sizeof(float*)*chart_size*chart_size);
	startingAt = calloc(sizeof(char),chart_size*nnonterminals);
	endingAt = calloc(sizeof(char),chart_size*nnonterminals);
	int	l, from, to;
	for(from=0;from<chart_size-1;from++)
		for(to=from+1;to<=chart_size-1;to++)
		{
			chart[from*chart_size + to] = calloc(sizeof(float),nnonterminals);
			for(l=0;l<nnonterminals;l++)
				chart[from*chart_size+to][l] = ZERO_PROB;
			//printf("allocating %d - %d = %p\n", from, to, chart[from*chart_size + to]);
		}
}

void	csaw_free_chart()
{
	int from,to;
	for(from=0;from<chart_size-1;from++)
		for(to=from+1;to<=chart_size-1;to++)
			free(chart[from*chart_size+to]);
	free(chart);
	free(startingAt);
	free(endingAt);
	for(from=0;from<chart_size;from++)
	{
		if(mwefrom[from])free(mwefrom[from]);
		if(mweto[from])free(mweto[from]);
		free(termprobs[from]);
	}
	free(mwefrom);
	free(mweto);
	free(nmwefrom);
	free(nmweto);
	for(from=0;from<ntokens;from++)
		free(tokens[from].deriv);
	ntokens=0;
}

static inline float	READ_CHART(int	from, int	to, int	nt)
{
	if(nt<0)
	{
		if(to > from+1)
		{
			int i;
			for(i=0;i<nmwefrom[from];i++)
			{
				struct token	*t = mwefrom[from][i];
				if(t->to==to && t->term==(-1-nt))
					return t->prob;
			}
			return ZERO_PROB;
		}
		else return termprobs[from][-1-nt];
	}
	//printf("read %d - %d / %d\n", from, to, nt);
	//fflush(stdout);
	return chart[from*chart_size + to][nt];
}

static inline void WRITE_CHART(int	from, int	to, int	nt, float	p)
{
	assert(nt>=0);
	//printf("chart cell %p\n", chart[from*chart_size + to]);
	//fflush(stdout);
	assert(nt>=0 && nt<nnonterminals);
	float	old = chart[from*chart_size + to][nt];
	if(p>old)
	{
		//printf("write %d - %d / %d = %s = %g\n", from, to, nt, nonterminals[nt], p);
		//if(from=0 && to==3 && nt==159)assert(!"not reached");
		chart[from*chart_size + to][nt] = p;
		if(old==ZERO_PROB)
		{
			startingAt[from*nnonterminals + nt] = 1;
			endingAt[to*nnonterminals + nt] = 1;
			nonzeros++;
		}
		increases++;
	}
}

static csaw_prune_beam(int	from, int	to, const float	beam_width)
{
	int	i;
	float	max=ZERO_PROB, *cell = chart[from*chart_size+to];
	for(i=0;i<nnonterminals;i++)
		if(cell[i]>max)max=cell[i];
	float	thresh = max-beam_width;
	for(i=0;i<nnonterminals;i++)
		if(cell[i]<thresh)cell[i] = ZERO_PROB;
}

static void apply_branching_rule(int	from, int	to, struct rule	*r, int	dfrom, int	dtr, float	p)
{
	if(p==ZERO_PROB)return;
	/*if(dtr)
		printf("how about %d -> %d %d ... from %d - %d? p = %f after %d dtrs\n",
			r->lhs, r->rhs[0], r->rhs[1], from, to, p, dtr);*/
	if(dtr+1 == r->arity)
	{
		p = COMBINE_PROB(p, READ_CHART(dfrom, to, r->rhs[dtr]));
		WRITE_CHART(from, to, r->lhs, p);
		return;
	}
	int	mid;
	for(mid=dfrom+1;mid<to;mid++)
		apply_branching_rule(from, to, r, mid, dtr+1, COMBINE_PROB(p, READ_CHART(from, mid, r->rhs[dtr])));
}

static void apply_unary_rules(int	from, int	to)
{
	int	i, j;
	// rhs[0] could be an ordinary terminal
	if(to == from+1)
	{
		for(j=0;j<nterminals;j++)
		{
			float	tp = termprobs[from][j];
			if(tp == ZERO_PROB)continue;
			struct ruleset	*rs = &u_rules_for_term[j];
			for(i=0;i<rs->nrules;i++)
			{
				float	p = rs->rules[i].p;
				p = COMBINE_PROB(p, tp);
				WRITE_CHART(from, to, rs->rules[i].lhs, p);
			}
		}
	}
	// rhs[0] could be a MWE
	for(j=0;j<nmwefrom[from];j++)
	{
		struct token	*mwe = mwefrom[from][j];
		if(mwe->to == to)
		{
			struct ruleset	*rs = &u_rules_for_term[mwe->term];
			for(i=0;i<rs->nrules;i++)
				WRITE_CHART(from, to, rs->rules[i].lhs, COMBINE_PROB(rs->rules[i].p, mwe->prob));
		}
	}
	// rhs[0] could be a nonterminal
	for(j=0;j<nnonterminals;j++)
	{
		float	dp = READ_CHART(from, to, j);
		if(dp == ZERO_PROB)continue;
		struct ruleset	*rs = &u_rules_for_nonterm[j];
		for(i=0;i<rs->nrules;i++)
		{
			float	p = rs->rules[i].p;
			p = COMBINE_PROB(p, dp);
			WRITE_CHART(from, to, rs->rules[i].lhs, p);
		}
	}
}

static void apply_binary_rules(int	from, int	to)
{
	int	i, j;
	// rhs[0] could be an ordinary terminal
	for(j=0;j<nterminals;j++)
	{
		float	tp = termprobs[from][j];
		if(tp == ZERO_PROB)continue;
		struct ruleset	*rs = &b_rules_for_term[j];
		for(i=0;i<rs->nrules;i++)
		{
			float	r1p = READ_CHART(from+1, to, rs->rules[i].rhs[1]);
			if(r1p == ZERO_PROB)continue;
			float	p = rs->rules[i].p;
			p = COMBINE_PROB(p, tp);
			p = COMBINE_PROB(p, r1p);
			WRITE_CHART(from, to, rs->rules[i].lhs, p);
		}
	}
	// rhs[0] could be a MWE
	for(j=0;j<nmwefrom[from];j++)
	{
		struct token	*mwe = mwefrom[from][j];
		if(mwe->to < to)
		{
			struct ruleset	*rs = &b_rules_for_term[mwe->term];
			for(i=0;i<rs->nrules;i++)
				apply_branching_rule(from, to, &rs->rules[i], mwe->to, 1, COMBINE_PROB(rs->rules[i].p, mwe->prob));
		}
	}
	// rhs[0] could be a nonterminal
	for(j=0;j<nnonterminals;j++)
	{
		if(!startingAt[from*nnonterminals + j])continue;
		struct ruleset	*rs = &b_rules_for_nonterm[j];
		for(i=0;i<rs->nrules;i++)
		{
			int	rhs0 = j, rhs1 = rs->rules[i].rhs[1], lhs = rs->rules[i].lhs;
			float	rp = rs->rules[i].p;
			if(rhs1>=0)
			{
				// two nonterminals
				if(!endingAt[to*nnonterminals + rhs1])continue;
				int	mid;
				for(mid=from+1;mid<to;mid++)
				{
					float	r0p = READ_CHART(from, mid, rhs0);
					if(r0p == ZERO_PROB)continue;
					float	r1p = READ_CHART(mid, to, rhs1);
					if(r1p == ZERO_PROB)continue;
					float	p = rp;
					p = COMBINE_PROB(p, r0p);
					p = COMBINE_PROB(p, r1p);
					WRITE_CHART(from, to, lhs, p);
				}
			}
			else
			{
				// rhs[0] is nonterminal, but rhs[1] is terminal
				// might be a single-word terminal
				float	mx = COMBINE_PROB(COMBINE_PROB(rp, READ_CHART(from,to-1,rhs0)), READ_CHART(to-1,to,rhs1));
				int k;
				// might be a MWE
				for(k=0;k<nmweto[to];k++)
				{
					struct token	*mwe = mweto[to][k];
					if(mwe->term != rhs1)continue;
					if(mwe->from <= from)continue;
					float	p = COMBINE_PROB(COMBINE_PROB(rp, READ_CHART(from,mwe->from,rhs0)), mwe->prob);
					if(p>mx)mx=p;
				}
				if(mx>ZERO_PROB)WRITE_CHART(from,to,lhs,mx);
			}
		}
	}
}

static void apply_higher_rules(int	from, int	to)
{
	int	i, j;
	// rhs[0] could be an ordinary terminal
	for(j=0;j<nterminals;j++)
	{
		float	tp = termprobs[from][j];
		if(tp == ZERO_PROB)continue;
		struct ruleset	*rs = &h_rules_for_term[j];
		for(i=0;i<rs->nrules;i++)
			apply_branching_rule(from, to, &rs->rules[i], from+1, 1, COMBINE_PROB(rs->rules[i].p, tp));
	}
	// rhs[0] could be a MWE
	for(j=0;j<nmwefrom[from];j++)
	{
		struct token	*mwe = mwefrom[from][j];
		if(mwe->to < to)
		{
			struct ruleset	*rs = &h_rules_for_term[mwe->term];
			for(i=0;i<rs->nrules;i++)
				apply_branching_rule(from, to, &rs->rules[i], mwe->to, 1, COMBINE_PROB(rs->rules[i].p, mwe->prob));
		}
	}
	// rhs[0] could be a nonterminal
	for(j=0;j<nnonterminals;j++)
	{
		if(!startingAt[from*nnonterminals + j])continue;
		struct ruleset	*rs = &h_rules_for_nonterm[j];
		for(i=0;i<rs->nrules;i++)
			apply_branching_rule(from, to, &rs->rules[i], from, 0, rs->rules[i].p);
	}
}

static int csaw_reconstruct_one(int	from, int	to, struct rule	*r, int	dtr, int	*left, float	pmatch, float	psofar, int (*dprintf)(const char*,...))
{
	left[dtr] = from;
	if(dtr+1==r->arity)
	{
		double	this_p = READ_CHART(from, to, r->rhs[dtr]);
		psofar = COMBINE_PROB(psofar, this_p);
		if(psofar != pmatch)return 0;
		int i;
		for(i=0;i+1<r->arity;i++)
		{
			if(i)dprintf(" ");
			csaw_reconstruct(left[i],left[i+1],r->rhs[i], dprintf);
		}
		if(r->arity>1)dprintf(" ");
		csaw_reconstruct(left[r->arity-1], to, r->rhs[r->arity-1], dprintf);
		return 1;
	}
	int mid;
	for(mid=from+1;mid<to;mid++)
	{
		double	this_p = READ_CHART(from, mid, r->rhs[dtr]);
		if(csaw_reconstruct_one(mid, to, r, dtr+1, left, pmatch, COMBINE_PROB(psofar, this_p), dprintf))
			return 1;
	}
	return 0;
}

static int csaw_reconstruct(int	from, int	to, int	lhs, int (*dprintf)(const char*,...))
{
	int	i;
	if(lhs<0)
	{
		//dprintf("%s", terminals[-1-lhs]);
		// a token. go find it.
		for(i=0;i<ntokens;i++)
			if(tokens[i].from == from && tokens[i].to == to && tokens[i].term == -1-lhs)
			{
				dprintf("%s", tokens[i].deriv);
				break;
			}
		if(i==ntokens)dprintf("(missing-token %s)", terminals[-1-lhs]);
		return 0;
	}
	float	p = READ_CHART(from,to,lhs);
	//printf("pretty sure %d - %d is %s with p %f\n", from, to, nonterminals[lhs], p);
	if(lhs != start_symbol)
	{
		char	*sl = strrchr(nonterminals[lhs], '/');
		char	*label = nonterminals[lhs];
		if(sl)label = sl+1;
		static int edge_id_gen = 1;
		dprintf("(%d %s %f %d %d ", edge_id_gen++, label, p, from, to);
	}
	for(i=0;i<nrules;i++)
	{
		struct rule	*r = &rules[i];
		int	left[r->arity];
		if(r->lhs != lhs)continue;
		if(csaw_reconstruct_one(from, to, r, 0, left, p, r->p, dprintf))break;
	}
	if(i==nrules)
	{
		fprintf(stderr, "FAILED to reconstruct [%d %d %s %g]\n", from, to, nonterminals[lhs], p);
	}
	if(lhs != start_symbol)dprintf(")");
}

struct unpacker
{
	int	from, to, nonterminal;
	struct tree	**trees;
	int			ntrees;
	struct usplit
	{
		float	score;
		int		rule;
		int		*from;
		int		*idx;
	}	*splits;
	int	nsplits;
};

static struct hash	*unpack_hash;
static struct unpacker	**unpackers;
static int				nunpackers;

static int edge_id_gen = 1;

static void	init_unpackers()
{
	unpack_hash = hash_new("unpack");
	edge_id_gen = 1;
}

static void	free_unpackers()
{
	int i;
	for(i=0;i<nunpackers;i++)
	{
		struct unpacker	*u = unpackers[i];
		int j;
		for(j=0;j<u->nsplits;j++)
		{
			free(u->splits[j].from);
			free(u->splits[j].idx);
		}
		free(u->splits);
		free(u->trees);
	}
	hash_free(unpack_hash);
}

static int	usplitcmp(const void *a, const void *b)
{
	const struct usplit *x = a, *y = b;
	if(x->score > y->score)return -1;
	if(x->score < y->score)return 1;
	return 0;
}

static sort_splits(struct unpacker	*u)
{
	qsort(u->splits, u->nsplits, sizeof(struct usplit), usplitcmp);
}

static void visit_local_reconstructions1(int	rid, struct rule	*r, int	*from, int	to, int	n, float	p, void	(*visitor)(float,int,int*))
{
	if(n==r->arity)visitor(p, rid, from);
	else
	{
		if(from[n]>=to)return;	// no room
		if(n+1 != r->arity)
		{
			int	mid;
			// consider all possible widths for next daughter
			for(mid=from[n]+1;mid<=to;mid++)
			{
				float	rp = READ_CHART(from[n], mid, r->rhs[n]);
				if(rp == ZERO_PROB)continue;
				from[n+1] = mid;
				visit_local_reconstructions1(rid, r, from, to, n+1, COMBINE_PROB(p, rp), visitor);
			}
		}
		else
		{
			// next daughter has known width
			float	rp = READ_CHART(from[n], to, r->rhs[n]);
			if(rp == ZERO_PROB)return;
			visit_local_reconstructions1(rid, r, from, to, n+1, COMBINE_PROB(p, rp), visitor);
		}
	}
}

static void visit_local_reconstructions(int	from, int to, int	x, void (*visitor)(float,int,int*))
{
	int i;
	assert(x>=0);
	for(i=0;i<nrules;i++)
	{
		if(rules[i].lhs != x)continue;
		int	_from[rules[i].arity+1];
		_from[0] = from;
		visit_local_reconstructions1(i, &rules[i], _from, to, 0, rules[i].p, visitor);
	}
}

static struct unpacker	*get_unpacker(int	from, int	to, int	nonterminal)
{
	char	key[1024];
	sprintf(key, "%d %d %d", from, to, nonterminal);
	struct unpacker	*u = hash_find(unpack_hash, key);
	if(u)return u;
	u = calloc(sizeof(*u),1);
	hash_add(unpack_hash, strdup(key), u);
	u->from = from;
	u->to = to;
	u->nonterminal = nonterminal;
	//float	best = READ_CHART(from, to, nonterminal);
	if(nonterminal >= 0)
	{
		void visitor(float	score, int	rule, int	*from)
		{
			u->nsplits++;
			u->splits = realloc(u->splits, sizeof(struct usplit)*u->nsplits);
			struct usplit	*s = &u->splits[u->nsplits-1];
			s->score = score;
			s->rule = rule;
			s->from = malloc(sizeof(int)*rules[rule].arity);
			memcpy(s->from, from, sizeof(int)*rules[rule].arity);
			s->idx = calloc(sizeof(int),rules[rule].arity);
		}
		visit_local_reconstructions(from, to, nonterminal, visitor);
		sort_splits(u);
	}
	else
	{
	}
	return u;
}

static float	nth_score(struct unpacker	*u, int	n)
{
	if(u->ntrees>n)return u->trees[n]->score;
	assert(u->ntrees==n);
	if(u->nonterminal >= 0)
		return u->splits[0].score;
	else
	{
		if(n==0) return READ_CHART(u->from, u->to, u->nonterminal);
		else return ZERO_PROB;
	}
}

static void enforce_token_span(struct tree	*t, int	from, int	to)
{
	t->tfrom = from;
	t->tto = to;
	assert(t->ndaughters<=1);
	if(t->ndaughters)enforce_token_span(t->daughters[0], from, to);
}

static struct tree	*unpack(struct unpacker	*u, int	n)
{
	if(u->ntrees>n)return u->trees[n];
	assert(u->ntrees==n);
	struct tree	*t = slab_alloc(sizeof(struct tree));
	bzero(t,sizeof(*t));
	t->tfrom = u->from;
	t->tto = u->to;
	if(u->nonterminal >= 0)
	{
		nextsplit:
		if(u->nsplits == 0)return NULL;
		assert(u->nsplits > 0);
		// dequeue this split and make room for more splits
		struct usplit	S = u->splits[0];
		struct rule	*r = rules + S.rule;
		u->nsplits--;
		memmove(u->splits, u->splits+1, sizeof(struct usplit)*u->nsplits);
		u->splits = realloc(u->splits, sizeof(struct usplit)*(u->nsplits + r->arity));
		// build the tree
		char	*sl = strrchr(nonterminals[u->nonterminal], '/');
		char	*label = nonterminals[u->nonterminal];
		if(sl)label = sl+1;
		t->label = label;
		t->edge_id = edge_id_gen++;
		t->daughters = slab_alloc(sizeof(struct tree*)*r->arity);
		t->ndaughters = r->arity;
		t->score = S.score;
		int i, allgood = 1, prevnsplits = u->nsplits;
		for(i=0;i<r->arity;i++)
		{
			// subtree
			struct unpacker	*subu = get_unpacker(S.from[i], (i+1==r->arity)?u->to:S.from[i+1], r->rhs[i]);
			t->daughters[i] = unpack(subu, S.idx[i]);
			if(!t->daughters[i])allgood = 0;
			// new split where this subtree's index is incremented
			struct usplit	*s = &u->splits[u->nsplits];
			*s = S;
			s->idx = malloc(sizeof(int)*r->arity);
			memcpy(s->idx, S.idx, sizeof(int)*r->arity);
			// offset the score
			s->score -= nth_score(subu, s->idx[i]);
			s->idx[i]++;
			s->score += nth_score(subu, s->idx[i]);
			if(!isinf(s->score) && s->score != ZERO_PROB)u->nsplits++;
		}
		if(allgood)sort_splits(u);
		else
		{
			u->nsplits = prevnsplits;
			goto nextsplit;
		}
	}
	else
	{
		if(n>0)return NULL;
		int i;
		for(i=0;i<ntokens;i++) if(tokens[i].from == u->from && tokens[i].to == u->to && tokens[i].term == -1-u->nonterminal)break;
		assert(i<ntokens);
		t = string_to_tree(strdup(tokens[i].deriv));
		//t->label = terminals[-1-u->nonterminal];
		t->score = READ_CHART(u->from, u->to, u->nonterminal);
		enforce_token_span(t, u->from, u->to);
		//t->edge_id = edge_id_gen++;
	}
	u->ntrees++;
	u->trees = realloc(u->trees, sizeof(struct tree*)*u->ntrees);
	u->trees[u->ntrees-1] = t;
	return t;
}

static float	beam_width = 0;

void	csaw_parse_these_tokens(int	nbest, void (*visitor)(struct tree	*t))
{
	start_timer(ctimer);

	csaw_setup_terminals();
	csaw_setup_chart();
	if(chart_size<=0)return;
	int	l, from, to;
	for(l=1;l<=chart_size-1;l++)
	{
		for(from=0;from<=chart_size-1-l;from++)
		{
			to = from+l;
			if(l>1)
			{
				start_timer(binarytimer);
				apply_binary_rules(from,to);
				stop_timer(binarytimer,1);
				start_timer(highertimer);
				apply_higher_rules(from,to);
				stop_timer(highertimer,1);
			}
			start_timer(unarytimer);
			apply_unary_rules(from,to);
			apply_unary_rules(from,to);
			apply_unary_rules(from,to);
			apply_unary_rules(from,to);
			apply_unary_rules(from,to);
			stop_timer(unarytimer,5);
			if(l && beam_width)csaw_prune_beam(from, to, beam_width);
		}
	}

	stop_timer(ctimer,1);
	start_timer(utimer);

	double	p = READ_CHART(0, chart_size-1, start_symbol);
	//fprintf(stderr, "P(start) = %g\n", p);

	//char	*derivation = malloc(10240);
	//int		dalen = 10240, dlen = 0;
	//*derivation = 0;

	if(p > ZERO_PROB)
	{
		/*int	dprintf(const char	*fmt, ...)
		{
			va_list	v;
			va_start(v, fmt);
			int	l = vsnprintf(derivation+dlen, dalen-dlen, fmt, v);
			va_end(v);
			if(l >= dalen-dlen)
			{
				va_list v2;
				va_start(v2, fmt);
				dalen += l + 10240 ;
				derivation = realloc(derivation, dalen);
				l = vsnprintf(derivation+dlen, dalen-dlen, fmt, v2);
				va_end(v2);
			}
			dlen += l;
			return l;
		}
		csaw_reconstruct(0, chart_size-1, start_symbol, dprintf);*/

		init_unpackers();
		struct unpacker	*u = get_unpacker(0, chart_size-1, start_symbol);
		int k;
		for(k=0;k<nbest;k++)
		{
			struct tree	*t = unpack(u, k);
			if(!t)break;
			assert(!strcmp(t->label, "TOP"));
			visitor(t->daughters[0]);
		}
		free_unpackers();
	}

	stop_timer(utimer, 1);
	//if(p!=ZERO_PROB)return derivation;;
	//free(derivation);
	//return NULL;
}
