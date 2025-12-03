#include	<math.h>
#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

#include	"tree.h"

struct string
{
	int		nwords;
	char	**words;
};

struct sr_trace
{
	int	nactions;
	struct sr_action
	{
		char	*shift, *reduce;
		int		nreduce;

		int	count;
	}	*actions;
};


#define	CONTEXT_STACK_SIZE	2
#define	CONTEXT_LOOKAHEAD_SIZE	2

struct sr_context
{
	char	*stack[CONTEXT_STACK_SIZE];
	char	*lookahead[CONTEXT_LOOKAHEAD_SIZE];

	int					nactions, count;
	struct sr_action	*actions;

	struct sr_action	*best_action;
};

struct sr_context_set
{
	int					ncontexts;
	struct sr_context	**contexts;
};

struct sr_mistakes
{
	int	total_actions;
	int	correct_actions;
	int second_best_actions;
};

char	*trim_string(char	*str);

struct string	*extract_string(struct tree	*t)
{
	if(t->ndaughters==0)
	{
		struct string	*s = malloc(sizeof(struct string));
		s->nwords = 1;
		s->words = malloc(sizeof(char*)*1);
		s->words[0] = strtok(t->label, " ");
		char	*p;
		while(p = strtok(NULL, " "))
		{
			s->nwords++;
			s->words = realloc(s->words, sizeof(char*)*s->nwords);
			s->words[s->nwords-1] = p;
		}
		return s;
	}
	if(t->ndaughters==1)
		return extract_string(t->daughters[0]);

	struct string	*s = calloc(sizeof(struct string),1);
	int i;
	for(i=0;i<t->ndaughters;i++)
	{
		struct string	*ds = extract_string(t->daughters[i]);
		int	onw = s->nwords, i;
		s->nwords += ds->nwords;
		s->words = realloc(s->words, sizeof(char*)*s->nwords);
		for(i=0;i<ds->nwords;i++)
			s->words[onw+i] = ds->words[i];
		free(ds->words);
		free(ds);
	}
	return s;
}

struct tree	*read_tree(FILE	*f)
{
	char	line[102400];
	if(!fgets(line, 102399, f))return NULL;

	char	*s = trim_string(line);
	return string_to_tree(s);
}

extract_sr_trace(struct tree	*t, struct sr_trace	*sr)
{
	int i;
	if(t->ndaughters && !(t->ndaughters==1 && t->daughters[0]->ndaughters==0))
	{
		for(i=0;i<t->ndaughters;i++)
			extract_sr_trace(t->daughters[i], sr);
		//for(i=0;i<indent;i++)printf("  ");
		//printf("reduce(%d, %s)\n", t->ndaughters, t->label);
		struct sr_action	act;
		act.reduce = t->label;
		act.nreduce = t->ndaughters;
		act.shift = NULL;
		sr->nactions++;
		sr->actions = realloc(sr->actions, sizeof(struct sr_action)*sr->nactions);
		sr->actions[sr->nactions-1] = act;
	}
	else
	{
		struct sr_action	act;
		act.reduce = NULL;
		act.nreduce = 0;
		act.shift = t->label;
		sr->nactions++;
		sr->actions = realloc(sr->actions, sizeof(struct sr_action)*sr->nactions);
		sr->actions[sr->nactions-1] = act;
		//for(i=0;i<indent;i++)printf("  ");
		//printf("shift(%s)\n", t->label);
	}
}

int	sr_compare_contexts(const struct sr_context	*a, const struct sr_context	*b)
{
	int	i, r;
	for(i=0;i<CONTEXT_STACK_SIZE;i++)
		if( (r=strcmp(a->stack[i], b->stack[i])) )return r;
	for(i=0;i<CONTEXT_LOOKAHEAD_SIZE;i++)
		if( (r=strcmp(a->lookahead[i], b->lookahead[i])) )return r;
	return 0;
}

struct sr_context	*sr_find_context(struct sr_context_set	*cs, char	*_stack[], int	nstack, struct string	*surf, int	surfp, int	add_if_missing)
{
	struct sr_context	C;
	int		i, j;

	for(i=0;i<CONTEXT_STACK_SIZE;i++)
		C.stack[i] = (nstack-1-i >= 0)?_stack[nstack-1-i]:"^";
	for(i=0;i<CONTEXT_LOOKAHEAD_SIZE;i++)
		C.lookahead[i] = (surf->nwords>(surfp+i))?surf->words[surfp+i]:"$";
	C.nactions = 0;
	C.actions = NULL;
	C.count = 0;

	for(i=0;i<cs->ncontexts;i++)
		if(sr_compare_contexts(&C, cs->contexts[i]) == 0)break;
	if(i==cs->ncontexts)
	{
		if(!add_if_missing)return NULL;
		cs->ncontexts++;
		cs->contexts = realloc(cs->contexts, sizeof(struct sr_context*)*cs->ncontexts);
		cs->contexts[cs->ncontexts-1] = malloc(sizeof(C));
		*(cs->contexts[cs->ncontexts-1]) = C;
	}
	return cs->contexts[i];
}

int	sr_compare_actions(const struct sr_action	*a, const struct sr_action	*b)
{
	int	r;
	if(a->shift && !b->shift)return 1;
	if(b->shift && !a->shift)return -1;
	if(a->shift && (r=strcmp(a->shift, b->shift)))return r;
	if(a->reduce && (r=strcmp(a->reduce, b->reduce)))return r;
	return a->nreduce - b->nreduce;
}

struct sr_action	*sr_context_find_action(struct sr_context	*ctx, struct sr_action	*_act)
{
	int	i;
	for(i=0;i<ctx->nactions;i++)
		if(sr_compare_actions(_act, &ctx->actions[i]) == 0)break;
	if(i==ctx->nactions)
	{
		ctx->nactions++;
		ctx->actions = realloc(ctx->actions, sizeof(struct sr_action)*ctx->nactions);
		ctx->actions[ctx->nactions-1] = *_act;
		ctx->actions[ctx->nactions-1].count = 0;
	}
	return &ctx->actions[i];
}

print_string(struct string	*s)
{
	int i;
	for(i=0;i<s->nwords;i++)printf("%s ", s->words[i]);
}

#define	CONTEXT_METRIC_ZERO			0.005
#define	CONTEXT_METRIC_THRESHOLD	2.5
#define	CONTEXT_METRIC_LOOKAHEAD_WEIGHT	1.0
#define CONTEXT_METRIC_STACK_WEIGHT	2.0

float	sr_contexts_metric(const struct sr_context	*a, const struct sr_context	*b)
{
	int	i;
	float	d = CONTEXT_METRIC_ZERO;
	for(i=0;i<CONTEXT_STACK_SIZE;i++)
		if(strcmp(a->stack[i], b->stack[i]))d += CONTEXT_METRIC_STACK_WEIGHT;
	for(i=0;i<CONTEXT_LOOKAHEAD_SIZE;i++)
		if(strcmp(a->lookahead[i], b->lookahead[i]))d += CONTEXT_METRIC_LOOKAHEAD_WEIGHT;
	return d;
}

struct sr_action	sr_oracle(struct sr_context_set	*cs, char	*_stack[], int	nstack, struct string	*surf, int	surfp, struct sr_action	*second_best)
{
	struct sr_context	C;
	int		i, j;

	for(i=0;i<CONTEXT_STACK_SIZE;i++)
		C.stack[i] = (nstack-1-i >= 0)?_stack[nstack-1-i]:"^";
	for(i=0;i<CONTEXT_LOOKAHEAD_SIZE;i++)
		C.lookahead[i] = (surf->nwords>(surfp+i))?surf->words[surfp+i]:"$";
	C.nactions = 0;
	C.actions = NULL;
	C.count = 0;

	for(i=0;i<cs->ncontexts;i++)
	{
		struct sr_context	*ctx = cs->contexts[i];
		float	d = sr_contexts_metric(&C, ctx);
		if(d > CONTEXT_METRIC_THRESHOLD)continue;
		if(d > 0.1)
		{
			//print_context(ctx);
			//printf(" is distance %f to test context\n", d);
			//print_context(&C);
		}
		int j;
		for(j=0;j<ctx->nactions;j++)
		{
			struct sr_action	act = ctx->actions[j];
			// this context contributes (act.count * 100.0 / d) votes for 'act'
			if(act.shift) act.shift = C.lookahead[0];
			struct sr_action	*cact = sr_context_find_action(&C, &act);
			cact->count += act.count * 100.0 / ctx->count / (d);
		}
	}

	struct sr_action	best_action = {.reduce=NULL,.shift=C.lookahead[0],.nreduce=0,.count=0};
	struct sr_action	second_action = {.reduce=NULL,.shift=C.lookahead[0],.nreduce=0,.count=0};
	for(i=0;i<C.nactions;i++)
	{
		if(C.actions[i].count > best_action.count)
		{
			second_action = best_action;
			best_action = C.actions[i];
		}
	}
	free(C.actions);
	if(second_best)*second_best = second_action;
	return best_action;
}

simulate_parse(struct sr_trace	*sr, struct string	*surf, struct sr_context_set	*cs, struct sr_mistakes	*mistakes)
{
	int		nstack = 0;
	char	*stack[1000];

	int	actp = 0, surfp = 0;

	for(actp = 0;actp < sr->nactions;actp++)
	{
		struct sr_action	*act = sr->actions+actp;
		char				*lookahead = (surfp<surf->nwords)?surf->words[surfp]:"$";

		if(!mistakes)
		{
			// record the action taken into the sr_context_set
			struct sr_context	*ctx = sr_find_context(cs, stack, nstack, surf, surfp, 1);
			struct sr_action	*ctx_act = sr_context_find_action(ctx, act);
			ctx_act->count++;
			ctx->count++;
		}
		else
		{
			// see if we would have predicted the action
			struct sr_action	second_best, predict = sr_oracle(cs, stack, nstack, surf, surfp, &second_best);
			if(sr_compare_actions(act, &predict) == 0)
				mistakes->correct_actions++;
			else if(sr_compare_actions(act, &second_best) == 0)
				mistakes->second_best_actions++;
			mistakes->total_actions++;
		}

		//printf("[%s] ", lookahead);
		//int i;
		//for(i=0;i<nstack;i++)if(i>=nstack-2)printf("%s ", stack[i]);
		//printf("%s %s %s ", (nstack>0)?stack[nstack-1]:"^", lookahead, (nstack>1)?stack[nstack-2]:"^");
		if(act->shift)
		{
			//printf("shift(%s)\n", act->shift);
			stack[nstack++] = act->shift;
			surfp++;
		}
		else
		{
			//printf("reduce(%d, %s)\n", act->nreduce, act->reduce);
			nstack -= act->nreduce;
			stack[nstack++] = act->reduce;
		}
	}
}

print_context(struct sr_context	*ctx)
{
	int	i;
	printf("%d	", ctx->count);
	for(i=0;i<CONTEXT_STACK_SIZE;i++)
		printf(" %s", ctx->stack[i]);
	printf(" .");
	for(i=0;i<CONTEXT_LOOKAHEAD_SIZE;i++)
		printf(" %s", ctx->lookahead[i]);
	printf("\n");
	for(i=0;i<ctx->nactions;i++)
	{
		struct sr_action	*act = &ctx->actions[i];
		printf("	%d	", act->count);
		if(act->shift)printf("shift(%s)\n", act->shift);
		else printf("reduce(%d,%s)\n", act->nreduce, act->reduce);
	}
}

print_context_set(struct sr_context_set	*cs)
{
	int	i;
	for(i=0;i<cs->ncontexts;i++)
		print_context(cs->contexts[i]);
}

struct sr_mistakes	pick_best_actions(struct sr_context_set	*cs)
{
	int	total_actions = 0, best_actions = 0, i, j;
	for(i=0;i<cs->ncontexts;i++)
	{
		struct sr_context	*ctx = cs->contexts[i];
		int	most = 0, jmost = 0;
		total_actions += ctx->count;
		for(j=0;j<ctx->nactions;j++)
		{
			struct sr_action	*act = &ctx->actions[j];
			if(act->count > most) { most = act->count; jmost = j; }
		}
		ctx->best_action = &ctx->actions[jmost];
		best_actions += most;
	}
	struct sr_mistakes	mistakes;
	mistakes.total_actions = total_actions;
	mistakes.correct_actions = best_actions;
	return mistakes;
}

struct sr_context_set	*train_on_trees(struct tree	**trees, int	count)
{
	int	i;
	struct sr_context_set	*cs = calloc(sizeof(*cs),1);
	for(i=0;i<count;i++)
	{
		struct string	*s = extract_string(trees[i]);
		struct sr_trace	*sr = calloc(sizeof(struct sr_trace),1);
		extract_sr_trace(trees[i], sr);
		simulate_parse(sr, s, cs, NULL);
	}

	struct sr_mistakes	training_accuracy = pick_best_actions(cs);
	printf("in training on %d trees, of %d actions total, %d could be predicted from context = %.1f%%\n", count, training_accuracy.total_actions, training_accuracy.correct_actions, 100*(float)training_accuracy.correct_actions/training_accuracy.total_actions);
	return cs;
}

struct sr_mistakes	test_on_trees(struct sr_context_set	*cs, struct tree	**trees, int	count)
{
	int	i;
	struct sr_mistakes	mistakes;
	bzero(&mistakes, sizeof(mistakes));
	for(i=0;i<count;i++)
	{
		struct string	*s = extract_string(trees[i]);
		struct sr_trace	*sr = calloc(sizeof(struct sr_trace),1);
		extract_sr_trace(trees[i], sr);
		simulate_parse(sr, s, cs, &mistakes);
	}

	printf("in testing on %d trees, of %d actions total, %d could be predicted from context = %.1f%%\n", count, mistakes.total_actions, (mistakes.correct_actions), 100*(float)(mistakes.correct_actions)/mistakes.total_actions);
	printf("	a further %d times, our second guess was right  = %.1f%%\n", mistakes.second_best_actions, 100*(float)(mistakes.second_best_actions)/mistakes.total_actions);
	return mistakes;
}

struct sr_trace	*oracle_trace;

int	parsing_oracle(int	step, char	**reduce, char	**shift)
{
	if(oracle_trace->nactions <= step)
	{
		*reduce = NULL;
		*shift = NULL;
		if(oracle_trace->nactions < step)	// don't complain if trying to figure out whether to reduce a root edge
			fprintf(stderr, "oh no, asked oracle for steps[%d] but we were supposed to have %d\n", step, oracle_trace->nactions);
		return -1;
	}
	struct sr_action	*act = oracle_trace->actions+step;
	*reduce = act->reduce;
	*shift = act->shift;
	//printf("parsing ORACLE says shift = %s, reduce = %s\n", *shift, *reduce);
	return 0;
}

void	treebank_control()
{
	struct tree	**trees = NULL;
	int			ntrees = 0;
	int i;

	while(1)
	{
		struct tree	*t = read_tree(stdin);
		if(!t)break;
		ntrees++;
		trees = realloc(trees, sizeof(struct tree*)*ntrees);
		trees[ntrees-1] = t;
	}

	printf("%d trees total\n", ntrees);

	for(i=0;i<ntrees && i < 10;i++)
	{
		struct tree	*T = trees[i];
		struct string	*S = extract_string(T);
		struct sr_trace	*sr = calloc(sizeof(struct sr_trace),1);
		extract_sr_trace(T, sr);

		printf("trying sentence:  "); print_string(S); printf("\n");
		printf("correct tree:\n"); print_tree(T, 0);
		oracle_trace = sr;
		parse(S->nwords, S->words, S->words, "(not supported)");
	}
	return;

	// mix them up in random order
	srand(time(0));
	for(i=0;i<ntrees;i++)
	{
		int	j = rand()%ntrees;
		struct tree	*tmp = trees[i];
		trees[i] = trees[j];
		trees[j] = tmp;
	}

	int	ntraining = ntrees * 0.75;
	struct tree	**training_trees = trees + 0;
	int	ntesting = ntrees - ntraining;
	struct tree	**testing_trees = trees + ntraining;

	struct sr_context_set	*cs = train_on_trees(training_trees, ntraining);
	//print_context_set(cs);

	test_on_trees(cs, testing_trees, ntesting);
}
