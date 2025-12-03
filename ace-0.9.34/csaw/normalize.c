#include	<string.h>
#include	<stdlib.h>
#include	<assert.h>
#include	"../tree.h"

void	csaw_normalize_tree(struct tree	*t)
{
	if(t->ndaughters==0)return;
	int i;
	for(i=0;i<t->ndaughters;i++)
		csaw_normalize_tree(t->daughters[i]);
	if(strstr(t->label, "_plr"))
	{
		assert(t->ndaughters == 1);
		struct tree	*p = calloc(sizeof(struct tree),1);
		p->label = strdup("PUNCT");
		p->ntokens = 1;
		p->tokens = malloc(sizeof(char*));
		p->tokens[0]=strdup("PUNCT");
		struct tree	*pl = calloc(sizeof(struct tree),1);
		pl->label = strdup(t->label);
		pl->ndaughters = 1;
		pl->daughters = malloc(sizeof(struct tree*));
		pl->daughters[0] = p;
		t->ndaughters=2;
		t->daughters = realloc(t->daughters, sizeof(struct tree*)*2);
		t->daughters[1] = pl;
	}
}

void	csaw_denormalize_tree(struct tree	*t)
{
	if(t->ndaughters==0)return;
	if(strstr(t->label, "_plr"))
	{
		assert(t->ndaughters == 2);
		t->ndaughters = 1;
	}
	int i;
	for(i=0;i<t->ndaughters;i++)
		csaw_denormalize_tree(t->daughters[i]);
}
