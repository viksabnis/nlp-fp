#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<math.h>

#include	"dag.h"
#include	"type.h"
#include	"lexicon.h"
#include	"chart.h"
#include	"hash.h"
#include	"rule-use-model.h"
#include	"lattice-mapping.h"

struct feat
{
	int	fno;
	char	*def;
	double	weight;
};

struct model
{
	int	nfeatures;
	struct feat	**feats;
	struct hash	*fhash;
	double	offset;
};

static struct feat	*build_feature(struct model	*m, char	*def, double	weight)
{
	struct feat	*f = calloc(sizeof(*f),1);
	f->fno = m->nfeatures++;
	f->def = strdup(def);
	f->weight = weight;
	//printf("new feature `%s' = %d\n", feat, f->fno);
	hash_add(m->fhash, f->def, f);
	m->feats = realloc(m->feats, sizeof(struct feat*) * m->nfeatures);
	m->feats[m->nfeatures-1] = f;
	return f;
}

struct model	*load_model(char	*model_fname)
{
	FILE	*f = fopen(model_fname, "r");
	if(!f){perror(model_fname);exit(-1);}

	double	weight;
	char	fname[1024];
	struct model	*m = calloc(sizeof(*m),1);
	m->fhash = hash_new(model_fname);
	while(2 == fscanf(f, "%lf	%[^\n]\n", &weight, fname))
	{
		if(!strcmp(fname, "offset"))
			m->offset = weight;
		else build_feature(m, fname, weight);
	}
	fclose(f);
	return m;
}

double	get_1weight(struct model	*m, char	*prefix, char	*lt)
{
	char	fname[256];
	sprintf(fname, "%s%s", prefix, lt);
	struct feat	*f = hash_find(m->fhash, fname);
	if(!f)return 0;
	else return f->weight;
}

// left[X] is the sum of all left: weights for lexemes ending at X or before
// right[X] is the sum of all right: weights for lexemes start at X or after
// in[X] is the sum of all in: weights for lexemes starting exactly at X
void	get_weights1(struct model	*m, int N, char	*lextype, int	from, int	to, double	*leftweights, double	*inweights, double	*rightweights)
{
	int i;
	for(i=0;i<=from;i++)
		leftweights[i] += get_1weight(m, "left:", lextype);
	inweights[i] += get_1weight(m, "in:", lextype);
	for(i=to;i<=N;i++)
		rightweights[i] += get_1weight(m, "right:", lextype);
}

void	get_weights(struct model	*m, int	N, struct lattice	*ll, double	*leftweights, double	*inweights, double	*rightweights)
{
	int	i;
	for(i=0;i<ll->nedges;i++)
	{
		struct edge	*e = ll->edges[i]->edge;
		if(e->have)continue;
		assert(e->lex);
		get_weights1(m, N, e->lex->lextype->name, e->from, e->to, leftweights, inweights, rightweights);
	}
}

static struct model	*xsb, *xcmp, *xajvp;
struct weightset
{
	double	*left, *in, *right;
}	xsbw, xcmpw, xajvpw;

reset_ws(struct weightset	*ws, int	N)
{
	if(ws->left)free(ws->left);
	if(ws->in)free(ws->in);
	if(ws->right)free(ws->right);
	ws->left = calloc(sizeof(double),N+1);
	ws->in = calloc(sizeof(double),N+1);
	ws->right = calloc(sizeof(double),N+1);
}

void	predict_rule_uses(int	N, struct lattice	*ll)
{
	return;
	//if(!xsb)xsb = load_model("/tmp/xsb-manual.mod");
	//if(!xsb)xsb = load_model("/tmp/xsb.mod");
	//assert(xsb);
	//if(!xcmp)xcmp = load_model("/tmp/xcmp.mod");
	//if(!xajvp)xajvp = load_model("/tmp/xajvp.mod");
	if(!xajvp)xajvp = load_model("/tmp/xaj-manual.mod");
	//assert(xsb && xcmp && xajvp);

	//reset_ws(&xsbw, N);
	//get_weights(xsb, N, ll, xsbw.left, xsbw.in, xsbw.right);
	//reset_ws(&xcmpw, N);
	//get_weights(xcmp, N, ll, xcmpw.left, xcmpw.in, xcmpw.right);
	reset_ws(&xajvpw, N);
	get_weights(xajvp, N, ll, xajvpw.left, xajvpw.in, xajvpw.right);
}

int	predict1(double	offset, struct weightset	*w, int	from, int	to, double	thresh)
{
	double	score = -offset + w->left[from] + w->right[to];
	int i;
	for(i=from;i<to;i++)score += w->in[i];
	double	P = 1.0 / (1.0 + exp(-score));
	//printf("score = %f ; p = %f ; offset = %f ; left = %f\n", score, P, offset, w->left[from]);
	if(P >= thresh)return 1;
	else return 0;
}

int	predict_1_rule_use(char	*rule, int	from, int	to)
{
	//if(!strcmp(rule, "hd_xsb-fin_c"))return predict1(xsb->offset, &xsbw, from, to, 0.01);
	//if(!strcmp(rule, "hd_xaj-int-vp_c"))return predict1(xajvp->offset, &xajvpw, from, to, 0.02);
	//if(!strcmp(rule, "hd_xcmp_c"))return predict1(xcmp->offset, &xcmpw, from, to, 0.01);
	return 1;
}
