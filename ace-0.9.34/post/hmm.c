#include	<math.h>
#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<assert.h>

#include	"words.h"
#include	"tags.h"


extern int	*train_words;
extern int	*train_tags;
extern int	train_total;
int					htags;

static struct hmm_state
{
	int		tag, prev;
	double	*pprob;
}	*states;
int	nstates;

// compute tag transition probabilities and word probabilities
void	build_hmm()
{
	int			i, j, k, count;
	struct tag	*t;
	double		*unigram, *bigram, *trigram;

	nstates = ntags*ntags;
	states = calloc(sizeof(struct hmm_state),nstates);
	for(i=0;i<ntags;i++)
		for(j=0;j<ntags;j++)
		{
			states[i*ntags+j].prev = i;
			states[i*ntags+j].tag = j;
			states[i*ntags+j].pprob = calloc(sizeof(double),ntags);
		}
	unigram = calloc(sizeof(double),ntags);
	bigram = calloc(sizeof(double),ntags*ntags);
	trigram = calloc(sizeof(double),ntags*ntags*ntags);
	for(i=2;i<train_total;i++)
	{
		unigram[train_tags[i]]++;
		bigram[train_tags[i] + train_tags[i-1]*ntags]++;
		trigram[train_tags[i] + train_tags[i-1]*ntags + train_tags[i-2]*ntags*ntags]++;
	}
	for(i=0;i<ntags;i++)
	{
		for(j=0;j<ntags;j++)
		{
			for(k=0;k<ntags;k++)
				trigram[k+j*ntags+i*ntags*ntags]
					/= bigram[j+i*ntags];
			bigram[j+i*ntags] /= unigram[i];
		}
		unigram[i] /= (train_total-2);
	}
	k = lookup_tag(".")->index;
	bigram[k+k*ntags] = 0;
	trigram[k+k*ntags+k*ntags*ntags] = 0;

	// use linear combination of trigram, bigram, unigram, and uniform distributions
	// to estimate hmm transitions
	for(i=0;i<ntags;i++)
		for(j=0;j<ntags;j++)
			for(k=0;k<ntags;k++)
			{
				// compute: given we were in [i,j],
				// what is the chance we go to [j,k]?
				if(trigram[k+j*ntags+i*ntags*ntags])
					states[j*ntags+k].pprob[i] = log(
						0.8*trigram[k+j*ntags+i*ntags*ntags]
					  + 0.1*bigram[k+j*ntags]
					  + 0.1*unigram[k]
					  + 0.0*(1.0 / ntags)   );
				else states[j*ntags+k].pprob[i] = log(
					    0.9*bigram[k+j*ntags]
					  + 0.07*unigram[k]
					  + 0.03*(1.0 / ntags)  );
			}

	for(i=0;i<ntags;i++)
		tags[i]->prob = log(unigram[i]);
	for(i=0;i<nwords;i++)
	{
		word_index[i]->tprob = calloc(sizeof(double), ntags);
		word_index[i]->nfreqs = ntags;
	}
	for(i=0;i<train_total;i++)
		word_index[train_words[i]]->tprob[train_tags[i]]++;
	k = lookup_tag("NNP")->index;
	// secretly pretend to have seen every word as a proper noun
	for(i=0;i<nwords;i++)
	{
		for(j=0;j<ntags;j++)
			word_index[i]->tprob[j] /= ((double)word_index[i]->count+0.2);
		word_index[i]->tprob[k] += 0.2 / ((double)word_index[i]->count+0.2);

		for(j=0;j<ntags;j++)
			word_index[i]->tprob[j] = log(word_index[i]->tprob[j]);
	}

	htags = ntags;
}

double	viterbi_decode(int	len, int	*words, int	*result)
{
	double	*mat, ptrans, pword, p, l0 = log(0);
	int		*back;
	int		i, j, k;

	if(!len)return 0;
	back = calloc(sizeof(int), nstates * len);
	mat = calloc(sizeof(double), nstates * len);

	// trick:
	// P(w|tag) / P(w) = ( P(tag|w) P(w) / P(tag) ) / P(w) = P(tag|w) / P(tag)
	// thus we can just store P(tag|w) and P(tag)
	// we don't get to factor out the / P(w), which is sad
	// however, it makes handling unknown words a lot easier

	// initialize left column with prob of transition from '.' (full sentence stop) on words[0]
	k = lookup_tag(".")->index;
	for(j=0;j<nstates;j++)
		mat[j]=l0;
	for(j=0;j<htags;j++)
	{
		int J = k*htags + j;
		ptrans = states[J].pprob[k];
		if(j < word_index[words[0]]->nfreqs)
			pword = word_index[words[0]]->tprob[j] - tags[j]->prob;
		else pword = l0;
		mat[j] = pword+ptrans;
	}

	// work across the matrix finding the best path to
	//   each (state, position) pair
	for(i=1;i<len;i++)
	{
		double	*mp = mat + (i-1)*nstates, *mn = mat + i*nstates;
		int		*bn = back + i*nstates;
		struct word	*W = word_index[words[i]];
		for(k=0;k<nstates;k++)
			mn[k] = l0;
		for(k=0;k<nstates;k++)
		{
			if(mp[k] < -99999999.0)continue;
			int		J = states[k].tag*htags, skp = states[k].prev;
			double	mpk = mp[k];
			for(j=0;j<htags;j++,J++)
			{
				ptrans = states[J].pprob[skp];
				if(j < W->nfreqs)
					pword = W->tprob[j] - tags[j]->prob;
				else pword = -10;	// unknown tag for this word
				p = pword + ptrans + mpk;
				// p is the probability of reaching (state J, position i) by some path through (state k, position i-1)
				if(p >= mn[J])
				{
					mn[J] = p;
					bn[J] = k;
				}
			}
		}
	}

/*
	printf("        (START)        ");
	for(i=0;i<len;i++)
		printf("%10s  ", word_index[words[i]]->word);
	printf("\n");
	for(j=0;j<nstates;j++)
	{
		for(i=0;i<len;i++)if(mat[j+i*nstates]>-999999999.0)break;
		if(i==len)continue;
		printf("[%8s %8s]    ", tags[states[j].prev]->tag, tags[states[j].tag]->tag);
		for(i=0;i<len;i++)
			printf("%10g  ", mat[j + i*nstates]);
		printf("\n");
	}
*/

	// find the best complete path
	p = l0, k = 0;
	for(j=0;j<nstates;j++)
		if(mat[j + (len-1)*nstates] > p)
			p = mat[j + (len-1)*nstates], k = j;

	// backtrace it
	for(i=len-1;i>=0;i--)
	{
		//printf("%s [%s %s] ", word_index[words[i]]->word, tags[states[k].tag]->tag, tags[states[k].prev]->tag);
		result[i] = states[k].tag;
		k = back[k + i*nstates];
	}
	//printf("  %f \n", p);

	free(mat);
	free(back);

	return exp(p);
}

int	post_image_size() { return post_hmm_image_size() + post_words_image_size() + post_tags_image_size(); }

void	post_freeze(void	*ptr)
{
	post_hmm_freeze(ptr);
	post_tags_freeze(ptr+post_hmm_image_size());
	post_words_freeze(ptr+post_hmm_image_size()+post_tags_image_size());
}

void	post_recover(void	*ptr)
{
	post_hmm_recover(ptr);
	post_tags_recover(ptr+post_hmm_image_size());
	post_words_recover(ptr+post_hmm_image_size()+post_tags_image_size());
}

struct hmm_info
{
	int					htags;
	int					nstates;
	struct hmm_state	*states;
};

int post_hmm_image_size() { return sizeof(struct hmm_info) + nstates * (sizeof(struct hmm_state) + sizeof(double)*htags); }

int	post_hmm_freeze(void	*ptr)
{
	struct	hmm_info	*p = ptr;
	struct	hmm_state	*s = ptr + sizeof(struct hmm_info);
	double				*P = (double*)(s + nstates);
	int					i;
	p->htags = htags;
	p->nstates = nstates;
	p->states = ptr + sizeof(struct hmm_info);
	for(i=0;i<nstates;i++,s++)
	{
		*s = states[i];
		memcpy(P, s->pprob, sizeof(double)*htags);
		s->pprob = P;
		P += htags;
	}
}

int	post_hmm_recover(void	*ptr)
{
	struct	hmm_info	*p = ptr;
	htags = p->htags;
	nstates = p->nstates;
	states = p->states;
}

void	post_tag_sequence(int	len, char	**lemmas, char	**_tags, int *unk)
{
	int	words[len], answers[len], i;

	remember_word_count();
	for(i=0;i<len;i++)
	{
		char	copy[25600], *p, *q;
		struct word	*w;
		p = copy; q = lemmas[i];
		while(*q)
			if(strchr(".?![]\",'|{}()\\/", *q))q++;
			else *p++ = *q++;
		*p = 0;
		w = lookup_word(copy, 0, i==0);
		if(!w->count) unk[i] = 1;
		else unk[i] = 0;
		words[i] = w->index;
	}
	viterbi_decode(len, words, answers);
	for(i=0;i<len;i++)_tags[i] = tags[answers[i]]->tag;
	forget_new_words();
}

dump_hmm_to_text(FILE	*f)
{
	int i, j;
	fprintf(f, "hmm states %d\n", nstates);
	for(i=0;i<nstates;i++)
	{
		struct hmm_state	*st = states+i;
		int nlines = 0;
		for(j=0;j<ntags;j++)
			if(!isnan(st->pprob[j]) && !isinf(st->pprob[j]))
				nlines++;
		fprintf(f, "state %d %d %d\n", st->tag, st->prev, nlines);
		for(j=0;j<ntags;j++)
			if(!isnan(st->pprob[j]) && !isinf(st->pprob[j]))
				fprintf(f, "> %d %f\n", j, st->pprob[j]);
	}
}

load_hmm_from_text(FILE	*f)
{
	int i;
	assert(1 == fscanf(f, "hmm states %d\n", &nstates));
	states = calloc(sizeof(struct hmm_state), nstates);
	for(i=0;i<nstates;i++)
	{
		struct hmm_state	*st = states+i;
		int	nlines;
		assert(3 == fscanf(f, "state %d %d %d\n", &st->tag, &st->prev, &nlines));
		int	tidx;
		double	prob;
		st->pprob = calloc(sizeof(double), ntags);
		int j;
		for(j=0;j<ntags;j++)
			st->pprob[j] = log(0);
		while(nlines-- > 0)
		{
			assert(2 == fscanf(f, "> %d %lf\n", &tidx, &prob));
			assert(tidx >= 0 && tidx < ntags);
			st->pprob[tidx] = prob;
		}
	}
	htags = ntags;
}
