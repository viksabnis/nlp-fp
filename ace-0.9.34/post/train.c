#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<unistd.h>
#include	<sys/fcntl.h>
#include	<math.h>
#include	<assert.h>

#include	"words.h"
#include	"tags.h"

void	count_tag(char	*word, char	*tag);

extern int	post_verbose;

int	*train_words;
int	*train_tags;
int	train_total;

int	train_from_text(char	*txt)
{
	char	*word, *slash, *tag;

	// iterate through the words in the input,
	//   building our dictionary-hash-table and tag list
	for(word = strtok(txt, " \t\n");word;word = strtok(0, " \t\n"))
	{
		if(!strncmp(word, "=====", 5))
		{
			count_tag("", ".");
			count_tag("", ".");
			continue;
		}

		// ugly special cases due to BUGS in the input text...
		if(!strcmp(word, "{"))
		{
			count_tag("{", "(");
			continue;
		}
		if(!strcmp(word, "}"))
		{
			count_tag("}", ")");
			continue;
		}

		slash = rindex(word, '/');
		if(!slash)
		{
			if(post_verbose)
				fprintf(stderr, "WARNING: malformed input near `%.16s' in training text\n", word);
			continue;
		}
		if(slash == word)continue;	// no surface form for this tag...!?

		*slash = 0, tag = slash+1;

		if(post_verbose>2)printf("[word `%s', tag `%s']\n", word, tag);
		count_tag(word, tag);
	}

	build_hmm();

	return 0;
}

void	count_tag(char	*word, char	*tag)
{
	struct word	*w = lookup_word(word, 1, 0);
	struct tag	*t = lookup_tag(tag);
	static int	atrain = 0;

	if(train_total+1>atrain)
	{
		atrain = (atrain+1)*2;
		train_words = realloc(train_words, sizeof(struct word*)*atrain);
		train_tags = realloc(train_tags, sizeof(struct tag*)*atrain);
	}
	train_words[train_total] = w->index;
	train_tags[train_total] = t->index;
	train_total++;

	w->count++;
	t->count++;
}

char	*load_file(char	*fname)
{
	int		fd = open(fname, O_RDONLY), len;
	char	*txt;

	if(fd<0) return perror(fname), (char*)0;
	txt = malloc(1 + (len = lseek(fd, 0, SEEK_END)));
	if(!txt) return perror("malloc"), (char*)0;
	lseek(fd, 0, SEEK_SET);
	if(len != read(fd, txt, len)) return perror("read"), (char*)0;
	txt[len] = 0;
	if(post_verbose)fprintf(stderr, "[read %d bytes from %s]\n", len, fname);

	return txt;
}

int	post_train_from(char	*fname)
{
	char	*train_txt;
	if(!(train_txt = load_file(fname)))exit(-1);

	if(train_from_text(train_txt))exit(-1);
	if(ntags)
	{
		//fprintf(stderr, "NOTE: %d training words, %d tags\n", train_total, ntags);
		return 0;
	}
	else
	{
		fprintf(stderr, "ERROR: no training data in `%s'!\n", fname);
		return -1;
	}
}

int	post_load_from_text_dump(char	*fname)
{
	int	i;
	FILE	*f = fopen(fname, "r");
	if(!f)return -1;

	int	my_ntags;
	assert(1 == fscanf(f, "tags %d\n", &my_ntags));
	for(i=0;i<my_ntags;i++)
	{
		char		my_tagstr[32];
		int			my_index, my_count;
		double		my_prob;
		assert(4 == fscanf(f, "%d %s %d %lf\n", &my_index, my_tagstr, &my_count, &my_prob));
		struct tag	*t = lookup_tag(my_tagstr);
		assert(t->index == my_index);
		t->count = my_count;
		t->prob = my_prob;
	}
	assert(0 == fscanf(f, "\n"));

	int	my_nwords;
	assert(1 == fscanf(f, "words %d\n", &my_nwords));
	for(i=0;i<my_nwords;i++)
	{
		char	wordstr[1024];
		int	nlines, index, count;
		assert(4 == fscanf(f, "%d %[^ \n] %d %d\n", &index, wordstr, &count, &nlines));
		assert(wordstr[strlen(wordstr)-1]=='"');
		wordstr[strlen(wordstr)-1] = 0;
		//printf("loaded word %d = %s\n", w->index, wordstr+1);
		char	*wptr = wordstr+1;
		struct word	*w = lookup_word(wptr, 1, 0);
		w->word = strdup(wordstr+1);
		assert(w->index == index);
		w->count = count;
		int	tidx;
		char	tagstr[32];
		double	prob;
		w->nfreqs = ntags;
		w->tprob = calloc(sizeof(double), w->nfreqs);
		int j;
		for(j=0;j<ntags;j++)w->tprob[j] = log(0);
		while(nlines-- > 0)
		{
			assert(3 == fscanf(f, "> %d %s %lf\n", &tidx, tagstr, &prob));
			assert(tidx >= 0 && tidx < ntags);
			assert(!strcmp(tagstr, tags[tidx]->tag));
			w->tprob[tidx] = prob;
		}
	}
	assert(0 == fscanf(f, "\n"));

	load_hmm_from_text(f);

	fclose(f);
	return 0;
}
