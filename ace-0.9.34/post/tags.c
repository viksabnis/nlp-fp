#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<unistd.h>
#include	<sys/fcntl.h>

#include	"words.h"
#include	"tags.h"

int				ntags;
struct tag		**tags;
static int	tags_ascii_len;

struct tags_info
{
	int	ntags, tags_ascii_len;
	struct tag	**tags;
};

struct tag	*lookup_tag(char	*tag)
{
	int			i;
	char		*bar;
	struct tag	*t;

	// if the tag is a multi-possibility coding like NP|VBG, just ignore all but the first.
	// `tag' won't be a read-only string since we don't do this kind of silliness from the program.
	if( (bar = strchr(tag, '|')) )
		*bar = 0;

	for(i=0;i<ntags;i++)
		if(!strcmp(tags[i]->tag, tag))return tags[i];
	t = malloc(sizeof(struct tag));
	t->index = ntags++;
	t->tag = strdup(tag);
	tags_ascii_len += (strlen(t->tag)&~3) + 4;
	t->count = 0;
	//t->nprecs = ntags;
	//t->precs = calloc(sizeof(int), ntags);
	//t->pprob = 0;
	tags = realloc(tags, sizeof(struct tag*) * ntags);
	tags[t->index] = t;
	return t;
}

int	post_tags_image_size() { return sizeof(struct tags_info) + ntags * (sizeof(struct tag*) + sizeof(struct tag)) + tags_ascii_len; }

void	post_tags_freeze(void	*ptr)
{
	struct tags_info	*p = ptr;
	struct tag	*t = ptr + sizeof(struct tags_info) + sizeof(struct tag*)*ntags;
	char			*a = (char*)(t + ntags);
	int				i;
	p->tags_ascii_len = tags_ascii_len;
	p->ntags = ntags;
	p->tags = ptr + sizeof(struct tags_info);
	for(i=0;i<ntags;i++,t++)
	{
		*t = *tags[i];
		p->tags[i] = t;
		strcpy(a, t->tag);
		t->tag = a; a += strlen(a)+1;
	}
}

void	post_tags_recover(void	*ptr)
{
	struct tags_info	*p = ptr;
	int	i;
	tags_ascii_len = p->tags_ascii_len;
	ntags = p->ntags;
	tags = p->tags;
}
