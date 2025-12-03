#ifndef	_TAGS_H
#define	_TAGS_H

struct tag
{
	int			index;
	char		*tag;
	int			count;
	double		prob;
};

extern int				ntags;
extern struct tag		**tags;

struct tag	*lookup_tag(char	*tag);
void		calc_best_unknown_word_tag();

double	viterbi_decode(int	len, int	*words, int	*result);
void	build_hmm();

#endif
