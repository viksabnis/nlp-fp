#ifndef	_WORDS_H
#define	_WORDS_H

struct word
{
	int			index;
	char		*word;
	int			count;

	// this is indexed by tag->index
	int			nfreqs;
	double		*tprob;
};

extern int				nwords;
extern struct word		**word_index;

void		calc_words_most_frequent();
struct word	*lookup_word(char	*word, int	mode, int	first);

#endif
