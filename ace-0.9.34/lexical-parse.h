#ifndef	_LEXICAL_PARSE_H
#define	_LEXICAL_PARSE_H

struct lattice	*lexical_lookup_into_chart(struct lattice	*token_chart);
void		apply_lexical_filtering(struct lattice	*lexical_chart);

#endif
