// note: the token lattice has tokens as edges and spots between tokens as vertices
// the HMM transitions correspond to those vertices, and the emission contexts correspond to the tokens/edges.

// lookups to be supported:
// given [tag1,tag2,tag3], what is the transition probability?
// given [string], what are the probabilites of that string given each tag?
// how efficient do those retrievals need to be?
//	need to look up all probs of all strings in the lattice once, and save them in a fast access matrix
//	forward algorithm: may revisit same triple many times; can organize access to be local in one or two of the dimensions, if that helps
//	backward algorithm:

// may have to solve forward/backward probabilities for tag bigrams, for conditional independence reasons
// can marginalize afterwards

#include	"lattice-mapping.h"

#ifndef	UBERTAG_H
#define	UBERTAG_H

struct ut_emission
{
	int	offset;	// where in the string table?
	unsigned short	tag, classcase;
	float	score;
}	__attribute__((packed));

struct ut_transition
{
	unsigned short	t2, t3;
	float			score;
}	__attribute__((packed));

struct ut_transition_set
{
	float	unigram_score;
	int						atrans3, atrans2;
	int						ntrans3, ntrans2;
	struct ut_transition	*trans3, *trans2;
};

struct ubertagger
{
	int		ntags;
	char	**tags;
	int		start_tag, end_tag, unk_tag;
	struct hash	*tag_hash;
	int		nclasscases;
	char	**classcases;
	struct hash	*classcase_hash;
	char	*emissions;				// concatenated emission strings, 0-separated
	int		nemissions, lemissions;
	struct ut_emission	*emission_tagscores;
	struct hash	*ltmap;
	struct ut_transition_set	*trans;
	struct hash	*whitelist;
};

struct ubertagger	*load_ubertagger(char	*expath, char	*txpath, char	*genmappath);
void	ubertag_lattice(struct ubertagger	*ut, struct lattice	*ll, double	thresh);
void	*freeze_ubertagger();
void	recover_ubertagger(void	*u);
int		load_ubertagging();

#endif
