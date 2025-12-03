struct tnt_result
{
	int	ntags;
	struct tag_option
	{
		char	*tag;
		double	prob;
	}	*tags;
};

int	tnt_init(char	*model, int	maxtags);
int	tnt_tag_sequence(int	nwords, char	**words, struct tnt_result	*results);
int	tnt_kill();
