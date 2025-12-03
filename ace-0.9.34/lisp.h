#ifndef	ACE_LISP_H
#define	ACE_LISP_H

// for reading Version.lisp and maybe some other config files

struct s_exp
{
	enum {
		s_exp_id = 1,
		s_exp_str = 2,
		s_exp_list = 3,
		s_exp_cons = 4
	}	type;
	int	quoted;
	char	*value;
	int				len;
	struct s_exp	**list;
};

struct s_exp	*parse_lisp(char	**P, int	quoted);

#endif
