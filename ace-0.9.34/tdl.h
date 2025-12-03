#ifndef	TDL_H
#define	TDL_H

#include	"dag.h"

struct tdl_line
{
	int	processed;
	char	*lhs, *rhs;
	char	*odef;
	char	*status, *filename;
	int		lnum;

	char	operation;
};

extern char	*g_cons_type;
extern char	*g_list_type;
extern char	*g_null_type;
extern char	*g_diff_list_type;

char	*trim_string(char	*str);
int	process_tdl_dgs_status(char	*status, int	(*callback)(char	*lhs, struct dg	*dg, struct tdl_line	*line));
int	process_mtr_status(char	*status, int	(*process)(char	*lhs, struct dg	*main_dg, struct dg	*output_override));
int	process_tdl_status(char	*status, int	(*callback)(struct tdl_line	*line, void	*ref), void	*ref);
//int	iterate_tdl(char	*path, int	(*callback)(char	*lhs, char	*rhs, void	*ref), void	*ref);
//int	iterate_tdl_dgs(char	*path, int	(*callback)(char	*lhs, struct dg	*dg));
//int	iterate_tdl_types(char	*path);
//int	iterate_tdl_lex(char	*path);

char	*get_conf(char	*lhs);
char	*get_conf_unq(char	*lhs);
char	*get_conf_file_path(char	*lhs);
char	*get_conf_parent_dir(char	*lhs);

char	*get_lisp_parameter(char	*name);
void	load_lisp(char	*path);

char	*path_for_include(char	*parent, char	*what, char	*suffix);

struct dg	*dagify(char	*str, struct type	*building_type);

#endif
