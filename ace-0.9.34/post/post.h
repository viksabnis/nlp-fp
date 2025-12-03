#ifndef	POST_H
#define	POST_H

int		post_train_from(char	*fname);
int		post_load_from_text_dump(char	*fname);
void	post_tag_sequence(int	len, char	**lemmas, char	**tags, int *unk);
int		post_image_size();
void	post_freeze(void	*ptr);
void	post_recover(void	*ptr);


#endif
