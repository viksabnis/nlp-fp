#ifndef	HASH_H
#define HASH_H

struct hash
{
	char	*name;
	int		size, entries;
	int		has_flk;	// fixed-length (binary) keys
	struct hash_bucket
	{
		char	*key;
		void	*value;
		struct hash_bucket *next;
	}		**buckets;
};

struct hash	*hash_new(char	*name);
size_t	hash_memory_usage(struct hash	*ht);
struct hash	*hash_copy(struct hash	*ht, void*	(*alloc)(size_t	len));
struct hash	*freeze_hash(struct hash	*ht);
struct hash	*freeze_string_hash(struct hash	*h);
void		hash_add(struct hash	*ht, char	*key, void	*value);
void		*hash_find(struct hash	*ht, char	*key);
void		hash_visit_key(struct hash	*ht, char	*key, void	(*visitor)(void *value));

#endif
