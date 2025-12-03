#include	<stdio.h>
#include	<string.h>
#include	<sys/fcntl.h>
#include	<sys/types.h>
#include	<sys/mman.h>
#include	<unistd.h>
#include	<stdlib.h>
//#include	<asm/mman.h>

#include	"dag.h"
#include	"rule.h"
#include	"morpho.h"
#include	"lexicon.h"
#include	"maxent.h"
#include	"mrs.h"
#include	"freeze.h"
#ifdef	POST
#include	"post.h"
#endif
#include	"lattice-mapping.h"
#include	"hash.h"
#include	"version.h"
#include	"ubertag.h"

extern void		**oldslabs;
extern int		noldslabs, aoldslabs;
extern long long		currslabsize;

extern int debug_level;

void	*freeze_labels();
void	recover_labels(void	*ls);
void	*freeze_rule_filter();
void	recover_rule_filter(void *rf);
void	*freeze_conf();
void	recover_conf(void	*vc);
void	*freeze_repp();
void	recover_repp(void	*ptr);
void	*freeze_instances();
void	recover_instances(void	*ptr);
void	*freeze_transfer();
void	recover_transfer(void	*ptr);

extern char	*grammar_version, *grammar_dir;

// copy all grammar objects to flat blocks
extern int	nlexemes, nrules, norules, ninstances, nfnames, ngeneric_les;
extern struct rule	**rules;
extern struct lexeme	**lexemes, **generic_les;
extern struct orule	**orules;
extern char		**fnames;
extern int		*introduce;

extern unsigned int generation;

struct grammar
{
	char		message[128];
	int		nlexemes, nrules, norules, nfnames, ngeneric_les;

	struct type_hierarchy	*main_th;
	struct type_hierarchy	*semi_th, *semi_p_th;

	struct rule	**rules;
	struct lexeme	**lexemes, **generic_les;
	struct generic_le_info	*generic_le_infos;
	struct orule	**orules;
	char		**fnames;
	void	*morpho_globals;
	int		*introduce;
	void	*rule_filter;
	void	*semindex;
	void	*stochmodel;
	void	*vpm;
	void	*labels;
	void	*conf;
	void	*repp;
	void	*instances;
	void	*post;
	void	*token_mapping_rules;
	void	*lexical_filtering_rules;
	void	*post_generation_mapping_rules;
	void	*transfer;
	void	*qc;
	void	*ubertagger;
};

extern void	*slab_alloc(int	len);

wchar_t	*freeze_wcs(wchar_t	*str)
{
	int	len;
	char	*copy;
	if(str==0)return 0;
	len = (wcslen(str)+1) * sizeof(wchar_t);
	return freeze_block(str, len);
}

char	*freeze_string(char	*str)
{
	int	len;
	char	*copy;
	if(str==0)return 0;
	len = strlen(str)+1;
	if(len%4)len = len - (len%4) + 4;
	copy = slab_alloc(len);
	return strcpy(copy, str);
}

struct tdl_line	*freeze_tdl_line(struct tdl_line	*lin)
{
	struct tdl_line	*lout = slab_alloc(sizeof(struct tdl_line));
	*lout=*lin;
	lout->lhs = freeze_string(lin->lhs);
	lout->rhs = freeze_string(lin->rhs);
	if(lin->odef)lout->odef = freeze_string(lin->odef);
	lout->status = freeze_string(lin->status);
	lout->filename = freeze_string(lin->filename);
	return lout;
}

struct rule	*freeze_rule(struct rule	*rin)
{
	struct rule	*rout = slab_alloc(sizeof(struct rule));

	*rout = *rin;
	rout->dg = copy_dg(rin->dg);
	rout->packdg = copy_dg(rin->packdg);
	rout->gpackdg = copy_dg(rin->gpackdg);
	rout->name = freeze_string(rin->name);
	strcpy(rout->name, rin->name);
	if(rout->tdl)rout->tdl = freeze_tdl_line(rin->tdl);

	// make sure the semantic index pointers can find the frozen rules
	rin->dg = (struct dg*)rout;
	return rout;
}

struct type_hierarchy	*ft_th;

static struct type	*FT(struct type	*t)
{
	if(!t)return 0;
	else if(t->name[0]=='"')return ft_th->strings[t->tnum];
	else return ft_th->types[t->tnum];
}

struct lexeme	*freeze_lexeme(struct lexeme	*lin)
{
	struct lexeme	*lout = slab_alloc(sizeof(struct lexeme));

	// XXX hack!
	if(generation > MAX_GEN_RESET)generation = 11;
	// XXX hack!

	lout->dg = lin->dg;	// NOTE: this is frozen *later*, for file layout reasons
	lout->word = freeze_string(lin->word);

	lout->stemlen = lin->stemlen;
	lout->stem = slab_alloc(sizeof(struct type*) * lout->stemlen);
	lout->lextype = FT(lin->lextype);
	lout->pred = FT(lin->pred);
	lout->onset = lin->onset;
	memcpy(lout->stem, lin->stem, sizeof(struct type*) * lout->stemlen);

	lin->dg = (struct dg*)lout;	// NOTE: keep pointer to new copy of lexeme, so semantic index can be updated

	return lout;
}

void	patch_type(struct type	*tout)
{
	int i;
	for(i=0;i<tout->nparents;i++)
		tout->parents[i] = FT(tout->parents[i]);
	for(i=0;i<tout->ndaughters;i++)
		tout->daughters[i] = FT(tout->daughters[i]);
}

void	patch_dg(struct dg	*dg)
{
	int	i;
	struct dg	**arcs;

	if(!dg)return;
	dg = dereference_dg(dg);
	if(!dg)return;

	//printf("type %s -> ", dg->xtype->name);
	dg->xtype = FT(dg->xtype);

	dg->ncarcs = 0;
	dg->carcs = 0;
	dg->gen = 0;
	dg->forwarded = 0;
	dg->copy = 0;
	dg->type = dg->xtype;

	arcs = DARCS(dg);

	//printf("%s\n", dg->type->name);
	for(i=0;i<dg->narcs;i++)
		patch_dg(arcs[i]);
}

struct type	*freeze_type(struct type	*tin)
{
	struct type	*tout = slab_alloc(sizeof(struct type));

	// XXX hack!
	if(generation > MAX_GEN_RESET)generation = 11;
	// XXX hack!

	*tout = *tin;
	tout->dg = tin->dg?copy_dg(tin->dg):0;
	tout->name = freeze_string(tin->name);
	tout->descendents = freeze_block(tin->descendents, tin->ndescendents * sizeof(short));
	tout->parents = freeze_block(tin->parents, sizeof(struct type*)*tout->nparents);
	tout->daughters = freeze_block(tin->daughters, sizeof(struct type*)*tout->ndaughters);

	if(tout->tdl)tout->tdl = freeze_tdl_line(tin->tdl);

	return tout;
}

struct type_hierarchy	*freeze_type_hierarchy(struct type_hierarchy	*thin)
{
	int	i;
	if(!thin)return NULL;
	for(i=0;i<thin->ntypes;i++)
		if(thin->types[i]->tnum != i)
		{
			fprintf(stderr, "type %s tnum %d is wrong.\n", thin->types[i]->name, thin->types[i]->tnum);
			fprintf(stderr, "claimed tnum = %d; actual tnum = %d\n", thin->types[i]->tnum, i);
			exit(-1);
		}

	struct type_hierarchy	*thout = slab_alloc(sizeof(*thout));
	thout->ntypes = thin->ntypes;
	thout->types = slab_alloc(sizeof(struct type*)*thout->ntypes);
	thout->nstrings = thin->nstrings;
	thout->strings = slab_alloc(sizeof(struct type*)*thout->nstrings);

	for(i=0;i<thout->ntypes;i++)thout->types[i] = freeze_type(thin->types[i]);
	for(i=0;i<thout->nstrings;i++)thout->strings[i] = freeze_type(thin->strings[i]);

	thout->thash = freeze_hash(thin->thash);
	thout->id = freeze_string(thin->id);
	thout->top = thin->top;
	thout->strtype = thin->strtype;
	return thout;
}

void	patch_type_hierarchy(struct type_hierarchy	*th)
{
	int	i;
	if(!th)return;

	struct hash_bucket *walk;
	for(i=0;i<th->thash->size;i++)
		for(walk=th->thash->buckets[i];walk;walk=walk->next)
		{
			struct type	*tin = walk->value;
			walk->value = FT(tin);
		}

	for(i=0;i<th->ntypes;i++)patch_type(th->types[i]);
	for(i=0;i<th->ntypes;i++)patch_dg(th->types[i]->dg);

	th->top = FT(th->top);
	th->strtype = FT(th->strtype);
}

struct dg	*freeze_dg(struct dg	*dg)
{
	patch_dg(dg);
	return copy_dg(dg);
}

void	*freeze_block(void	*src, int	len)
{
	void	*dst;
	int	alen = len;

	if(!src && !len)return 0;
	if(len%4)alen += 4-len%4;
	dst = slab_alloc(alen);
	memcpy(dst, src, len);
	return dst;
}

static void freezer_note(char *designation)
{
	static int last_bytes = 0;
	long long			size = slab_usage() - last_bytes;
	last_bytes = slab_usage();
	if(size<8192)printf(" %s: %lld", designation, size);
	else if(size<1024*1024)printf(" %s: %lldK", designation, (size+512)/1024);
	else if(size<1024*1024*1024)printf(" %s: %.1fM", designation, ((float)size+512*1024)/(1024*1024));
	else printf(" %s: %.1fG", designation, ((float)size+512*1024*1024)/(1024*1024*1024));
}

int	reset_memorized_types = 0;

int	freeze_grammar()
{
	int		i, j;
	struct grammar	*G;

	use_freezer();
	//print_rule("sing_noun_infl_rule");

	inval_thash();

	clear_slab();

	G = slab_alloc(sizeof(struct grammar));

	//null_generation();	// why? seems dangerous...

extern struct type_hierarchy	*main_th, *semi_th, *semi_p_th;
	G->main_th = freeze_type_hierarchy(main_th);
	if(semi_th==main_th)G->semi_th = G->semi_p_th = G->main_th;
	else
	{
		G->semi_th = freeze_type_hierarchy(semi_th);
		ft_th = G->semi_th;
		patch_type_hierarchy(G->semi_th);
		G->semi_p_th = freeze_type_hierarchy(semi_p_th);
		ft_th = G->semi_p_th;
		patch_type_hierarchy(G->semi_p_th);
	}
	ft_th = G->main_th;
	patch_type_hierarchy(G->main_th);
	semi_th = G->semi_th;
	semi_p_th = G->semi_p_th;
	main_th = G->main_th;
	set_default_type_hierarchy(main_th);
	freezer_note("types");
	reset_memorized_types = 1;

	for(i=0;i<nrules;i++)patch_dg(rules[i]->dg);
	for(i=0;i<nrules;i++)patch_dg(rules[i]->packdg);
	for(i=0;i<nrules;i++)patch_dg(rules[i]->gpackdg);

	for(i=0;i<nlexemes;i++)
	{
		if(lexemes[i]->dg)patch_dg(lexemes[i]->dg);
		for(j=0;j<lexemes[i]->stemlen;j++)
			//lexemes[i]->stem[j] = strings[lexemes[i]->stem[j]->tnum];
			lexemes[i]->stem[j] = FT(lexemes[i]->stem[j]);
	}

	for(i=0;i<ngeneric_les;i++)
	{
		if(generic_les[i]->dg)patch_dg(generic_les[i]->dg);
		for(j=0;j<generic_les[i]->stemlen;j++)
			generic_les[i]->stem[j] = FT(generic_les[i]->stem[j]);
	}

	//printf("\n"); print_rule("sing_noun_infl_rule");

	for(i=0;i<nrules;i++)rules[i] = freeze_rule(rules[i]);
	for(i=0;i<norules;i++)
		orules[i]->rule = rules[orules[i]->rule->rnum];

	for(i=0;i<norules;i++)orules[i] = freeze_orule(orules[i]);
	freezer_note("rules");

	//printf("\n"); print_rule("sing_noun_infl_rule");

	for(i=0;i<nlexemes;i++)lexemes[i] = freeze_lexeme(lexemes[i]);
	for(i=0;i<ngeneric_les;i++)generic_les[i] = freeze_lexeme(generic_les[i]);
	freezer_note("lex-info");

	for(i=0;i<nfnames;i++)fnames[i] = freeze_string(fnames[i]);
	introduce = freeze_block(introduce, sizeof(int) * nfnames);

	G->rule_filter = freeze_rule_filter();
	freezer_note("\n miscellaneous");

	// freeze lexicon dgs -- this isn't done earlier so that the
	// 	'struct lexemes' will all be quickly accessible without
	// 	having to page in all their dgs
	for(i=0;i<nlexemes;i++)
	{
		// XXX hack!
		if(generation > MAX_GEN_RESET)generation = 11;
		// XXX hack!

		if(lexemes[i]->dg)lexemes[i]->dg = copy_dg(lexemes[i]->dg);
	}
	for(i=0;i<ngeneric_les;i++)
	{
		if(generation > MAX_GEN_RESET)generation = 11;
		if(generic_les[i]->dg)generic_les[i]->dg = copy_dg(generic_les[i]->dg);
	}
	freezer_note("lex-dgs");

	G->nrules = nrules;
	G->norules = norules;
	G->nlexemes = nlexemes;
	G->ngeneric_les = ngeneric_les;
	G->nfnames = nfnames;
	G->rules = slab_alloc(sizeof(void*) * G->nrules);	memcpy(G->rules, rules, sizeof(void*) * G->nrules);
	G->orules = slab_alloc(sizeof(void*) * G->norules);	memcpy(G->orules, orules, sizeof(void*) * G->norules);
	G->lexemes = slab_alloc(sizeof(void*) * G->nlexemes);	memcpy(G->lexemes, lexemes, sizeof(void*) * G->nlexemes);
	G->generic_les = slab_alloc(sizeof(void*) * G->ngeneric_les);	memcpy(G->generic_les, generic_les, sizeof(void*) * G->ngeneric_les);
	G->generic_le_infos = slab_alloc(sizeof(struct generic_le_info) * G->ngeneric_les);	memcpy(G->generic_le_infos, generic_le_infos, sizeof(struct generic_le_info) * G->ngeneric_les);
	G->fnames = slab_alloc(sizeof(void*) * G->nfnames);	memcpy(G->fnames, fnames, sizeof(char*) * G->nfnames);
	G->vpm = freeze_vpm();
	G->labels = freeze_labels();
	G->conf = freeze_conf();
	G->repp = freeze_repp();
	G->instances = freeze_instances();
	G->introduce = introduce;
	G->morpho_globals = freeze_morpho_globals();
	G->qc = freeze_qc();
	freezer_note("miscellaneous");
	G->semindex = freeze_semantic_index();
	G->transfer = freeze_transfer();
	freezer_note("sem-index");
	G->stochmodel = freeze_stochastic_model();
	freezer_note("stochastic-model");
	G->ubertagger = freeze_ubertagger();
	if(G->ubertagger)freezer_note("ubertagger");

	int l = snprintf(G->message, sizeof(G->message)-1, "frozen grammar file: ace |%s| grammar |%s;;%s|",
		ACE_VERSION, grammar_dir, grammar_version);
	if(l > sizeof(G->message)-3)
		fprintf(stderr, "WARNING: not enough room in 128 bytes to record grammar information\n");
	//strcpy(G->message, "frozen grammar file\n");
	//strcat(G->message, grammar_dir); strcat(G->message, "\n");
	//strcat(G->message, grammar_version); strcat(G->message, "\n");

#ifdef	POST
	if(enable_post)
	{
		G->post = slab_alloc(post_image_size());
		post_freeze(G->post);
		freezer_note("pos-tagger");
	}
	else G->post = NULL;
#endif

extern void	*token_mapping_rules, *lexical_filtering_rules, *post_generation_mapping_rules;
	G->token_mapping_rules = freeze_lattice_rule_set(token_mapping_rules);
	G->lexical_filtering_rules = freeze_lattice_rule_set(lexical_filtering_rules);
	G->post_generation_mapping_rules = freeze_lattice_rule_set(post_generation_mapping_rules);
	freezer_note("latmap rules");

	//printf("\n"); print_rule("sing_noun_infl_rule");

	printf("\n ... "); commit_slab();
	return 0;
}

int	loaded_freeze_fd = -1;
long	loaded_freeze_size;

static int	load_freeze()
{
	struct grammar	*G;
	int		i;

	if(loaded_freeze_size < sizeof(*G))
	{
		fprintf(stderr, "this does not appear to be a grammar image.\n");
		exit(-1);
	}

	G = (struct grammar*)mmap((void*)FREEZER_MMAP_BASE, loaded_freeze_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, loaded_freeze_fd, 0);
	// first try to map with HUGETLB
	//G = (struct grammar*)mmap((void*)FREEZER_MMAP_BASE, loaded_freeze_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_HUGETLB, loaded_freeze_fd, 0);
	//fprintf(stderr, "result of mmap grammar with HUGETLB: %p\n", G);
	//if(G == (void*)MAP_FAILED)
	//	G = (struct grammar*)mmap((void*)FREEZER_MMAP_BASE, loaded_freeze_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, loaded_freeze_fd, 0);
	if(G == (void*)MAP_FAILED)
	{
		perror("mmap");
		exit(-1);
	}
	if(G != (void*)FREEZER_MMAP_BASE)
	{
		fprintf(stderr, "mmap returned %p\n", G);
		perror("mmap didn't put the freezer where i wanted it");
		exit(-1);
	}
	char	frozen_ace_version[128];
	char	frozen_grammar[128];
	if(2 != sscanf(G->message, "frozen grammar file: ace |%[^|]| grammar |%[^|]|",
		frozen_ace_version, frozen_grammar))
	{
		fprintf(stderr, "this does not appear to be a grammar image.\n");
		exit(-1);
	}
	if(strcmp(frozen_ace_version, ACE_VERSION))
	{
		fprintf(stderr, "version mismatch: this is ACE version %s, but this grammar image was compiled by ACE version %s\n", ACE_VERSION, frozen_ace_version);
		exit(-1);
	}
	char	*frozen_grammar_version = strstr(frozen_grammar, ";;");
	if(frozen_grammar_version)
	{
		frozen_grammar_version += 2;
		grammar_version = strdup(frozen_grammar_version);
		if(debug_level > 0)fprintf(stderr, "NOTE: loading frozen grammar %s\n", grammar_version);
	}

extern struct type_hierarchy	*main_th, *semi_th, *semi_p_th;
	main_th = G->main_th;
	semi_th = G->semi_th;
	semi_p_th = G->semi_p_th;
	set_default_type_hierarchy(main_th);

	nlexemes = G->nlexemes;
	ngeneric_les = G->ngeneric_les;
	nrules = G->nrules;
	norules = G->norules;
	nfnames = G->nfnames;

	lexemes = G->lexemes;
	generic_les = G->generic_les;
	generic_le_infos = G->generic_le_infos;
	rules = G->rules;
	orules = G->orules;

	// in case we accidentally add more during parsing
	fnames = malloc(sizeof(char*) * nfnames);
	introduce = malloc(sizeof(int) * nfnames);
	memcpy(fnames, G->fnames, sizeof(char*) * nfnames);
	memcpy(introduce, G->introduce, sizeof(int) * nfnames);

	recover_rule_filter(G->rule_filter);
	recover_repp(G->repp);
	recover_conf(G->conf);
	recover_instances(G->instances);
	recover_labels(G->labels);
	recover_qc(G->qc);
	recover_vpm(G->vpm);
	recover_semantic_index(G->semindex);
	recover_transfer(G->transfer);
	recover_stochastic_model(G->stochmodel);
	recover_ubertagger(G->ubertagger);

#ifdef	POST
	if(enable_post)
		post_recover(G->post);
#endif

extern void	*token_mapping_rules;
extern void	*lexical_filtering_rules;
extern void	*post_generation_mapping_rules;
	token_mapping_rules = G->token_mapping_rules;
	compile_lattice_rule_set(token_mapping_rules);
	lexical_filtering_rules = G->lexical_filtering_rules;
	compile_lattice_rule_set(lexical_filtering_rules);
	post_generation_mapping_rules = G->post_generation_mapping_rules;
	compile_lattice_rule_set(post_generation_mapping_rules);

	thaw_morpho_globals(G->morpho_globals);

	if(debug_level)
		fprintf(stderr, "NOTE: %d types, %d lexemes, %d rules, %d orules, %d instances, %d strings, %d features\n",
				main_th->ntypes, nlexemes, nrules, norules, ninstances, main_th->nstrings, nfnames);

	/*if(mlock(strings[0], sizeof(struct type)*nstrings))
		perror("unable to mlock strings");*/

	return 0;
}

void	reload_frozen_grammar()
{
	if(loaded_freeze_fd==-1)
	{
		fprintf(stderr, "can't reload_frozen_grammar(), since no freeze is currently loaded!\n");
		exit(-1);
	}
	fprintf(stderr, "NOTE: generation reset\n");
	munmap((void*)FREEZER_MMAP_BASE, loaded_freeze_size);
	null_generation();
	load_freeze();
}

// load flat blocks grammar file
int	load_frozen_grammar(char	*path)
{
	int	freeze_fd = open(path, O_RDONLY);
	int	len;

	if(freeze_fd<0) { perror(path); exit(-1); }

	len = lseek(freeze_fd, 0, SEEK_END);
	lseek(freeze_fd, 0, SEEK_SET);
	loaded_freeze_fd = freeze_fd;
	loaded_freeze_size = len;
	return load_freeze();
}

void	*freeze_point = 0, *freeze_next;
int	freeze_fd;

size_t	FREEZER_MMAP_SIZE = 0x14000000;

// prepare mmap to save flat blocks grammar file
int	setup_save_frozen_grammar(char	*path)
{
	FREEZER_MMAP_SIZE = 1024 * 1024 * (size_t)freezer_megabytes;
	freeze_fd = open(path, O_RDWR | O_CREAT, 0664);

	if(freeze_fd<0) { perror(path); exit(-1); }

	if(ftruncate(freeze_fd, FREEZER_MMAP_SIZE)) { perror("ftruncate FREEZER_MMAP_SIZE"); exit(-1); }
	//freeze_point = mmap((void*)FREEZER_MMAP_BASE, FREEZER_MMAP_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_FIXED, freeze_fd, 0);
	freeze_point = mmap((void*)FREEZER_MMAP_BASE, FREEZER_MMAP_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, freeze_fd, 0);
	if(freeze_point == (void*)MAP_FAILED)
	{
		perror("mmap fixed");
		exit(-1);
	}
	if(freeze_point != (void*)FREEZER_MMAP_BASE)
	{
		fprintf(stderr, "mmap returned %p\n", freeze_point);
		perror("mmap didn't put the freezer where I wanted it");
		exit(-1);
	}
}

int use_freezer()
{
	//fprintf(stderr, "we got %p\n", freeze_point);
	freeze_next = freeze_point;
	currslabsize = FREEZER_MMAP_SIZE;
	return 0;
}

/*
void	dump_grammar()
{
	int	i;

	for(i=0;i<ntypes;i++)
	{
		printf("type `%s': ", types[i]->name);
		print_dg(types[i]->dg);printf("\n");
	}

	for(i=0;i<nrules;i++)
	{
		printf("rule `%s': ", rules[i]->name);
		print_dg(rules[i]->dg);printf("\n");
	}

	for(i=0;i<nlexemes;i++)
	{
		printf("lex `%s': ", lexemes[i]->word);
		print_dg(lexemes[i]->dg);printf("\n");
	}
}*/
