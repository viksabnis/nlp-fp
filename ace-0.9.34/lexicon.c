#include	<stdlib.h>
#include	<string.h>
#include	<stdio.h>
#include	<assert.h>
#include	<ctype.h>
#include	<sys/time.h>

#include	"tdl.h"
#include	"lexicon.h"
#include	"chart.h"
#include	"morpho.h"
#include	"conf.h"
#include	"freeze.h"
#include	"unicode.h"

struct lexeme	**lexemes;
int		nlexemes;
int		alexemes = 0;

struct lexeme	**generic_les;
struct generic_le_info	*generic_le_infos;
int		ngeneric_les;

extern unsigned int	generation;

extern int trace, gen_qc;

struct dg	*constrain_lex_rels(struct dg *dg, struct dg *rels);

int	enable_simple_form_lexicon = 0;

// TODO: make this accept the dg of the first TOKEN that will be unified in
// ... that will allow rejection of most generic LEs without forming a full lexical edge
// ... might have to store a complete wellformed dag for each generic LE to make that work optimally?

struct dg	*lexical_dg(struct lexeme *lex, struct dg	*rels)
{
	struct dg	*ldg, *dg;
	if(enable_simple_form_lexicon)
		ldg = expand_lexeme(lex);
	else ldg = lex->dg;

	if(rels)
	{
		//printf("constraining lexical dag for %s.\n", lex->word);
		//printf("base:\n"); print_dg(lex->dg?copy_dg(ldg):ldg); printf("\n");
		//printf("rels:\n"); print_dg(rels); printf("\n");
		ldg = constrain_lex_rels(lex->dg?copy_dg(ldg):ldg, rels);
		//printf("result:\n"); print_dg(ldg); printf("\n");
	}

	struct dg	*lt = lex->lextype->dg;//restrict_copy_dg(lex->lextype->dg, (g_mode == GENERATING)?1:0);
	dg = unify_dg(ldg, lt, -1);
	if(!dg)
	{
		if(rels)
		{
#ifdef UNIFY_PATHS
			if(trace > 1)
			{
				printf("specialization of `%s' failed: ", lex->word);
				unify_backtrace();
			}
#endif
			return 0;
		}
		fprintf(stderr, "NOTE: ERROR! lexeme `%s' failed construction\n", lex->word);
#ifdef UNIFY_PATHS
		unify_backtrace();
#endif
		output_lui_dg(ldg, "lexical dag");
		output_lui_dg(lex->lextype->dg, "type dag");
		while(1)sleep(1);
		exit(-1);
	}
	int wellform_result = wellform(dg, lex->word);
	assert(wellform_result == 0);

	return dg;
}

struct edge	*lexical_edge(struct lexeme	*lex, int	i, int	len, struct dg	*rels)
{
	struct edge	*edge = slab_alloc(sizeof(struct edge));

//#define RECORD_LEXICAL_ACCESS
#ifdef RECORD_LEXICAL_ACCESS
	static FILE	*lexf = 0;
	if(!lexf)lexf = fopen("/tmp/lexical-access", "w");
	fprintf(lexf, "%s\n", lex->word);
	fflush(lexf);
#endif

	bzero(edge, sizeof(struct edge));
	edge->dg = lexical_dg(lex, rels);
	if(edge->dg == 0)return 0;
	edge->id = next_eid();
	edge->from = i;
	edge->to = i+len;
	edge->lex = lex;
	edge->qc = gen_qc?NULL:extract_qc(edge->dg);
	if(g_mode == GENERATING)
	{
		edge->ep_span_bv = bitvec_slab_alloc(n_epsbv);
		bitvec_clear_all(edge->ep_span_bv, n_epsbv);
	}

	return edge;
}

int	lex_strcmp(char	*a, char	*b)
{
	return strcasecmp(a, b);
	while(*a)if(*b++!=*a++)return a[-1]-b[-1];
	if(*b)return -*b;
	return 0;
}

int	ascii_visit_lexicon(char	*stem, int (*visitor)(struct lexeme *lex))
{
	int		num=0;
	char		stemcmp[1024];
	int		i, j, k, r = -1;

	sprintf(stemcmp, "\"%s\"", stem);
	for(i=0,j=nlexemes-1;i<=j;)
	{
		k = (i+j)/2;
		r = lex_strcmp(lexemes[k]->stem[0]->name, stemcmp);
		if(r==0)break;
		if(r<0)i = k+1;
		else j = k-1;
	}
	if(r==0)
	{
		i=k;
		for(i=k;i<nlexemes && !lex_strcmp(lexemes[i]->stem[0]->name, stemcmp);i++)
			num += visitor(lexemes[i]);
		for(i=k-1;i>=0 && !lex_strcmp(lexemes[i]->stem[0]->name, stemcmp);i--)
			num += visitor(lexemes[i]);
	}
	return num;
}

int	mbswcscasecmp(char	*mbs, wchar_t	*wcs)
{
	wchar_t	*w = towide(mbs);
	int	r = wcscasecmp(w, wcs);
	free(w);
	return r;
}

int	visit_lexicon(char	*stem, int (*visitor)(struct lexeme *lex))
{
	int		num=0;
	wchar_t		stemcmp[1024];
	int		i, j, k, r = -1;

	swprintf(stemcmp, 1020, L"\"%s\"", stem);
	for(i=0,j=nlexemes-1;i<=j;)
	{
		k = (i+j)/2;
		r = mbswcscasecmp(lexemes[k]->stem[0]->name, stemcmp);
		if(r==0)break;
		if(r<0)i = k+1;
		else j = k-1;
	}
	if(r==0)
	{
		i=k;
		for(i=k;i<nlexemes && !mbswcscasecmp(lexemes[i]->stem[0]->name, stemcmp);i++)
			num += visitor(lexemes[i]);
		for(i=k-1;i>=0 && !mbswcscasecmp(lexemes[i]->stem[0]->name, stemcmp);i--)
			num += visitor(lexemes[i]);
	}
	return num;
}

void	dump_parts_of_speech()
{
	FILE	*f = popen("uniq", "w");
	struct dg	*synsem, *lkeys, *keyrel;
	struct dg	*pred, *carg;
	int		synsemf = lookup_fname("SYNSEM");
	int		lkeysf = lookup_fname("LKEYS");
	int		keyrelf = lookup_fname("KEYREL");
	int		predf = lookup_fname("PRED");
	int		cargf = lookup_fname("CARG");
	int	i;
	char	rel[128], *rptr, *letype, *pos;

	for(i=0;i<nlexemes;i++)
	{
		synsem = dg_hop(lexemes[i]->dg, synsemf);
		lkeys = keyrel = 0;
		if(synsem)lkeys = dg_hop(synsem, lkeysf);
		if(synsem && lkeys)keyrel = dg_hop(lkeys, keyrelf);
		if(synsem && keyrel)
		{
			pred = dg_hop(keyrel, predf);
			carg = dg_hop(keyrel, cargf);
			if(pred)rptr = pred->xtype->name;
			else if(carg)rptr = carg->xtype->name;
			else rptr = 0;
			if(rptr)
			{
				if(*rptr == '"')
				{
					strcpy(rel, rptr+1);
					if(*rel)rel[strlen(rel)-1] = 0;
				}
				else strcpy(rel, rptr);
				letype = lexemes[i]->dg->xtype->name;
				if(!strncmp(letype, "n_", 2))pos = "noun";
				else if(!strncmp(letype, "v_", 2))pos = "verb";
				else if(!strncmp(letype, "det_", 4))pos = "det";
				else if(!strncmp(letype, "adj_", 4))pos = "adj";
				else if(!strncmp(letype, "adv_", 4))pos = "adv";
				else if(!strncmp(letype, "p_", 2))pos = "prep";
				else if(!strncmp(letype, "pp_", 3))pos = "prep";
				else if(!strncmp(letype, "va_", 3))pos = "auxverb";
				else if(!strncmp(letype, "vc_", 3))pos = "copverb";
				else if(!strncmp(letype, "conj_", 5))pos = "conj";
				else if(!strncmp(letype, "comp_", 5))pos = "comp";
				else pos = 0;
				if(pos)fprintf(f, "%s	%s\n", pos, rel);
			}
		}
	}

	pclose(f);
}

static int	orthfeat = -1, rfeat = 2, ffeat = 1, synsemfeat = -1, lkeysfeat, keyrelfeat,
			predfeat, phonfeat, onsetfeat, listfeat, __tlfeat;
static struct type	*predsort, *con, *voc, *native_token_list;

int	nsimpleform = 0;

void	init_fnums()
{
	if(enable_simple_form_lexicon)
	{
		orthfeat = lookup_fname("ORTH");
		__tlfeat = lookup_fname("--TL");
	}
	synsemfeat = lookup_fname("SYNSEM");
	lkeysfeat = lookup_fname("LKEYS");
	keyrelfeat = lookup_fname("KEYREL");
	predfeat = lookup_fname("PRED");
	phonfeat = lookup_fname("PHON");
	onsetfeat = lookup_fname("ONSET");
	listfeat = lookup_fname("LIST");
	predsort = lookup_type("predsort");
	con = lookup_type("con");
	voc = lookup_type("voc");
	native_token_list = lookup_type("native_token_list");
}

struct dg	*constrain_lex_rels(struct dg *dg, struct dg *rels)
{
	// XXX shouldn't the do a unification?
	return dg_path_add(dg, lex_rels_path, rels);
}

struct type *predict_onset(char *form)
{
	if(*form=='"')form++;
	if(strchr("aeiouAEIOU", *form))return voc;
	else return con;
}

void	simplify_lexeme(struct lexeme	*l)
{
	struct dg	*dg = l->dg, *ss, *lk, *kr, *pr, *ph, *on, *__tl;

	// check for most common structures and just store parameters for them
	if(l->stemlen != 1)return;
	if(dg->narcs != 2)return;

	// we want just 'ORTH' and 'SYNSEM' features
	if(dg->label[0] != orthfeat && dg->label[1] != orthfeat)return;
	if(dg->label[0] != synsemfeat && dg->label[1] != synsemfeat)return;

	ss = dg_hop(dg, synsemfeat);
	// we want just 'LKEYS' and 'ONSET' or else just LKEYS
	if(ss->narcs == 2)
	{
		if(ss->label[0] != lkeysfeat && ss->label[1] != lkeysfeat)return;
		if(ss->label[0] != phonfeat && ss->label[1] != phonfeat)return;
	}
	else if(ss->narcs==1)
	{
		if(ss->label[0] != lkeysfeat)return;
	}
	else return;

	// check LKEYS branch
	lk = dg_hop(ss, lkeysfeat);
	// we want just 'KEYREL'
	if(lk->narcs != 1 || lk->label[0] != keyrelfeat)return;
	kr = dg_hop(lk, keyrelfeat);
	// we want just 'PRED'
	if(kr->narcs != 1 || kr->label[0] != predfeat)return;
	pr = dg_hop(kr, predfeat);
	// we want l->pred
	if(pr->narcs != 0 || pr->xtype != l->pred)return;

	// check PHON branch
	ph = dg_hop(ss, phonfeat);
	if(!ph)l->onset = 0;
	else
	{
		// we want just 'ONSET'
		if(ph->narcs != 1 || ph->label[0] != onsetfeat)return;
		on = dg_hop(ph, onsetfeat);
		// we want just '--TL'
		if(on->narcs != 1 || on->label[0] != __tlfeat)return;
		__tl = dg_hop(on, __tlfeat);
		// we want 'native_token_list' with no arcs
		if(__tl->xtype != native_token_list || __tl->narcs != 0)return;
		// we want predictable onset
		if(on->xtype != predict_onset(l->stem[0]->name))return;
		l->onset = 1;
	}

	//printf("`%s' has simple form; ph = %p, onset = %d\n", l->word, ph, (int)l->onset);
	nsimpleform++;
	l->dg = 0;
}

struct dg	*expand_lexeme(struct lexeme	*l)
{
	struct dg	*dg, *ss, *lk, *kr, *pr, *st, *f, *ph, *on, *__tl;

	if(l->dg)return l->dg;
	if(!enable_simple_form_lexicon)
		assert(!"Found a simple-form lexeme, but that feature is not enabled!");
	if(orthfeat==-1)init_fnums();

	pr = atomic_dg(top_type);
	pr->xtype = pr->type = l->pred;
	kr = add_dg_hop(atomic_dg(top_type), predfeat, pr);
	lk = add_dg_hop(atomic_dg(top_type), keyrelfeat, kr);
	ss = add_dg_hop(atomic_dg(top_type), lkeysfeat, lk);

	if(l->onset)
	{
		__tl = atomic_dg("native_token_list");
		on = atomic_dg(top_type);
		on->xtype = on->type = predict_onset(l->stem[0]->name);
		on = add_dg_hop(on, __tlfeat, __tl);
		ph = add_dg_hop(atomic_dg(top_type), onsetfeat, on);
		ss = add_dg_hop(ss, phonfeat, ph);
	}

	f = atomic_dg(top_type);
	f->xtype = f->type = l->stem[0];
	st = add_dg_hop(atomic_dg(top_type), ffeat, f);
	st = add_dg_hop(st, rfeat, atomic_dg(g_null_type));
	dg = atomic_dg(top_type);
	dg = add_dg_hop(dg, orthfeat, st);
	dg = add_dg_hop(dg, synsemfeat, ss);

	//printf("expanded `%s':\n", l->word);
	//print_dg(dg);printf("\n");

	dg = wellform_dg(dg);
	assert(dg != NULL);
	return dg;
}

struct lexeme	*get_lex_by_name(char *name)
{
	int	i;

	for(i=0;i<nlexemes;i++)
		if(!strcmp(lexemes[i]->word, name))return lexemes[i];
	return NULL;
}

void print_lexeme(char *name)
{
	struct lexeme	*l = get_lex_by_name(name);
	if(l)
	{
		print_dg(l->dg); printf("\n");
		printf(" lex type %s\n", l->lextype->name);
		print_dg(l->lextype->dg); printf("\n");
	}
}

struct lexeme	*make_lexeme(char	*word, struct dg	*dg, struct type	*type, struct dg	*fulldg)
{
	struct lexeme	*l = malloc(sizeof(struct lexeme));
	struct dg	*stem, *str, *synsem, *lkeys, *keyrel, *pred;
	int			print = 0;

	// XXX hack!
	if(generation > MAX_GEN_RESET)
	{
		fprintf(stderr, "WARNING: generation overflow; bad things may happen\n");
		generation = 11;
	}
	// XXX hack!

	if(synsemfeat==-1)init_fnums();
	l->word = strdup(word);
	l->dg = dg;
	l->stemlen = 0;
	l->stem = 0;
	l->lextype = type;
	l->pred = 0;

	// look up a few interesting ERG-specific paths in lexemes:
	// SYNSEM.LKEYS.KEYREL.PRED is a predsort that the lexeme provides

	/*synsem = dg_hop(fulldg, synsemfeat);
	if(synsem)
	{
		lkeys = dg_hop(synsem, lkeysfeat);
		if(lkeys)
		{
			keyrel = dg_hop(lkeys, keyrelfeat);
			if(keyrel)
			{
				pred = dg_hop(keyrel, predfeat);*/
				pred = dg_path(fulldg, lex_pred_path);
				if(pred && pred->xtype != predsort)
				{
					l->pred = pred->xtype;
					//printf("lex `%s' provides `%s'\n", word, l->pred->name);
				}
			/*}
		}
	}*/

	stem = dg_path(fulldg, lex_stem_path);

	for(;stem;stem = dg_hop(stem, rfeat))
	{
		str = dg_hop(stem, ffeat);
		if(!str)break;	// end of list.
		if(str->type->name[0] != '"' && 0)	// generics sometimes give STEM < *top* >...
		{
			fprintf(stderr, "lexicon: stem[%d] in word `%s' is not a string [%s]\n", l->stemlen, word, str->type->name);
			exit(-1);
		}
		l->stemlen++;
		l->stem = realloc(l->stem, sizeof(struct type*)*l->stemlen);
		l->stem[l->stemlen-1] = str->type;
		if(print)printf("%s[%d] = %s\n", word, l->stemlen, str->type->name);
	}
	if(l->stemlen == 0)
	{
		fprintf(stderr, "lexicon: lexeme `%s' has no stem!\n", word);
		exit(-1);
	}
	if(!stem)
	{
		fprintf(stderr, "lexeme `%s' has open ended stem list!\n", word);
		exit(-1);
	}

	return l;
}

void	add_lexeme(char	*word, struct dg	*dg, struct type	*type, struct dg	*fulldg)
{
	struct lexeme	*l = make_lexeme(word, dg, type, fulldg);
	nlexemes++;
	if(nlexemes > alexemes)
	{
		alexemes += 2048;
		lexemes = realloc(lexemes, sizeof(struct lexeme)*alexemes);
	}
	lexemes[nlexemes-1] = l;

	if(enable_simple_form_lexicon)
		simplify_lexeme(l);

	if(!temporary_expedient(l->word))
		add_semantic_index(l, fulldg, 0);

	//printf("lexeme %s has %d-long stem starting %s\n", word, l->stemlen, l->stem[0]->name);
	//if(nlexemes%100 == 0)printf("lexeme %s             \r", word); fflush(stdout);
	/*printf("lexeme %s  --> ", word);
	print_dg(dg);
	printf("\n");*/
}

int		nexpedients = 0;
char	**expedients = 0;

int	load_expedients(char	*path)
{
	FILE	*f = 0;
	if(!path)return 0;
	f = fopen(path, "r");
	if(f)
	{
		char	exp[1024];
		while(fgets(exp, 1023, f) != NULL)
		{
			if(*exp && exp[strlen(exp)-1]=='\n')
				exp[strlen(exp)-1] = 0;
			if(*exp==0)continue;
			if(*exp==';')continue;
			nexpedients++;
			expedients = realloc(expedients, sizeof(char*)*(nexpedients+1));
			expedients[nexpedients-1] = strdup(trim_string(exp));
			expedients[nexpedients] = NULL;
		}
		fclose(f);
		return 0;
	}
	else
	{
		fprintf(stderr, "unable to load temporary expedients from `%s'\n", path);
		exit(-1);
	}
}

int temporary_expedient(char *sign)
{
	int i;

	for(i=0;i<nexpedients;i++)
		if(!strcasecmp(sign, expedients[i]))return 1;
	return 0;
}

int	study_lexeme(char	*name, struct dg	*dg, struct type	*t)
{
	struct dg	*fulldg;

	fulldg = unify_dg_noss(dg, t->dg, -1);
	if(!fulldg)
	{
		fprintf(stderr, "study_lexeme `%s': dag incompatible with type `%s'\n", name, t->name);
		return -1;
	}

	// example of why we must wellform lexemes before using them,
	// even when t->dg is already wellformed:
	// tuesday_n1 stipulates a CARG value, while its type does not
	// CARG is introduced on const_value_relation,
	// while the lexical type has a nom_relation.
	// wellformedness pushes the relation's type down to the GLB of those.
	// ... note that if 'dg' were already wellformed,
	// then wellformed unification would guarantee that fulldg was already wellformed.
	// however, 'dg' is usually far from wellformed,
	// and wellform-ing it is no cheaper than wellforming fulldg.
	int wellform_result = wellform(fulldg, name);
	assert(wellform_result == 0);

	add_lexeme(name, dg, t, fulldg);

	return 0;
}

int	study_generic_le(char	*name, struct dg	*dg, struct tdl_line	*tdl)
{
	int wellform_result = wellform(dg, name);
	assert(wellform_result == 0);
	//printf("generic_le '%s'\n", name);
	struct lexeme	*l = make_lexeme(name, dg, dg->xtype, dg);
	ngeneric_les++;
	generic_les = realloc(generic_les, sizeof(struct lexeme)*ngeneric_les);
	generic_les[ngeneric_les-1] = l;

	generic_le_infos = realloc(generic_le_infos, sizeof(struct generic_le_info) * ngeneric_les);
	bzero(&generic_le_infos[ngeneric_les-1], sizeof(struct generic_le_info));

	if(check_conf_list("generic-les-for-semantic-index", name))
		generic_le_infos[ngeneric_les-1].for_generation = 1;

	return 0;
}

int	lexcomp(const void	*a, const void	*b)
{
	const struct lexeme	*la = *(const struct lexeme**)a, *lb = *(const struct lexeme**)b;
	int	res;

	if(la->stemlen==0)return -1;
	if(lb->stemlen==0)return 1;
	wchar_t	*sa = towide(la->stem[0]->name);
	wchar_t	*sb = towide(lb->stem[0]->name);
	res = wcscasecmp(sa,sb);
	if(!res)res = strcmp(la->word, lb->word);
	free(sa);
	free(sb);
	return res;
	/*res = strcasecmp(la->stem[0]->name, lb->stem[0]->name);
	if(res)return res;
	else return strcmp(la->word, lb->word);*/
}

int	load_lexicon()
{
	extern int	lexify_tdl_line(struct tdl_line	*line, void	*ref);
	struct timeval tv1, tv2;

	int load_lexicon()
	{
		//gettimeofday(&tv1, 0);
		if(process_tdl_status("lex-entry", lexify_tdl_line, 0))
		{
			fprintf(stderr, "lexicon: unable to load, bailing out.\n");
			exit(-1);
		}
		//gettimeofday(&tv2, 0);
		//show_task_name("loading lexicon...");
		//printf("%.1f secs\n",
			//(tv2.tv_sec - tv1.tv_sec) + 0.000001*(tv2.tv_usec-tv1.tv_usec));
		qsort(lexemes, nlexemes, sizeof(struct lexeme*), lexcomp);

		//show_task_name("generic lexemes");
		if(process_tdl_dgs_status("generic-lex-entry", study_generic_le))
		{
			fprintf(stderr, "lexicon: unable to load generics, bailing out.\n");
			exit(-1);
		}
		return 0;
	}
	run_task("processing lexicon...", load_lexicon);

	show_task_name("simple lexemes");
	printf("%d / %d = %.2f%%\n", nsimpleform, nlexemes, 100*(float)nsimpleform / nlexemes);
	return 0;
}

int	install_substitute_orthography(struct lexeme	*lex, char	*str)
{
	//printf("should install `%s' in L_%s\n", orth, lex->word);
	struct dg	*orth = dg_path(lex->dg, lex_stem_path);
	if(!orth)
	{
		fprintf(stderr, "WARNING: ought to install new orthography `%s' on L_%s, but no orthography path present\n", str, lex->word);
		return 0;
	}

	int	i;
	char	*ptr=NULL;
	assert(lex->stemlen==1);
	//printf("installing `%s' as L_%s's %d'th ORTH value\n", qstr, lex->word, i);
	struct dg	*f = dg_hop(orth, 1);	// FIRST
	struct dg	*r = dg_hop(orth, 2);	// REST
	if(!f)
	{
		//fprintf(stderr, "WARNING: had to add a FIRST for L_%s's %d'th ORTH value\n", lex->word, i);
		f = atomic_dg(str);
		orth = add_dg_hop(orth, 1, f);
	}
	else f->xtype = lookup_type(str);
	if(!r)
	{
		//fprintf(stderr, "WARNING: had to add a REST for L_%s's %d'th ORTH value\n", lex->word, i);
		r = atomic_dg(g_null_type);
		orth = add_dg_hop(orth, 2, r);
	}
	else r->xtype = lookup_type(g_null_type);
	orth = r;
	return 0;
}

struct lexeme	*instantiate_gle(struct lexeme	*gle, char	*surface, char	*carg)
{
	// create a temporary copy of 'gle'
	// stuff 'surface' in as the orthography value
	// stuff 'carg' in as the CARG value
	struct lexeme	*l = slab_alloc(sizeof(*l));
	bzero(l, sizeof(*l));
	int	wl = strlen(gle->word);
	int	sl = strlen(surface);
	char	wordname[wl + 10 + sl];
	sprintf(wordname, "%s[%s]", gle->word, surface);
	l->word = freeze_string(wordname);
	l->dg = copy_dg(gle->dg);
	assert(gle->stemlen == 1);
	l->stemlen = 1;
	l->onset = gle->onset;
	l->stem = slab_alloc(sizeof(struct type*));
	l->lextype = gle->lextype;
	l->pred = gle->pred;

	// set the orthography value
	l->stem[0] = add_string(surface);
	install_substitute_orthography(l, surface);
	// set the CARG value
	
	struct dg	*carg_dg;
	//static int savef[10] = {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1};
	//carg_dg = walk_dg(l->dg, savef, "SYNSEM", "LOCAL", "CONT", "RELS", "LIST", "FIRST", "CARG", NULL);
	carg_dg = dg_path(l->dg, lex_carg_path);
	assert(carg_dg != NULL);
	carg_dg->type = carg_dg->xtype = add_string(carg);
	return l;
}
