#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<math.h>
#include	<wctype.h>

#include	"unicode.h"
#include	"token.h"
#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"hash.h"
#include	"ubertag.h"
#include	"lattice-mapping.h"
#include	"tdl.h"
#include	"freeze.h"

#define	LOGZERO	((double)-9E99)
#define	SMOOTH_EMISSION		(-20)//(-1000)
#define	SMOOTH_TRANSITION	(-20)//(-1000)

//#define	DEBUG(x...)	do { printf(x); } while(0)
#define	DEBUG(x...)

int	enable_ubertagging = 0;

void	ut_normalize_emission(char	*em_mbs)
{
	wchar_t	*em_wcs = towide(em_mbs);
	int	i,j;
	// if there are non-punctuation characters, ditch all peripheral punctuation characters
	for(i=0;em_wcs[i] && em_wcs[i]!= L'▲';i++)if(!iswpunct(em_wcs[i]))break;
	int	first_nonpunct = i;
	if(!em_wcs[first_nonpunct] || em_wcs[first_nonpunct]== L'▲')
	{
		// no non-punctuation characters
		free(em_wcs);
		return;
	}
	// find end
	for(;em_wcs[i] && em_wcs[i]!= L'▲';i++){}
	// find last nonpunct
	for(i--;i>=0;i--)if(!iswpunct(em_wcs[i]))break;
	assert(i>=0);
	int last_nonpunct = i;
	for(i=j=0;em_wcs[i]!=0 && em_wcs[i]!= L'▲';i++)
		if((i>=first_nonpunct && i<=last_nonpunct)||!iswpunct(em_wcs[i]))
			em_wcs[j++] = em_wcs[i];
	// preserve case/class marker
	if(em_wcs[i]==L'▲')
		for(;em_wcs[i];i++)
			em_wcs[j++] = em_wcs[i];
	em_wcs[j]=0;
	char	*new_mbs = tombs(em_wcs);
	//printf("normalize %s -> %s\n", em_mbs, new_mbs);
	strcpy(em_mbs, new_mbs);
	free(new_mbs);
	free(em_wcs);
}

static inline double	logsumexp(double	a, double	b)
{
	if(b>a)return b + log1p(exp(a-b));
	else return a + log1p(exp(b-a));
}

int	ut_lookup_tag(struct ubertagger	*ut, char	*tag, int	insert)
{
	int	*tagi = hash_find(ut->tag_hash,tag);
	if(!tagi)
	{
		if(!insert)return -1;
		tagi = malloc(sizeof(int));
		*tagi = ut->ntags++;
		ut->tags = realloc(ut->tags, sizeof(char*)*ut->ntags);
		ut->tags[*tagi] = strdup(tag);
		hash_add(ut->tag_hash, ut->tags[*tagi], tagi);
	}
	return *tagi;
}

int	ut_lookup_classcase(struct ubertagger	*ut, char	*classcase, int	insert)
{
	int	*cci = hash_find(ut->classcase_hash,classcase);
	if(!cci)
	{
		if(!insert)return -1;
		cci = malloc(sizeof(int));
		*cci = ut->nclasscases++;
		ut->classcases = realloc(ut->classcases, sizeof(char*)*ut->nclasscases);
		ut->classcases[*cci] = strdup(classcase);
		hash_add(ut->classcase_hash, ut->classcases[*cci], cci);
	}
	return *cci;
}

double	ut_score_ex(struct ubertagger	*ut, int	tag, char	*emission, int	classcase)
{
	//double	score = SMOOTH_EMISSION;
	//void	visitor(struct ut_emission	*e) { if(e->tag == tag)score = e->score; }
	//hash_visit_key(ut->emission_hash, emission, (void(*)(void*))visitor);
	//return score;
	int	ecmp(const struct ut_emission	*a, const struct ut_emission	*b)
	{
		char	*sa = ut->emissions + a->offset;
		char	*sb = ut->emissions + b->offset;
		if(a->offset==-1)sa = emission;
		if(b->offset==-1)sb = emission;
		int	s = strcmp(sa, sb);
		if(s)return s;
		s = ((int)a->classcase) - (int)b->classcase;
		if(s)return s;
		s = ((int)a->tag) - (int)b->tag;
		return s;
	}
	struct ut_emission	EM = {-1,tag,classcase,0};
	struct ut_emission	*em = bsearch(&EM, ut->emission_tagscores, ut->nemissions, sizeof(struct ut_emission), (int(*)(const void*,const void*))ecmp);
	if(em)return em->score;
	else return SMOOTH_EMISSION;
}

ut_load_ex(struct ubertagger	*ut, char	*expath)
{
	char	*gzsuffix = strstr(expath, ".gz");
	int	zipped = (gzsuffix && strlen(gzsuffix)==3)?1:0;
	char	unzipper[10240];
#ifdef __APPLE__
	if(zipped)sprintf(unzipper, "gzcat %s", expath);
#else
	if(zipped)sprintf(unzipper, "zcat %s", expath);
#endif
	FILE	*f = zipped?popen(unzipper,"r"):fopen(expath,"r");
	if(!f){perror(expath);exit(-1);}

	struct hash	*ehash = hash_new("ut-emit");
	ut->classcase_hash = hash_new("ut-classcase");
	int	alemissions = 1024000;
	ut->emissions = calloc(alemissions,1);
	int	aemissions = 0;
	struct ut_emission	**eptrs = NULL;
	assert(0 == ut_lookup_classcase(ut, "", 1));

	char	line[10240];
	char	tag[10240], emission[10240];
	double	score;
	while(fgets(line,10239,f))
	{
		if(line[0]=='%')continue;
		if(line[0]=='\n')continue;
		if(3 != sscanf(line,"%[^	]	%[^	]	%lf\n",tag,emission,&score))
		{
			fprintf(stderr, "ERROR: malformed ubertagger line: %s", line);
			exit(-1);
		}
		char	*sep = strstr(emission, "▲");
		int		classcase = 0;
		if(sep)
		{
			*sep = 0;
			classcase = ut_lookup_classcase(ut, sep+strlen("▲"), 1);
		}
		ut_normalize_emission(emission);
		int tagid = ut_lookup_tag(ut, tag, 1);
		// this emission may already be in our table, since we're normalizing (collapsing the space of emissions sometimes)
		struct ut_emission	*em = NULL;
		void visitor(struct ut_emission	*e) { if(e->tag==tagid && e->classcase == classcase)em=e; }
		hash_visit_key(ehash, emission, (void(*)(void*))visitor);
		if(!em)
		{
			em = malloc(sizeof(*em));
			em->tag = tagid;
			em->classcase = classcase;
			em->score = score;
			int	l = strlen(emission);
			while(ut->lemissions + l+1 > alemissions)
			{
				alemissions *= 2;
				ut->emissions = realloc(ut->emissions, alemissions);
			}
			strcpy(ut->emissions+ut->lemissions, emission);
			em->offset = ut->lemissions;
			ut->lemissions += l+1;
			hash_add(ehash, strdup(emission), em);
		}
		else em->score = logsumexp(em->score, score);
		ut->nemissions++;
		if(ut->nemissions > aemissions)
		{
			aemissions = 2*ut->nemissions;
			eptrs = realloc(eptrs, sizeof(struct ut_emission)*aemissions);
		}
		eptrs[ut->nemissions-1] = em;
	}
	if(zipped)pclose(f);
	else fclose(f);
	//printf("loaded %d emissions\n", ut->nemissions);

	int	epcmp(const struct ut_emission	**a, const struct ut_emission	**b)
	{
		int	s = strcmp(ut->emissions + (*a)->offset, ut->emissions + (*b)->offset);
		if(s)return s;
		s = ((int)(*a)->classcase) - (int)(*b)->classcase;
		if(s)return s;
		s = ((int)(*a)->tag) - (int)(*b)->tag;
		return s;
	}
	qsort(eptrs, ut->nemissions, sizeof(void*), (int(*)(const void*,const void*))epcmp);

	ut->emission_tagscores = malloc(sizeof(struct ut_emission) * ut->nemissions);
	int i;
	for(i=0;i<ut->nemissions;i++)
		ut->emission_tagscores[i] = *eptrs[i];
	hash_free(ehash);
}

ut_add_trans3(struct ubertagger	*ut, short	tags[3], float	score)
{
	struct ut_transition_set	*ts = &ut->trans[tags[0]];
	ts->ntrans3++;
	if(ts->ntrans3 > ts->atrans3)
	{
		if(!ts->atrans3)ts->atrans3 = 1;
		else ts->atrans3 *= 2;
		ts->trans3 = realloc(ts->trans3, sizeof(struct ut_transition)*ts->atrans3);
	}
	struct ut_transition	*T = ts->trans3 + ts->ntrans3-1;
	T->t2 = tags[1];
	T->t3 = tags[2];
	T->score = score;
}

ut_add_trans2(struct ubertagger	*ut, short	tags[2], float	score)
{
	struct ut_transition_set	*ts = &ut->trans[tags[0]];
	ts->ntrans2++;
	if(ts->ntrans2 > ts->atrans2)
	{
		if(!ts->atrans2)ts->atrans2 = 1;
		else ts->atrans2 *= 2;
		ts->trans2 = realloc(ts->trans2, sizeof(struct ut_transition)*ts->atrans2);
	}
	struct ut_transition	*T = ts->trans2 + ts->ntrans2-1;
	T->t2 = tags[0];
	T->t3 = tags[1];
	T->score = score;
}

int	ut_trans_cmp(const struct ut_transition	*a, const struct ut_transition	*b)
{
	if(a->t2 != b->t2)return ((int)a->t2) - (int)b->t2;
	return ((int)a->t3) - (int)b->t3;
}

double	ut_score_tx(struct ubertagger	*ut, int	t1, int	t2, int	t3)
{
	struct ut_transition	*t, T = {t2,t3,0};
	t = bsearch(&T, ut->trans[t1].trans3, ut->trans[t1].ntrans3, sizeof(T), (int(*)(const void*,const void*))ut_trans_cmp);
	if(t)
	{
		//printf("found %s %s %s -> %f\n", ut->tags[t1], ut->tags[t2], ut->tags[t3], t->score);
		return t->score;
	}
	t = bsearch(&T, ut->trans[t2].trans2, ut->trans[t2].ntrans2, sizeof(T), (int(*)(const void*,const void*))ut_trans_cmp);
	if(t)
	{
		//printf("backoff %s %s -> %f\n", ut->tags[t2], ut->tags[t3], t->score);
		return t->score;
	}
	return ut->trans[t3].unigram_score;

	/*short	tags[3] = {t1,t2,t3};
	void	*scp = hash_find(ut->transition_trigram, (void*)tags);
	if(scp)return *(double*)&scp;
	scp = hash_find(ut->transition_bigram, (void*)&tags[1]);
	if(scp)return *(double*)&scp;
	return ut->transition_unigram[t3];*/
}

ut_load_tx(struct ubertagger	*ut, char	*txpath)
{
	char	*gzsuffix = strstr(txpath, ".gz");
	int	zipped = (gzsuffix && strlen(gzsuffix)==3)?1:0;
	char	unzipper[10240];
#ifdef	__APPLE__
	if(zipped)sprintf(unzipper, "gzcat %s", txpath);
#else
	if(zipped)sprintf(unzipper, "zcat %s", txpath);
#endif
	FILE	*f = zipped?popen(unzipper,"r"):fopen(txpath,"r");
	if(!f){perror(txpath);exit(-1);}

	ut->trans = calloc(sizeof(struct ut_transition_set),ut->ntags);
	ut->trans[ut->unk_tag].unigram_score = SMOOTH_TRANSITION;

	//ut->transition_trigram = hash_new("ut-3gram");
	//ut->transition_trigram->has_flk = 6;
	//ut->transition_bigram = hash_new("ut-2gram");
	//ut->transition_bigram->has_flk = 4;
	//ut->transition_unigram = calloc(sizeof(double),ut->ntags+1000);
	//printf("ntags before loading tx = %d\n", ut->ntags);
	char	line[10240];
	char	tag1[10240], tag2[10240], tag3[10240];
	double	score;
	int		ntrans[3] = {0,0,0};
	while(fgets(line,10239,f))
	{
		if(line[0]=='%')continue;
		if(line[0]=='\n')continue;
		if(4 == sscanf(line,"%[^	]	%[^	]	%[^	]	%lf\n",tag1,tag2,tag3,&score))
		{
			short	*tags=malloc(6);
			tags[0] = ut_lookup_tag(ut, tag1, 0);
			tags[1] = ut_lookup_tag(ut, tag2, 0);
			tags[2] = ut_lookup_tag(ut, tag3, 0);
			assert(tags[0]!=-1 && tags[1]!=-1 && tags[2]!=-1);
			//hash_add(ut->transition_trigram, (void*)tags, *(void**)&score);
			ut_add_trans3(ut, tags, (float)score);
			ntrans[0]++;
		}
		else if(3 == sscanf(line,"%[^	]	%[^	]	%lf\n",tag1,tag2,&score))
		{
			short	*tags=malloc(4);
			tags[0] = ut_lookup_tag(ut, tag1, 0);
			tags[1] = ut_lookup_tag(ut, tag2, 0);
			assert(tags[0]!=-1 && tags[1]!=-1);
			//hash_add(ut->transition_bigram, (void*)tags, *(void**)&score);
			ut_add_trans2(ut, tags, (float)score);
			ntrans[1]++;
		}
		else if(2 == sscanf(line,"%[^	]	%lf\n",tag1,&score))
		{
			int	t1 = ut_lookup_tag(ut, tag1, 0);
			assert(t1!=-1);
			//ut->transition_unigram[t1] = score;
			ut->trans[t1].unigram_score = score;
			ntrans[2]++;
		}
		else
		{
			fprintf(stderr, "ERROR: malformed ubertagger line: %s", line);
			exit(-1);
		}
	}
	if(zipped)pclose(f);
	else fclose(f);
	//printf("loaded %d / %d / %d transitions\n", ntrans[0], ntrans[1], ntrans[2]);

	int i;
	for(i=0;i<ut->ntags;i++)
	{
		qsort(ut->trans[i].trans3, ut->trans[i].ntrans3, sizeof(struct ut_transition), (int(*)(const void*,const void*))ut_trans_cmp);
		qsort(ut->trans[i].trans2, ut->trans[i].ntrans2, sizeof(struct ut_transition), (int(*)(const void*,const void*))ut_trans_cmp);
	}
}

ut_load_gm(struct ubertagger	*ut, char	*genmappath)
{
	FILE	*f = fopen(genmappath, "r");
	if(!f){perror(genmappath);exit(-1);}
	ut->ltmap = hash_new("lextype-map");
	char	type[1024], tag[1024];
	while(2==fscanf(f,"%[^	]	%[^\n]\n", type, tag))
	{
		//printf("map %s -> %s\n", type, tag);
		hash_add(ut->ltmap, strdup(type), strdup(tag));
	}
	fclose(f);
	/*
	// FIXME this is hardcoded in PET too (as a backup) and I don't have access to a config file for it at the moment(?).
	hash_add(ut->ltmap, strdup("aj_-_i-cmp-unk_le"), "aj_pp_i-cmp_le");
	hash_add(ut->ltmap, strdup("aj_-_i-crd-gen_le"), "aj_-_i-crd-two_le");
	hash_add(ut->ltmap, strdup("aj_-_i-crd-unk_le"), "aj_-_i-crd-two_le");
	hash_add(ut->ltmap, strdup("aj_-_i-frct-gen_le"), "aj_-_i-frct_le");
	hash_add(ut->ltmap, strdup("aj_-_i-ord-gen_le"), "aj_-_i-ord-two_le");
	hash_add(ut->ltmap, strdup("aj_-_i-sup-unk_le"), "aj_-_i-sup_le");
	hash_add(ut->ltmap, strdup("aj_-_i-unk_le"), "aj_-_i_le");
	hash_add(ut->ltmap, strdup("aj_np_i-crd-gen_le"), "aj_np_i-crd-nsp_le");
	hash_add(ut->ltmap, strdup("av_-_dc-like-unk_le"), "av_-_dc-like-pr_le");
	hash_add(ut->ltmap, strdup("av_-_i-unk_le"), "av_-_i-vp_le");
	hash_add(ut->ltmap, strdup("n_-_c-pl-gen_le"), "n_-_mc_le:n_pl_olr");
	hash_add(ut->ltmap, strdup("n_-_c-pl-unk_le"), "n_-_mc_le:n_pl_olr");
	hash_add(ut->ltmap, strdup("n_-_day-crd-gen_le"), "n_-_c-day_le");
	hash_add(ut->ltmap, strdup("n_-_mc-ns-g_le"), "n_-_mc-ns_le");
	hash_add(ut->ltmap, strdup("n_-_mc-unk_le"), "n_-_mc_le");
	hash_add(ut->ltmap, strdup("n_-_meas-n-gen_le"), "n_-_c-meas_le");
	hash_add(ut->ltmap, strdup("n_-_pn-dom-e-gen_le"), "n_-_pn-dom-euro_le");
	hash_add(ut->ltmap, strdup("n_-_pn-dom-gen_le"), "n_-_pn-dom-card_le");
	hash_add(ut->ltmap, strdup("n_-_pn-dom-o-gen_le"), "n_-_pn-dom-ord_le");
	hash_add(ut->ltmap, strdup("n_-_pn-gen_le"), "n_-_pn_le");
	hash_add(ut->ltmap, strdup("n_-_pn-pl-unk_le"), "n_-_pn-pl_le");
	hash_add(ut->ltmap, strdup("n_-_pn-unk_le"), "n_-_pn_le");
	hash_add(ut->ltmap, strdup("n_np_pn-hour-gen_le"), "n_-_pn-hour_le");
	hash_add(ut->ltmap, strdup("v_-_pas-unk_le"), "v_-_psv_le");
	hash_add(ut->ltmap, strdup("v_np*_bse-unk_le"), "v_np*_le:v_n3s-bse_ilr");
	hash_add(ut->ltmap, strdup("v_np*_pa-unk_le"), "v_np*_le:v_pst_olr");
	hash_add(ut->ltmap, strdup("v_np*_pr-3s-unk_le"), "v_np*_le:v_3s-fin_olr");
	hash_add(ut->ltmap, strdup("v_np*_pr-n3s-unk_le"), "v_np*_le:v_n3s-bse_ilr");
	hash_add(ut->ltmap, strdup("v_np*_prp-unk_le"), "v_np*_le:v_prp_olr");
	hash_add(ut->ltmap, strdup("v_np*_psp-unk_le"), "v_np*_le:v_psp_olr");
	hash_add(ut->ltmap, strdup("v_np*_unk_le"), "v_np*_le");
	*/
}

struct ubertagger	*load_ubertagger(char	*expath, char	*txpath, char	*genmappath)
{
	struct ubertagger	*ut = calloc(sizeof(struct ubertagger),1);
	ut->tag_hash = hash_new("ut-tags");
	ut->start_tag = ut_lookup_tag(ut, "<S>", 1);
	ut->end_tag = ut_lookup_tag(ut, "<E>", 1);
	ut->unk_tag = ut_lookup_tag(ut, "<U>", 1);
	//printf("loading %s\n", expath);
	ut_load_ex(ut,expath);
	//printf("loading %s\n", txpath);
	ut_load_tx(ut,txpath);
	//assert(ut->start_tag != -1 && ut->end_tag != -1);
	//printf("loading %s\n", genmappath);
	ut_load_gm(ut,genmappath);
	//printf("loaded ubertagger with %d tags\n", ut->ntags);
	/*printf("UT	tags	%zd\n", hash_memory_usage(ut->tag_hash));
	printf("UT	emis	%zd\n", hash_memory_usage(ut->emission_hash));
	printf("UT	tra3	%zd\n", hash_memory_usage(ut->transition_trigram));
	printf("UT	tra2	%zd\n", hash_memory_usage(ut->transition_bigram));
	printf("UT	ltmap	%zd\n", hash_memory_usage(ut->ltmap));*/
	int i, t_ram = 0, t2_ram = 0, t3_ram = 0;
	for(i=0;i<ut->ntags;i++)
	{
		t_ram += sizeof(struct ut_transition_set);
		t2_ram += sizeof(struct ut_transition)*ut->trans[i].ntrans2;
		t3_ram += sizeof(struct ut_transition)*ut->trans[i].ntrans3;
	}
	//printf("UT	trans	%d structures; %d t2 ; %d t3\n", t_ram, t2_ram, t3_ram);
	//printf("UT	emiss	%zd structures; %d strings\n", ut->nemissions * sizeof(struct ut_emission), ut->lemissions);
	return ut;
}

void load_hashlist(struct hash	*h, char	*path)
{
	FILE	*f = fopen(path, "r");
	if(!f){perror(path);exit(-1);}
	char	line[102400];
	while(fgets(line,102399,f))
	{
		char	*p = trim_string(line);
		hash_add(h, strdup(p), (void*)1L);
	}
	fclose(f);
}

struct ubertagger	*the_ubertagger;

int	load_ubertagging()
{
	char	*expath = get_conf_file_path("übertag-emission-path")?:get_conf_file_path("ubertag-emission-path");
	char	*txpath = get_conf_file_path("übertag-transition-path")?:get_conf_file_path("ubertag-transition-path");
	char	*gmpath = get_conf_file_path("übertag-generic-map-path")?:get_conf_file_path("ubertag-generic-map-path");
	char	*wlpath = get_conf_file_path("übertag-whitelist-path")?:get_conf_file_path("ubertag-whitelist-path");

	if(!expath || !txpath || !gmpath)return -1;
	
	//the_ubertagger = load_ubertagger("/home/sweaglesw/cdev/erg-1214/ut/nanc_wsj_redwoods_noaffix.ex.gz","/home/sweaglesw/cdev/erg-1214/ut/nanc_wsj_redwoods_noaffix.tx.gz", "/home/sweaglesw/cdev/erg-1214/ut/generics.cfg");
	the_ubertagger = load_ubertagger(expath,txpath,gmpath);
	if(!the_ubertagger)return -1;
	the_ubertagger->whitelist = hash_new("ut-whitelist");
	if(wlpath)load_hashlist(the_ubertagger->whitelist, wlpath);
	return 0;
}

ut_freeze_string_table(struct hash	*h, char	**strings, int	nstrings, char	**oldstrings)
{
	struct hash_bucket	*walk;
	int i;
	bzero(strings, sizeof(char*)*nstrings);
	for(i=0;i<h->size;i++)
		for(walk=h->buckets[i];walk;walk=walk->next)
		{
			walk->value = freeze_block(walk->value,sizeof(int));
			int	idx = *(int*)walk->value;
			assert(idx>=0 && idx<nstrings);
			strings[idx] = walk->key;
		}
	// freeze any strings that didn't get hit by the hash table
	for(i=0;i<nstrings;i++)
		if(!strings[i])
			strings[i] = freeze_string(oldstrings[i]);
}

void	*freeze_ubertagger()
{
	if(!the_ubertagger)return NULL;
	struct ubertagger	*u = slab_alloc(sizeof(*u));
	*u = *the_ubertagger;
	int	i;
	u->tags = slab_alloc(sizeof(char*)*u->ntags);
	u->tag_hash = freeze_hash(the_ubertagger->tag_hash);
	ut_freeze_string_table(u->tag_hash, u->tags, u->ntags, the_ubertagger->tags);
	u->classcases = slab_alloc(sizeof(char*)*u->nclasscases);
	u->classcase_hash = freeze_hash(the_ubertagger->classcase_hash);
	ut_freeze_string_table(u->classcase_hash, u->classcases, u->nclasscases, the_ubertagger->classcases);
	u->ltmap = freeze_string_hash(the_ubertagger->ltmap);
	u->emissions = freeze_block(the_ubertagger->emissions, u->lemissions);
	u->emission_tagscores = freeze_block(the_ubertagger->emission_tagscores, u->nemissions * sizeof(struct ut_emission));
	u->trans = slab_alloc(sizeof(struct ut_transition_set)*u->ntags);
	for(i=0;i<u->ntags;i++)
	{
		struct ut_transition_set	*t = &u->trans[i];
		u->trans[i] = the_ubertagger->trans[i];
		t->atrans3 = t->ntrans3;
		t->atrans2 = t->ntrans2;
		t->trans3 = freeze_block(t->trans3, sizeof(struct ut_transition)*t->ntrans3);
		t->trans2 = freeze_block(t->trans2, sizeof(struct ut_transition)*t->ntrans2);
	}
	u->whitelist = freeze_hash(the_ubertagger->whitelist);
	//printf("UT whitelist to freeze flk = %d\n", u->whitelist->has_flk);
	the_ubertagger = u;
	return u;
}

void	recover_ubertagger(void	*u)
{
	the_ubertagger = u;
}

struct edge	*ut_get_lexedge(struct edge	*e)
{
	while(e->have)e = e->daughters[0];
	return e;
}

char	*ut_get_lextag(struct ubertagger	*ut, struct edge	*e, int	len)
{
	if(e->have)
	{
		if(strstr(e->rule->name, "_plr"))
			return ut_get_lextag(ut, e->daughters[0], len);
		char	*s = ut_get_lextag(ut, e->daughters[0], len + 1 + strlen(e->rule->name));
		strcat(s, ":");
		strcat(s, e->rule->name);
		return s;
	}
	else
	{
		char	*ltname = e->lex->lextype->name;
		char	*mapped = hash_find(ut->ltmap, ltname);
		if(mapped)ltname = mapped;
		char	*s = malloc(len + strlen(ltname) + 1);
		strcpy(s, ltname);
		return s;
	}
}

int	ubertag_whitelist_check(struct edge	*e)
{
	//printf("how about %s?\n", e->lex->word);
	while(1)
	{
		if(e->rule)
		{
			if(hash_find(the_ubertagger->whitelist, e->rule->name))
			{
				//printf("whitelist saved rule %s\n", e->rule->name);
				return 1;
			}
		}
		else if(hash_find(the_ubertagger->whitelist, e->lex->word))
		{
			//printf("whitelist saved %s\n", e->lex->word);
			return 1;
		}
		//else printf("whitelist didn't save %s\n", e->lex->word);
		if(!e->have)break;
		e = e->daughters[0];
	}
	return 0;
}

// lexical chart has an edge for each possible tag of each possible token
void	ubertag_lattice(struct ubertagger	*ut, struct lattice	*ll, double	thresh)
{
	// forward: compute P(tag X-1 and token X-1 and tag X and token X | observations up to X)
	// i.e. for each vertex, for each pair of incoming/outgoing token_tags, compute a P
	int	i, j;
	int	a,b;
	int		tags[ll->nedges];
	char	*tagnames[ll->nedges];
	int		npreceding_tags[ll->nedges];
	int		*preceding_tags[ll->nedges];
	double	*preceding_tag_scores[ll->nedges];
	double	*backward[ll->nedges];
	double	emission[ll->nedges];
	double	forward_sum[ll->nvertices];
	double	forward_sum_end = 0;
	// especially since plr are ignored in tag names, multiple lexical edges can have identical tags.
	// only want to score each tag once in the lattice, to avoid biasing computations.
	int	is_duplicate[ll->nedges];
	// first, fetch tag ID numbers for each tag_token and initialize forward scores to LOGZERO
	for(i=0;i<ll->nedges;i++)
	{
		struct lattice_edge	*e = ll->edges[i];
		char	*tagname = ut_get_lextag(ut, e->edge,0);
		tagnames[i] = tagname;
		struct edge	*lexedge = ut_get_lexedge(e->edge);
		struct token	*tok0 = (struct token*)lexedge->daughters[0];
		struct dg	*class = dg_hop(tok0->dg, lookup_fname("+CLASS"));
		assert(class);
		struct dg	*tcase = dg_hop(class, lookup_fname("+CASE"));
		struct dg	*carg = dg_hop(tok0->dg, lookup_fname("+CARG"));
		char	*emission_string;
		int		classcase = 0;
		//printf("class %s\n", class->xtype->name);
		if(!tcase && carg && carg->xtype->name[0]=='"')
		{
			emission_string = strdup(carg->xtype->name+1);
			assert(emission_string[0]);
			emission_string[strlen(emission_string)-1] = 0;
		}
		else
		{
			assert(tcase);
			char	*tcasestring = tcase->xtype->name;
			int	elen = 5 + strlen(tcasestring);
			for(j=0;j<lexedge->lex->stemlen;j++)
			{
				struct token	*tok = (struct token*)lexedge->daughters[j];
				struct dg	*form = dg_hop(tok->dg, lookup_fname("+FORM"));
				assert(form);
				elen += (j?1:0) + strlen(form->xtype->name)-2;
			}
			emission_string = malloc(elen+1);
			elen = 0;
			for(j=0;j<lexedge->lex->stemlen;j++)
			{
				struct token	*tok = (struct token*)lexedge->daughters[j];
				struct dg	*form = dg_hop(tok->dg, lookup_fname("+FORM"));
				assert(form);
				if(j)strcpy(emission_string+ elen++, " ");
				strcpy(emission_string+elen, form->xtype->name+1);
				elen += strlen(form->xtype->name)-2;
				emission_string[elen]=0;
			}
			/*strcpy(emission_string+elen, "▲");
			elen += strlen("▲");
			strcpy(emission_string+elen, tcasestring);*/
			classcase = ut_lookup_classcase(ut, tcasestring, 0);
		}
		ut_normalize_emission(emission_string);
		tags[i] = ut_lookup_tag(ut, tagname, 0);
		if(tags[i]==-1)tags[i] = ut->unk_tag;
		is_duplicate[i] = 0;
		for(j=0;j<i;j++)
		{
			if(tags[j]==tags[i] && ll->edges[i]->from==ll->edges[j]->from && ll->edges[i]->to==ll->edges[j]->to)
			{
				// identical tag numbers isn't good enough for UNK;
				// tagnames could still differ. want a separate path through
				// the lattice active for each tagname.
				if(tags[i]!=ut->unk_tag || !strcmp(tagnames[j],tagnames[i]))
					is_duplicate[i] = j+1;
			}
		}
		emission[i] = ut_score_ex(ut, tags[i], emission_string, classcase);
		DEBUG("looked up %s => %d	//	emit |%s| with score %f\n", tagname, (tags[i]==ut->start_tag)?-1:tags[i], emission_string, emission[i]);
		free(emission_string);
		npreceding_tags[i] = 0;
		preceding_tags[i] = malloc(sizeof(int)*ut->ntags);
		preceding_tag_scores[i] = malloc(sizeof(double)*ut->ntags);
		backward[i] = malloc(sizeof(double)*ut->ntags);
		for(j=0;j<ut->ntags;j++)preceding_tag_scores[i][j] = LOGZERO;
		if(e->from == ll->start)
		{
			double	tx = ut_score_tx(ut, ut->start_tag, ut->start_tag, tags[i]);
			//printf("score to start with %s = %f + %f\n", ut->tags[tags[i]], tx, emission[i]);
			preceding_tag_scores[i][ut->start_tag] = tx + emission[i];
			npreceding_tags[i]++;
			preceding_tags[i][npreceding_tags[i]-1] = ut->start_tag;
		}
	}
	// precompute list of plausible tag IDs that come before each tag_token
	for(i=0;i<ll->nedges;i++)
	{
		struct lattice_edge	*e = ll->edges[i];
		struct lattice_vertex	*v = e->to;
		if(is_duplicate[i])continue;
		for(j=0;j<v->nfollowers;j++)
		{
			struct lattice_edge	*f = v->followers[j];
			int	fi;
			for(fi=0;fi<ll->nedges;fi++)if(ll->edges[fi]==f)break;
			assert(fi<ll->nedges);
			npreceding_tags[fi]++;
			preceding_tags[fi][npreceding_tags[fi]-1] = tags[i];
		}
	}
	// march across the sentence in vertex order
	for(i=0;i<ll->nvertices;i++)
	{
		struct lattice_vertex	*v = ll->vertices[i];
		/*if(v != ll->start)
		{
			printf("reached vertex %d\n", i);
			// normalize scores of all edges terminating at 'v' to sum to 1
			double	vtotal = LOGZERO;
			for(a=0;a<ll->nedges;a++) if(ll->edges[a]->to==v)
				for(j=0;j<npreceding_tags[a];j++)
				{
					printf(" arriving by %s %s = %f\n", ut->tags[preceding_tags[a][j]], ut->tags[tags[a]], preceding_tag_scores[a][preceding_tags[a][j]]);
					vtotal = logsumexp(vtotal, preceding_tag_scores[a][preceding_tags[a][j]]);
				}
			forward_sum[i] = vtotal;
			for(a=0;a<ll->nedges;a++) if(ll->edges[a]->to==v)
				for(j=0;j<npreceding_tags[a];j++)
				{
					preceding_tag_scores[a][preceding_tags[a][j]] -= vtotal;
					printf("normalized P(%s %s | preceding) = %f\n", ut->tags[preceding_tags[a][j]], ut->tags[tags[a]], preceding_tag_scores[a][preceding_tags[a][j]]);
				}
		}
		else forward_sum[i] = 0;*/
		// look forward from 'v'
		for(a=0;a<ll->nedges;a++) if(!is_duplicate[a] && ll->edges[a]->to==v)
		{
			// 'a' loops over all edges ending at 'v'
			for(j=0;j<v->nfollowers;j++)
			{
				struct lattice_edge	*be = v->followers[j];
				for(b=0;b<ll->nedges;b++)if(ll->edges[b]==be)break;	// FIXME this is inefficient; squanders advantage from ->followers
				assert(b<ll->nedges);
				if(is_duplicate[b])continue;
				// 'b' loops over all edges following 'v'
				// a->v->b is a tag bigram; sum into b's probabilities for all possible preceding tags T (so t a b is the tag sequence)
				int t, ti;
				for(ti=0;ti<npreceding_tags[a];ti++)
				{
					t = preceding_tags[a][ti];
					double	tx = ut_score_tx(ut, t,tags[a],tags[b]);
					double	ex = emission[b];
					double	prev = preceding_tag_scores[a][t];
					double	score = prev + tx + ex;
					//printf("approach %s %s -> %s local score %f\n", ut->tags[t], ut->tags[tags[a]], ut->tags[tags[b]], score);
					preceding_tag_scores[b][tags[a]] =
						logsumexp(preceding_tag_scores[b][tags[a]], score);
				}
			}
		}
	}

	// compute probability of hitting end
	double	end_p = LOGZERO;
	for(i=0;i<ll->nedges;i++)
	{
		struct lattice_edge	*e = ll->edges[i];
		if(e->to != ll->end)continue;
		if(is_duplicate[i])continue;
		double	e_score = LOGZERO;
		for(j=0;j<npreceding_tags[i];j++)
		{
			int	pt = preceding_tags[i][j];
			double	tx = ut_score_tx(ut, pt, tags[i], ut->end_tag);
			double	prev = preceding_tag_scores[i][pt];
			double	score = prev+tx;	// no emission score for <E> tag
			e_score = logsumexp(e_score, score);
		}
		//printf("score to end on %s = %f\n", ut->tags[tags[i]], e_score);
		end_p = logsumexp(end_p, e_score);
	}
	//printf("score to end at all = %f\n", end_p);
	forward_sum_end = end_p;

	// now in possession of P(X_t-1 X_t | O_1...t)
	//  ...fore[X,Y] = P(we hit X and Y and see all the observations up to Y | observations up to Y)


	// backward probabilities
	// want back[X,t] = P(O_t+1...N | X_t-1 X_t)
	// e.g. back[X,N] = 1
	// back[X,N-1] = P(O_N | X_N-2 X_N-1) = transition probability from <X_N-2 X_N-1> to <E>
	// intuitive: back[X,Y,k] = sum over Y's followers Z [   transition(X,Y,Z) * emission(Z) * back[Y,Z,k+1]  ]

	for(i=ll->nvertices-1;i>=0;i--)
	{
		struct lattice_vertex	*v = ll->vertices[i];
		//printf("back-reached vertex %d\n", i);
		for(b=0;b<ll->nedges;b++) if(ll->edges[b]->to==v)
		{
			if(is_duplicate[b])continue;
			struct lattice_edge	*Y = ll->edges[b];
			int	Yt = tags[b];
			for(j=0;j<npreceding_tags[b];j++)
			{
				int	Xt = preceding_tags[b][j];
				if(v==ll->end)
					backward[b][Xt] = ut_score_tx(ut, Xt, Yt, ut->end_tag);
				else
				{
					backward[b][Xt] = LOGZERO;
					int z;
					for(z=0;z<ll->nedges;z++) if(!is_duplicate[z] && ll->edges[z]->from==v)
					{
						int	Zt = tags[z];
						double	score = ut_score_tx(ut, Xt, Yt, Zt) + emission[z] + backward[z][Yt];
						backward[b][Xt] = logsumexp(backward[b][Xt], score);
					}
				}
				//printf("onwards from %s %s = %f\n", ut->tags[Xt], ut->tags[Yt], backward[b][Xt]);
			}
		}
	}

	// then have back[X,Y] = P(observations following Y | we hit X and Y)
	// = P(observations following Y | we hit X and Y and see all the observations up to Y) [ by conditional independence ]

	// multiplying:  back[X,Y] * fore[X,Y] = P(we hit X and Y and see all the observations | observations up to Y)
	// may need to keep a normalization factor handy to just get P(we hit X and Y)
	// in p'tic, multiply by P(observations up to Y) [=sum of forewards at Y->to] and divide by P(all observations) [=sum of forewards at ll->end]

	int	new_nedges = 0;
	int	i_true;
	// look at all lexical edges including duplicates, but score by the first equivalent representative
	for(i_true=0;i_true<ll->nedges;i_true++)
	{
		double	e_total = LOGZERO;
		i = is_duplicate[i_true]?(is_duplicate[i_true]-1):i_true;
		for(j=0;j<npreceding_tags[i];j++)
		{
			double	fw = preceding_tag_scores[i][preceding_tags[i][j]];
			double	bw = backward[i][preceding_tags[i][j]];
			double	p_x_y = fw + bw;// + forward_sum[i] - foward_sum_end;
			p_x_y -= forward_sum_end;
			//if(p_x_y > -1000000)
			//	printf("%s %s	=> %f + %f =	%f\n", ut->tags[preceding_tags[i][j]], ut->tags[tags[i]], fw, bw, p_x_y);
			e_total = logsumexp(e_total, p_x_y);
		}
		DEBUG("%s	%s	=>	%f	=>	%f\n", ll->edges[i_true]->edge->lex->word, ut->tags[tags[i]], e_total, exp(e_total));
		if(e_total >= thresh || ubertag_whitelist_check(ll->edges[i_true]->edge))
		{
			//printf("keeping %s / %s\n", tagnames[i_true], ll->edges[i_true]->edge->lex->word);
			DEBUG("	KEEP\n");
			ll->edges[new_nedges++] = ll->edges[i_true];
		}
		else
		{
			//printf("discard %s / %s\n", tagnames[i_true], ll->edges[i_true]->edge->lex->word);
			DEBUG("	DISCARD\n");
		}
	}

	for(i=0;i<ll->nedges;i++)
	{
		free(backward[i]);
		free(preceding_tags[i]);
		free(preceding_tag_scores[i]);
		free(tagnames[i]);
	}
	ll->nedges = new_nedges;
}
