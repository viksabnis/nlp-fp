#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>

#include	"dag.h"
#include	"chart.h"
#include	"hash.h"
#include	"freeze.h"
#include	"maxent.h"

struct maxent_feature
{
	float	score;
	// XXX features below this comment are not accessible at parse time -- only at grammar load time
	char	*head;
	char	*rhs[2];

	int		ngp;
	char	**gp;
};

void print_mef(struct maxent_feature *f);

static struct hash	*mem;
static struct hash	*mem_ro;	// table for subset that only uses rule names; fixed-length keys

// values: ruleid
// -1 as rhs means no such daughter
// -1 as gp means no such grandparent
// -2 as gp means root
struct __attribute__((packed)) maxent_rule_key
{
	signed short lhs, rhs1, rhs2;
	signed short	gp[MAX_GRANDPARENTING];
};

#define MAXENT_NOISE(fmt, ...)
//#define MAXENT_NOISE printf

//int	nmaxent_requests = 0, nmaxent_lookups = 0, nmaxent_visits = 0;

/*show_me()
{
	fprintf(stderr, "MAXENT: %d visits / %d lookups / %d requests = %.1f per request ; %.1f%% hit rate\n", nmaxent_visits, nmaxent_lookups, nmaxent_requests, (float)nmaxent_visits / nmaxent_requests, 100*(float)nmaxent_visits / nmaxent_lookups);
}*/

float	maxent_score_ro(int lhs, int rhs1, int rhs2, struct scoring_ancestry	*anc)
{
	struct maxent_rule_key key;
	int i;
	float	score = 0;
	if(!mem_ro)return 0;
	//printf("score_ro: mem_ro entries = %d\n", mem_ro->entries);
	//printf(" lhs %d = %s, rhs1 %d = %s, rhs2 %d, anc.rooted %d, anc.nparent_types %d [%s = %d]\n",
		//lhs, rules[lhs]->name, rhs1, rules[rhs1]->name, rhs2, anc->rooted, anc->nparent_types, anc->parent_types[0], lookup_rule(anc->parent_types[0])->rnum);
	key.lhs = lhs;
	key.rhs1 = rhs1;
	key.rhs2 = rhs2;
	for(i=0;i<MAX_GRANDPARENTING;i++)key.gp[i] = -1;
	for(i=0;i<=anc->nparent_types;i++)
	{
		if(i)
		{
			//struct rule	*r = lookup_rule(anc->parent_types[i-1]);
			//assert(r != NULL);
			//key.gp[i-1] = r->rnum;
			key.gp[i-1] = anc->gprnum[i-1];
		}
		float *v = hash_find(mem_ro, (void*)&key);
		if(v)score += *v;
	}
	if(anc->rooted && anc->nparent_types < MAX_GRANDPARENTING)
	{
		key.gp[anc->nparent_types] = -2;
		float *v = hash_find(mem_ro, (void*)&key);
		if(v)score += *v;
	}
	return score;
}

// visit all maxent features containing this local subtree and compatible with the ancestry
// add up their scores
float	maxent_score(char *lhs, char *rhs1, char *rhs2, int rtl_unused, struct scoring_ancestry	*anc)
{
	float ret = 0;
	//char	*key = rtl?rhs2:rhs1;
	char	hkey[512];
	int	space = 511;

	void visitor(struct maxent_feature *feat)
	{
		int	i;
		//nmaxent_visits++;
		ret += feat->score;
	}

	//nmaxent_requests++;

	//return (double)rand()/RAND_MAX - 0.5;
	if(!mem)return 0;

	int	ngp;
	char	*hkp = hkey;
	hkp += safe_snprintf(hkey, 511 - (hkp-hkey), "%s:%s:%s", lhs, rhs1?:"", rhs2?:"");//key?:"");
	for(ngp=0;ngp<=anc->nparent_types;ngp++)
	{
		//if(ngp) hkp += safe_snprintf(hkp, 511 - (hkp-hkey), ":%s", anc->parent_types[ngp-1]);
		if(ngp) hkp += safe_snprintf(hkp, 511 - (hkp-hkey), ":%s", rules[anc->gprnum[ngp-1]]->name);
		MAXENT_NOISE("scoring key = %s\n", hkey);
		//hash_visit_key(mem, hkey, (void(*)(void*))visitor);
		struct maxent_feature	*feat = hash_find(mem, hkey);
		if(feat)ret += feat->score;
		//nmaxent_lookups++;
	}
	if(anc->rooted)
	{
		hkp += safe_snprintf(hkp, 511 - (hkp-hkey), ":^");
		MAXENT_NOISE("scoring key = %s\n", hkey);
		//hash_visit_key(mem, hkey, (void(*)(void*))visitor);
		struct maxent_feature	*feat = hash_find(mem, hkey);
		if(feat)ret += feat->score;
		//nmaxent_lookups++;
	}
	MAXENT_NOISE(" ... %f\n", ret);
	return ret;
}

// loading

void print_mef(struct maxent_feature *f)
{
	printf("maxent head `%s' rhs [%s %s] score %f\n",
		f->head, f->rhs[0]?:"NO-RHS[0]", f->rhs[1]?:"", f->score);
}

void record_maxent_feature(char *lhs, char *rhs[2], float score, int	ngp, char	**gp)
{
	struct maxent_feature *feat = malloc(sizeof(struct maxent_feature));
	char	key[512], *kp = key;
	int	i;

	struct rule	*rhsrule[2];
	rhsrule[0] = lookup_rule(rhs[0]);
	rhsrule[1] = (*rhs[1])?lookup_rule(rhs[1]):NULL;
	if(rhsrule[0] && (rhsrule[1] || !*rhs[1]))
	{
		float	*v = malloc(sizeof(float));
		*v = score;
		struct maxent_rule_key	*bkey = malloc(sizeof(*bkey));
		struct rule	*lhsrule = lookup_rule(lhs);
		if(!lhsrule)
		{
			fprintf(stderr, "WARNING: no such rule as %s in maxent model\n", lhs);
			return;
		}
		assert(lhsrule != NULL);
		bkey->lhs = lhsrule->rnum;
		bkey->rhs1 = rhsrule[0]->rnum;
		if(*rhs[1])bkey->rhs2 = rhsrule[1]->rnum;
		else bkey->rhs2 = -1;
		for(i=0;i<ngp;i++)
		{
			if(!strcmp(gp[i],"^"))bkey->gp[i] = -2;
			else
			{
				struct rule	*rgp = lookup_rule(gp[i]);
				if(!rgp)
				{
					fprintf(stderr, "WARNING: no such rule %s in maxent model\n", gp[i]);
					return;
				}
				assert(rgp != NULL);
				bkey->gp[i] = rgp->rnum;
			}
		}
		for(;i<MAX_GRANDPARENTING;i++)bkey->gp[i] = -1;
		hash_add(mem_ro, (void*)bkey, v);
		//printf("mem_ro adding %d %d %d\n", bkey->lhs, bkey->rhs1, bkey->rhs2);
		//if(bkey->lhs == 333 && bkey->rhs1 == 255 && bkey->rhs2 == -1)printf("added 333,255,-1 to mem_ro\n");
		return;	// don't need it in ordinary 'mem' hash
	}

	kp += sprintf(key, "%s:%s:%s", lhs, rhs[0]?:"", rhs[1]?:"");
	for(i=0;i<ngp;i++)kp += sprintf(kp, ":%s", gp[i]);
	feat->score = score;

	feat->head = strdup(lhs);
	feat->rhs[0] = (rhs[0] && *rhs[0])?strdup(rhs[0]):NULL;
	feat->rhs[1] = (rhs[1] && *rhs[1])?strdup(rhs[1]):NULL;
	feat->ngp = ngp;
	feat->gp = malloc(sizeof(char*)*ngp);
	for(i=0;i<ngp;i++)feat->gp[i] = strdup(gp[i]);
	//print_mef(feat);
	//printf("recording feature at key '%s'\n", key);
	hash_add(mem, strdup(key), feat);
}

static int	maxent_lnum = 0;

static char	*parse_word(char	**P)
{
	char	*p = *P, *ret;

	if(*p==' ')p++;
	ret = p;
	int	quoted = 0;
	while(*p && (*p!=' ' || quoted))
	{
		if(*p=='\\' && p[1])p++;
		else if(*p=='"')quoted=!quoted;
		p++;
	}
	if(*p==' '){*p=0;p++;}
	else
	{
		if(quoted)
		{
			fprintf(stderr, "maxent: problem reading line %d of .mem file; quoted value not terminated properly?\n", maxent_lnum);
			exit(-1);
		}
		assert(!quoted);
	}
	*P = p;
	return *ret?ret:0;
}

int load_mem(char *fname)
{
	FILE	*f;
	char	line[1024];

#define DEBUG(fmt, ...)
//#define DEBUG	printf

	if(!fname)return 0;
	f = fopen(fname, "r");
	if(!f) { perror(fname); return -1; }

	/*if(mem)
		fprintf(stderr, "NOTE: overwriting pre-existing max-ent model with `%s'\n", fname);*/
	mem = hash_new("maxent model");
	mem_ro = hash_new("maxent model (rule-only)");
	mem_ro->has_flk = sizeof(struct maxent_rule_key);

	DEBUG("loading maxent file from '%s'\n", fname);
	maxent_lnum = 0;

//struct timeval tv, tv2;
//gettimeofday(&tv, NULL);
//double tfgets = 0;
	while(fgets(line, 1024, f))
	{
		maxent_lnum++;
		// XXX this measurement was wrong...
		// need to reset `tv' before each fgets()
		//gettimeofday(&tv2, NULL);
		//tfgets += (double)(tv2.tv_sec - tv.tv_sec + 0.000001 * (tv2.tv_usec - tv.tv_usec));
		int llen = strlen(line), tint, i = 0;
		float sfloat;
		char *p, *type, *grandparents_count, *head, *rhs[2], *score;

		if(line[0]!='('){DEBUG("IGNORE maxent line `%s'\n", line);continue;}
		if(line[llen-1]=='\n')line[--llen] = 0;
		DEBUG("process maxent line '%s'\n", line);
		p = strrchr(line, ']');
		if(p>line+1)
		{
			// find *second* to last ']'
			p--;
			while(p>line && *p!=']')p--;
			if(p==line)p=NULL;
		}
		if(!p){DEBUG("IGNORE maxent line `%s' (no closing ])\n", line);continue;}
		*p = 0; score = p+1; p = strchr(line, '[');
		if(!p){DEBUG("IGNORE maxent line `%s' (no opening [)\n", line);continue;}
		p = p+1;
		while(*score==' ' || *score=='\t')score++;
		if((*score<'0' || *score>'9') && *score!='.' && *score!='+' && *score!='-'){DEBUG("IGNORE maxent score `%s'\n", score);continue;}
		sfloat = atof(score);

		type = parse_word(&p);
		grandparents_count = parse_word(&p);
		if(*grandparents_count != '('){DEBUG("IGNORE maxent line with bad grandparent count\n");continue;}
		int	ngrandparents = atoi(grandparents_count+1), j;
		char	*grandparents[ngrandparents];
		for(j=ngrandparents-1;j>=0;j--)grandparents[j] = parse_word(&p);
		head = parse_word(&p);
		if(!type || !head){DEBUG("IGNORE maxent line with type %s head %s\n", type?:"(null)", head?:"(null)");continue;}
		tint = atoi(type);
		if(tint <1 || tint >2){DEBUG("IGNORE maxentline with type %s\n", type);continue;}
		rhs[0] = parse_word(&p);
		while(*p==' ')p++;
		rhs[1] = p;
		record_maxent_feature(head, rhs, sfloat, ngrandparents, grandparents);
	}
	//printf("maxent loading fgets took %.2fs\n", tfgets);

	fclose(f);
	return 0;
}

struct stochastic_model
{
	struct hash	*mem, *mem_ro;
};

void	*freeze_stochastic_model()
{
	int	i, j;
	struct hash_bucket *walk;
	if(!mem)
	{
		struct stochastic_model *mod = slab_alloc(sizeof(*mod));
		mod->mem = NULL;
		mod->mem_ro = NULL;
		return mod;
	}
	for(i=0;i<mem->size;i++)
		for(walk=mem->buckets[i];walk;walk=walk->next)
		{
			struct maxent_feature *fi = walk->value;
			struct maxent_feature *fo = slab_alloc(sizeof(float));//slab_alloc(sizeof(struct maxent_feature));
			fo->score = fi->score;
			walk->value = fo;
		}
	for(i=0;i<mem_ro->size;i++)
		for(walk=mem_ro->buckets[i];walk;walk=walk->next)
		{
			float *v = walk->value;
			float *vo = slab_alloc(sizeof(float));//slab_alloc(sizeof(struct maxent_feature));
			*vo = *v;
			walk->value = vo;
		}
	struct stochastic_model *mod = slab_alloc(sizeof(*mod));
	mod->mem = freeze_hash(mem);
	mod->mem_ro = freeze_hash(mem_ro);
	return mod;
}

void	recover_stochastic_model(void *_frozen)
{
	extern int debug_level;
	struct stochastic_model *mod = _frozen;
	if(!mod) { mem = NULL; mem_ro = NULL; }
	else
	{
		mem = mod->mem;
		mem_ro = mod->mem_ro;
	}
	if(mem && debug_level)printf("NOTE: max-ent model hash contains %d entries in %d slots\n", mem->entries, mem->size);
}
