#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>

// thoughts on the 'relatives' system
// 1. in activation, need to activate SPNs that are *supertypes* of the input preds
// 2. in enumeration, need to align to input preds that are *subtypes* of the entity's preds

#include	"dag.h"
#include	"lexicon.h"
#include	"hash.h"
#include	"mrs.h"
#include	"freeze.h"
#include	"transfer.h"
#include	"bitvec.h"
#include	"conf.h"

#define	VACUOUS	"vacuous"

char	*normalize_predicate(char	*p, char	*q);

struct semindex_pred_node
{
	// structure to keep track of all the info about a particular pred name
	char	*pred;

	// during chart population, keep track of which input EPs are compatible with this pred
	// this has to be a separate "cons" structure from the mrs_ep itself, since
	//   different semindex_pred_node's can have overlapping sets of compatible input EPs
	struct ep_list
	{
		struct mrs_ep	*ep;
		struct ep_list	*next;
	}	*activation;

	// complete list of semindex_pred_node's which are hierarchically related to this one,
	//   i.e. should be activated when this one is
	// sweaglesw 2010-08-29: actually, we should activate supertypes, and enumerate subtypes
	int							nrelatives;
	struct semindex_pred_node	**relatives;

	// list of lexemes' and rules' EPs that provide the predication in question
	// if an entity provides the prediction multiple times then it will show up
	//   in this list multiple times, with different 'pidx' values
	int	nentities, aentities;
	struct grammar_entity
	{
#define	LEXEME	1
#define RULE	2
		char what, nextra_preds, pidx, unused;
		union
		{
			struct lexeme	*lex;
			struct rule		*rule;
		};
		// if this grammar entity has multiple EPs,
		//   keep track of what the extra ones are
		struct semindex_pred_node	**extra_preds;
	}	*entities;
};

struct semindex_pred_node	*lookup_semindex(char *predn, int alloc);
void						add_relative_to_spn(struct semindex_pred_node *rel, struct semindex_pred_node *node);
int	semindex_ignore_quotes = 1;

static struct hash	*sindex;

int							nstrpars;
struct semindex_pred_node	**strpars;

static int predfnum, cargfnum;

void init_index()
{
	int			i, j;

#define	GLB_TYPE(t)	(t->name[0]=='g' && t->name[1]=='(')	/* XXX crude hack to detect GLB types */

	predfnum = lookup_fname("PRED");
	cargfnum = lookup_fname("CARG");
	sindex = hash_new("semantic index");
	struct type_hierarchy	*odth = default_type_hierarchy();
	extern struct type_hierarchy	*semi_th;
	set_default_type_hierarchy(semi_th);
	struct type	*predsort = lookup_type("semi-predicate");
	if(!predsort)predsort = lookup_type("predsort");
	if(!predsort)
	{
		fprintf(stderr, "WARNING: unable to find semi-predicate or predsort; not performing semantic indexing.\n");
		return;
	}
	for(i=0;i<predsort->ndescendents;i++)
	{
		struct type	*t = semi_th->types[predsort->descendents[i]];
		if(GLB_TYPE(t))continue;
		struct semindex_pred_node *node = lookup_semindex(t->name, 1);

		for(j=1;j<t->ndescendents;j++) if(!GLB_TYPE(semi_th->types[t->descendents[j]]))
			add_relative_to_spn(node, lookup_semindex(semi_th->types[t->descendents[j]]->name, 1));

		if(descendent_of(semi_th->strtype->tnum, t))
		{
			nstrpars++;
			strpars = realloc(strpars, sizeof(struct type*) * nstrpars);
			strpars[nstrpars-1] = lookup_semindex(t->name, 1);
		}
	}
	set_default_type_hierarchy(odth);
}

struct semindex_pred_node	*lookup_semindex(char *predn_orig, int alloc)
{
	char	temp[1024];
	char	*predn = normalize_predicate(predn_orig, temp);
	//printf("lookup_semindex: normalized %s to %s\n", predn_orig, predn);
	struct semindex_pred_node	*node = hash_find(sindex, predn);
	if(!node && alloc)
	{
		node = calloc(sizeof(struct semindex_pred_node), 1);
		node->pred = freeze_string(predn);
		if(predn[0]=='"')
		{
			int i;
			// string predication; add it to the relation hierarchy
			for(i=0;i<nstrpars;i++)
				add_relative_to_spn(node, strpars[i]);
		}
		hash_add(sindex, node->pred, node);
	}
	return node;
}

void add_relative_to_spn(struct semindex_pred_node *rel, struct semindex_pred_node *node)
{
	node->relatives = realloc(node->relatives, sizeof(struct semindex_pred_node*)*++node->nrelatives);
	node->relatives[node->nrelatives-1] = rel;
	rel->relatives = realloc(rel->relatives, sizeof(struct semindex_pred_node*)*++rel->nrelatives);
	rel->relatives[rel->nrelatives-1] = node;
}

void	entity_add_semantic_index(short what, struct dg *indpred, char *indkey, void *entity, struct dg *rels, int pidx)
{
	int							nextras = 0, i;
	struct semindex_pred_node	*node, **extras = 0;
	struct grammar_entity		*e;

	for(;rels;rels = dg_hop(rels, 2 /* REST */ ))
	{
		struct dg	*pred, *rel = dg_hop(rels, 1 /* FIRST */);
		if(!rel)break;
		pred = dg_hop(rel, predfnum);
		if(!pred || pred==indpred)continue;
		extras = realloc(extras, sizeof(char*)*(nextras+1));
		extras[nextras++] = lookup_semindex(pred->xtype->name, 1);
	}

	node = lookup_semindex(indkey, 1);
	// 'e' only gets added to 'node', not to 'node's relatives.
	if(node->nentities+1 >= node->aentities)
	{
		if(node->aentities==0)node->aentities = 1;
		else node->aentities *= 2;
		node->entities = realloc(node->entities, sizeof(struct grammar_entity)*node->aentities);
	}
	e = node->entities + node->nentities++;

	e->nextra_preds = nextras;
	e->extra_preds = extras;
	e->what = what;
	e->lex = entity;
	e->pidx = pidx;
}

//static int	savef[10] = {-1,-1,-1,-1,-1,-1,-1,-1};
//static int	rsavef[10] = {-1,-1,-1,-1,-1,-1,-1,-1};

key_for_carg(char	*carg, char	*store)
{
	snprintf(store, 1000, "CARG=%s\n", carg);
}

void	add_semantic_index(struct lexeme *l, struct dg *full, int which)
{
	// walk through the lexeme's full dag's MRS, hash-add this lexeme for each relation name mentioned
	int			pidx = 0;
	struct dg	*rels, *Rels;

//	if(!which)rels = walk_dg(full, savef, "SYNSEM", "LOCAL", "CONT", "RELS", "LIST", NULL);
//	else rels = walk_dg(full, rsavef, "C-CONT", "RELS", "LIST", NULL);

	if(!which)rels = dg_path(full, lex_rels_path);
	else rels = dg_path(full, rule_rels_path);

	static int list_fnum = -1;
	if(list_fnum==-1)
		list_fnum = lookup_fname("LIST");
	if(rels)rels = dg_hop(rels, list_fnum);

	Rels = rels;
	if(!sindex)init_index();

	if(rels && dg_hop(rels, 1))
	{
		for(;rels;rels = dg_hop(rels, 2 /* REST */ ))
		{
			struct dg	*pred, *rel = dg_hop(rels, 1 /* FIRST */), *carg;
			char		*predn, *cargn;
			int			i;
			if(!rel)break;
			carg = dg_hop(rel, cargfnum);
			if(carg)cargn = carg->xtype->name;
			else cargn = 0;
			pred = dg_hop(rel, predfnum);
			if(!pred)continue;
			predn = pred->xtype->name;

			char	*key, ckstore[1024];
			if(cargn)
			{
				key_for_carg(cargn, ckstore);
				key = ckstore;
			}
			else key = pred->xtype->name;
			entity_add_semantic_index(which?RULE:LEXEME, pred, key, l, Rels, pidx++);
			break;
		}
	}
	else entity_add_semantic_index(which?RULE:LEXEME, 0, VACUOUS, l, 0, 0);
}

void	freeze_ge(struct grammar_entity *n, struct grammar_entity	*ge)
{
	int						i;
	*n = *ge;
	n->extra_preds = slab_alloc(sizeof(struct semindex_pred_node*) * n->nextra_preds);
	for(i=0;i<n->nextra_preds;i++)
		n->extra_preds[i] = (struct semindex_pred_node*)ge->extra_preds[i]->activation;
	if(n->what == LEXEME)
		n->lex = (struct lexeme*)ge->lex->dg;	// funny freezer forwarding addresses
	if(n->what == RULE)
		n->rule = (struct rule*)ge->rule->dg;	// funny freezer forwarding addresses
}

struct semindex_pred_node	*freeze_spn(struct semindex_pred_node	*old)
{
	struct semindex_pred_node	*node = (struct semindex_pred_node*)old->activation;
	int							i;

	node->pred = freeze_string(old->pred);
	node->activation = 0;

	node->nrelatives = old->nrelatives;
	node->relatives = slab_alloc(sizeof(struct semindex_pred_node*) * node->nrelatives);
	for(i=0;i<node->nrelatives;i++)
		node->relatives[i] = (struct semindex_pred_node*)old->relatives[i]->activation;

	node->aentities = node->nentities = old->nentities;
	node->entities = slab_alloc(sizeof(struct grammar_entity) * node->aentities);
	for(i=0;i<node->nentities;i++)
		 freeze_ge(node->entities+i, old->entities+i);

	return node;
}

struct semantic_index
{
	struct hash	*sindex;
	int	nexpedients;
	char	**expedients;
};

extern int nexpedients;
extern char	**expedients;

void	*freeze_semantic_index()
{
	int	i;
	struct hash_bucket *walk;
	// NOTE: this gets called shortly after the lexicon is frozen.
	// The old lexicon memory still exists and our hash table points to it.
	// We arranged to leave forwarding addresses in lex->dg slots.

	if(!sindex)return NULL;

	// tricky process.  first make slab copies of all the SPNs, with forwarding addresses in the ->activation slots.
	for(i=0;i<sindex->size;i++)
		for(walk=sindex->buckets[i];walk;walk=walk->next)
		{
			struct semindex_pred_node *n = walk->value;
			n->activation = slab_alloc(sizeof(struct semindex_pred_node));
		}
	// next migrate all the data to the slab copies
	for(i=0;i<sindex->size;i++)
		for(walk=sindex->buckets[i];walk;walk=walk->next)
			walk->value = freeze_spn(walk->value);
	// finally, freeze the hash structure
	struct semantic_index	*freeze = slab_alloc(sizeof(*freeze));
	freeze->sindex = freeze_hash(sindex);
	freeze->nexpedients = nexpedients;
	freeze->expedients = slab_alloc(sizeof(char*) * nexpedients);
	for(i=0;i<nexpedients;i++)
		freeze->expedients[i] = freeze_string(expedients[i]);
	return freeze;
}

void	recover_semantic_index(void *frozen)
{
	extern int debug_level;
	struct semantic_index	*freeze = frozen;
	if(!freeze)return;
	sindex = freeze->sindex;
	nexpedients = freeze->nexpedients;
	expedients = freeze->expedients;
	if(debug_level)
		printf("NOTE: semantic index hash contains %d entries in %d slots\n",
					sindex->entries, sindex->size);
}


/* semantic lookup at generation time: efficient two-phase process
	- activation: for each predication in the input mrs, 'activate' the corresponding index nodes and their supertype relatives
	- enumeration: traverse the activated nodes, filtering those which require inactive preds, and finding all alignments, including against subtype relatives
		- constraints: we call back to generate.c to implement the constraints specified in the alignments

	- as an after-thought we add semantically vacuous rules and those lexemes which are licensed
 */

// activation

struct spn_list
{
	struct semindex_pred_node	*node;
	struct spn_list				*next;
};

void print_spn_activation(struct semindex_pred_node	*node)
{
	struct ep_list *epl;
	printf(" active SPN: `%s' [%d entities]", node->pred, node->nentities);
	for(epl=node->activation;epl;epl=epl->next)
		printf(" /%p %s", epl->ep, epl->ep->pred);
	printf("\n");
}

int	activate_semindex_node(struct semindex_pred_node *node, struct mrs_ep *ep, struct spn_list	**Rest)
{
	struct ep_list				*epl;
	struct spn_list				*spnl;

	// if this node hasn't been activated yet, record it in our list of activated nodes
	if(node->activation)spnl = *Rest;
	else
	{
		spnl = slab_alloc(sizeof(struct spn_list));
		spnl->node = node;
		spnl->next = *Rest;
	}

	// add the relevant ep to the activation record
	for(epl=node->activation;epl;epl=epl->next)
		if(epl->ep == ep)break;
	if(!epl)
	{
		epl = slab_alloc(sizeof(struct ep_list));
		epl->ep = ep;
		epl->next = node->activation;
		node->activation = epl;
	}

	//printf("node '%s' [%d entities]\n", node->pred, node->nentities);

	*Rest = spnl;
	return node->nentities;
}

char *ep_has_carg(struct mrs_ep *ep)
{
	int i;
	for(i=0;i<ep->nargs;i++)
		if(!strcasecmp(ep->args[i].name, "CARG") && ep->args[i].value->is_const)
			return ep->args[i].value->name;
	return 0;
}

int	activate_semindex(struct mrs_ep *ep, struct spn_list	**Rest)
{
	char						*carg = ep_has_carg(ep);
	struct semindex_pred_node	*node = lookup_semindex(ep->pred, 0), *cnode;
	int							i, count = 0, altquoted = 0;
	char	alt_pred[1024];

	//printf("activating '%s' with carg '%s'\n", ep->pred, carg);

	ep->active = 0;
	if(node)
	{
		int local_count = 0;
		revisit:
		for(i=0;i<node->nrelatives;i++)
		{
			// note: generating with GG requires adding signs with *less* specific predicates, which can be constrained by other signs.
			// but generating off the result of JAEN requires adding signs with *more* specific predicates, which are of course subsumed by the input
			// we used to only look at things that are less specific:
			//  if(pred_subsumes(node->relatives[i]->pred, node->pred))
			// now we will look at everything (but don't hit the node itself twice)
			if(strcmp(node->relatives[i]->pred, node->pred))
			{
				//printf("going into %s\n", node->relatives[i]->pred);
				local_count += activate_semindex_node(node->relatives[i], ep, Rest);
			}
			//else printf("not going into %s\n", node->relatives[i]->pred);
		}
		local_count += activate_semindex_node(node, ep, Rest);
		count += local_count;
		//printf("local activated count = %d\n", local_count);
	}
	if(semindex_ignore_quotes && strlen(ep->pred)<1020 && !altquoted)
	{
		if(ep->pred[0]=='"')sprintf(alt_pred, "%.*s", (int)strlen(ep->pred)-2, ep->pred+1);
		else sprintf(alt_pred, "\"%s\"", ep->pred);
		node = lookup_semindex(alt_pred, 0);
		altquoted = 1;
		if(node)goto revisit;
	}
	if(carg)
	{
		// grammar entities with CARG's aren't put into their pred's index slot, but into the carg's index slot.
		// go looking for those.
		char	key[1024];
		key_for_carg(carg, key);
		cnode = lookup_semindex(key, 0);
		if(cnode) count += activate_semindex_node(cnode, ep, Rest);
	}

	return count;
}

// enumeration

struct ep_alignment	*enumerate_eps(struct grammar_entity	*e, struct semindex_pred_node *node, int ai, int ei, struct mrs_ep	*align[], struct ep_alignment	*rest, char	*ep_hit_map);
//int constrain_gen_edge(struct edge *e, struct dg	*cont, int	neps, struct mrs_ep	*eps[]);
struct dg	*dagify_rels_from_eps(int neps, struct mrs_ep	*eps[]);

struct ep_alignment
{
	struct grammar_entity	*e;
	struct mrs_ep			*align[32];
	struct ep_alignment	*next;
};

int	instantiate_alignment(struct ep_alignment	*a)
{
	// we have produced a complete alignment of 'e' against the input semantics.
	struct grammar_entity	*e = a->e;
	struct mrs_ep			**align = a->align;
	struct edge	*edge = NULL;
	struct dg	*rels = dagify_rels_from_eps(1+e->nextra_preds, align);
	int			result, i;
	struct slab_state slab;

	get_slabstate(&slab);
	if(e->what == LEXEME)
	{
		//printf("aligned `%s' to eps ", e->lex->word);
		//for(i=0;i<=e->nextra_preds;i++)printf(" %d", align[i]->epnum); printf("\n");
		edge = lexical_edge(e->lex, 0, 0, rels);
		// the edge has not been restricted yet...
		extern int	dont_unspecialize, inhibit_pack;
		if(edge && !dont_unspecialize && !inhibit_pack)edge->dg = restrict_copy_dg(edge->dg, 1);
		//if(!edge)printf("failed lexical_edge\n");
		//cont = walk_dg(edge->dg, savef, "SYNSEM", "LOCAL", "CONT", NULL);
	}
	if(e->what == RULE)
	{
		//printf("aligned `%s' to eps ", e->rule->name);
		//for(i=0;i<=e->nextra_preds;i++)printf(" %d", align[i]->epnum); printf("\n");
		edge = epsilon_edge(e->rule, 0, e->rule->rtl, rels);
		//cont = walk_dg(edge->dg, rsavef, "C-CONT", NULL);
	}
	if(!edge)set_slabstate(&slab);
	else
	{
		int i;
		for(i=0;i<=e->nextra_preds;i++)
			bitvec_set(edge->ep_span_bv, align[i]->epnum);
			//edge->ep_span |= ((unsigned long long)1)<<align[i]->epnum;
		edge->neps = 1+e->nextra_preds;
		add_agenda(edge);
	}
	return edge?1:0;
}

struct ep_alignment	*record_alignment(struct grammar_entity	*e, struct mrs_ep	*align[], struct ep_alignment	*rest, char	*ep_hit_map)
{
	struct ep_alignment	*a;
	int	i;

	for(a=rest;a;a=a->next)
	{
		if(a->e != e)continue;
		for(i=0;i<=e->nextra_preds;i++)
			if(a->align[i] != align[i])break;
		if(i<=e->nextra_preds)continue;
		// this is identical to alignment 'a' which we already had.
		//printf(" ... rejecting duplicate alignment\n");
		return rest;
	}
	// this alignment is not found in 'rest'.
	a = slab_alloc(sizeof(struct ep_alignment));
	a->e = e;
	memcpy(a->align, align, sizeof(struct mrs_ep*)*(1+e->nextra_preds));
	a->next = rest;
	int	mark = (e->what == LEXEME)?1:2;
	for(i=0;i<=e->nextra_preds;i++)
		ep_hit_map[align[i]->epnum] |= mark;
	/*printf(" ... accepting new alignment of %s: ", (e->what==LEXEME)?e->lex->word:e->rule->name);
	for(i=0;i<=e->nextra_preds;i++)
		printf(" %s/%p", align[i]->pred, align[i]);
	printf("\n");*/
	return a;
}

struct ep_alignment	*enumerate_alignments(struct grammar_entity	*e, int ei, struct mrs_ep	*align[], struct ep_alignment	*rest, char	*ep_hit_map)
{
	if(ei == e->nextra_preds)
	{
		// we have produced a complete alignment of 'e' against the input semantics.
		// record it.
		return record_alignment(e, align, rest, ep_hit_map);
	}
	else
	{
		// we've finished aligning up to but not including extra_preds[ei].
		struct semindex_pred_node	*next = e->extra_preds[ei];
		int	i;
		//printf("enumerating '%s' [%d]\n", next->pred, ei);
		rest = enumerate_eps(e, next, (ei<e->pidx)?(ei):(ei+1), ei+1, align, rest, ep_hit_map);
		//printf(" has %d relatives\n", next->nrelatives);
		for(i=0;i<next->nrelatives;i++)
			if(pred_subsumes(next->pred, next->relatives[i]->pred))
			{
				//printf(" rel = %s\n", next->relatives[i]->pred);
				rest = enumerate_eps(e, next->relatives[i], (ei<e->pidx)?(ei):(ei+1), ei+1, align, rest, ep_hit_map);
			}
		return rest;
	}
}

struct ep_alignment	*enumerate_eps(struct grammar_entity	*e, struct semindex_pred_node *node, int ai, int ei, struct mrs_ep	*align[], struct ep_alignment	*rest, char	*ep_hit_map)
{
	struct ep_list *epl;
	int count = 0;

	for(epl=node->activation;epl;epl=epl->next)
	{
		if(epl->ep->active)continue;
		align[ai] = epl->ep;
		epl->ep->active = 1;
		rest = enumerate_alignments(e, ei, align, rest, ep_hit_map);
		epl->ep->active = 0;
	}
	return rest;
}

struct ep_alignment	*enumerate_semindex(struct semindex_pred_node *node, struct ep_alignment	*rest, char	*ep_hit_map)
{
	int i, j, count = 0;
	struct ep_list	*epl;
	struct mrs_ep	*align[32];

	//printf("active: "); print_spn_activation(node);

	// inspect each grammar entity representing this predication;
	//   for those of which all required predications are activated,
	//   investigate all possible alignments against the input mrs.
	for(i=0;i<node->nentities;i++)
	{
		struct grammar_entity	*e = node->entities+i;
		for(j=0;j<e->nextra_preds;j++)
			if(e->extra_preds[j]->activation == 0)
				break;
		if(j < e->nextra_preds)continue;
		assert(e->nextra_preds+1 <= 32);
		//printf("consider grammar entity `%s'\n", (e->what==RULE)?e->rule->name:e->lex->word);
		//printf(" extra EPs: ");
		//for(j=0;j<e->nextra_preds;j++)
		//	printf(" '%s'", e->extra_preds[j]->pred);
		//printf("\n");
		rest = enumerate_eps(e, node, e->pidx, 0, align, rest, ep_hit_map);
	}
	return rest;
}

struct semindex_pred_node	*invent_semindex_node_for_gle(struct lexeme	*gle, struct mrs_ep	*ep)
{
	struct semindex_pred_node	*node = slab_alloc(sizeof(*node));
	bzero(node, sizeof(*node));
	node->pred = gle->pred->name;
	node->nentities = node->aentities = 1;
	struct grammar_entity	*e = slab_alloc(sizeof(*e));
	bzero(e, sizeof(*e));
	node->entities = e;
	e->what = LEXEME;
	e->lex = gle;
	struct ep_list	*epl = slab_alloc(sizeof(*epl));
	bzero(epl, sizeof(*epl));
	epl->ep = ep;
	epl->next = NULL;
	node->activation = epl;
	return node;
}

int	semindex_try_generics(struct mrs_ep	*ep, struct ep_alignment	**Rest, char	*ep_hit_map)
{
	// if there is a CARG, we get to look at generic LEs
	char	*carg = ep_has_carg(ep);
	int	i, count = 0;
	if(carg)
	{
		// see if any generic LEs provide this relation
		//printf("uncovered EP %s has carg %s\n", ep->pred, carg);
		for(i=0;i<ngeneric_les;i++)
		{
			if(!generic_le_infos[i].for_generation)continue;
			struct type	*p = generic_les[i]->pred;
			char	normal[1024];
			char	*gle_pred = normalize_predicate(p->name, normal);
			if(!strcmp(gle_pred, ep->pred))
			{
				// bingo.
				//printf("NOTE: generic '%s' fires for unknown input EP '%s'\n", generic_les[i]->word, ep->pred);
				// FIXME the first 'carg' argument below possibly should be a 
				// modified copy of the string with spaces changed to underscores
				// (or vice versa?)
				struct lexeme	*igle = instantiate_gle(generic_les[i], carg, carg);
				struct semindex_pred_node	*node = invent_semindex_node_for_gle(igle, ep);
				count++;
				*Rest = enumerate_semindex(node, *Rest, ep_hit_map);
			}
		}
	}
	if(!count)
	{
		// we should look at the other set of generics (activated by the pos tag in the relation name)
		fprintf(stderr, "NOTE: EP '%s' is unknown in the semantic index\n", ep->pred);
		itsdb_error("input EP not in index");
	}
}

int evacuate(int ntriggers, char **triggers, struct dg	**trigcons)
{
	struct semindex_pred_node	*vac = lookup_semindex(VACUOUS, 0);
	struct grammar_entity		*e;
	int							i, count = 0;

	for(i=0;i<vac->nentities;i++)
	{
		e = vac->entities+i;
		if(e->what == RULE)
		{
			add_agenda(epsilon_edge(e->rule, 0, e->rule->rtl, 0));
			count++;
		}
	}
	int j;
	// triggers[] is guaranteed unique already (unless there are multiple trigcons per lexeme)
	for(j=0;j<ntriggers;j++)
	{
		struct lexeme	*lex = get_lex_by_name_hash(triggers[j]);
		if(!lex)
		{
			fprintf(stderr, "ERROR: trigger rules call for non-existant lexeme `%s'\n", triggers[j]);
			continue;
		}
		// we may have to instantiate this vacuous lexeme several times, with different constraints.
		struct edge	*edge = lexical_edge(lex, 0, 0, 0);
		if(trigcons[j])
		{
			//printf("applying trigger constraint to %s\n", lex->word);
			//print_dg(trigcons[j]);printf("\n");
			if(0 != unify_dg_infrom(edge->dg, trigcons[j]))
			{
				extern int trace;
				if(trace)
				{
					fprintf(stderr, "TRIGGER CONSTRAINT on '%s' failed\n", triggers[j]);
					unify_backtrace();
				}
				continue;
			}
		}
		add_agenda(edge);
		count++;
	}

	return count;
}

void	check_triggers(int	nx, char	**x, int	ny, char	**y)
{
	int	i, j;
	char	goty[ny];
	static FILE	*logf = NULL;
	if(!logf)
	{
		logf = fopen("/tmp/triglog.txt", "a");
		if(!logf) { perror("/tmp/triglog.txt"); exit(-1); }
		fprintf(logf, "STARTUP\n");
	}
	extern int tsdb_i_id;
	fprintf(logf, "next item (i_id = %d) ; ACE %d trigs, LKB %d trigs\n", tsdb_i_id, nx, ny);
	bzero(goty, sizeof(goty));
	for(i=0;i<nx;i++)
	{
		for(j=0;j<ny;j++)
		{
			if(goty[j])continue;
			if(!strcmp(x[i], y[j]))
			{
				goty[j] = 1;
				break;
			}
		}
		if(j==ny)
			fprintf(logf, "extra ACE trigger: %s\n", x[i]);
	}
	for(j=0;j<ny;j++)
		if(!goty[j])
			fprintf(logf, "extra LKB trigger: %s\n", y[j]);
	fflush(logf);
}

// driver

void semantic_lookup(struct mrs	*mrs)
{
	extern int debug_level;
	struct spn_list	*active = NULL, *walk;
	int				i, count = 0;

	// activate index nodes
	for(i=0;i<mrs->nrels;i++)
		activate_semindex(mrs->rels+i, &active);

	// enumerate grammar entity alignments
	char	ep_hit_map[mrs->nrels];
	bzero(ep_hit_map, mrs->nrels);
	struct ep_alignment	*alignments = NULL, *awalk;
	for(walk=active;walk;walk=walk->next)
		alignments = enumerate_semindex(walk->node, alignments, ep_hit_map);

	// see if we need to enumerate any generic lexemes
	for(i=0;i<mrs->nrels;i++)
		if(!ep_hit_map[i])
			semindex_try_generics(mrs->rels+i, &alignments, ep_hit_map);
	for(i=0;i<mrs->nrels;i++)
	{
		if(!ep_hit_map[i])
		{
			fprintf(stderr, "WARNING: EP '%s' is not covered\n", mrs->rels[i].pred);
		}
		if(ep_hit_map[i] & 2)
		{
			//printf("ep `%s' can be ccont\n", mrs->rels[i].pred);
			bitvec_set(can_be_ccont_ep_bv, i);
		}
	}

	// clear activation records
	while(active) { active->node->activation = 0; active = active->next; }

	// add entities according to the unique alignments we found
	for(awalk=alignments;awalk;awalk=awalk->next)
		count += instantiate_alignment(awalk);

	// finally, add vacuous entities
	int	ntriggers = 0;
	char	**triggers = NULL;
	struct dg	**trigcons = NULL;
	void	add_vac(char	*lexid, struct dg	*cons)
	{
		//printf("trigger %s %p\n", lexid, cons);
		int	i, packed = 0;
		for(i=0;i<ntriggers;i++)
			if(!strcmp(lexid, triggers[i]))
			{
				if(!cons)
				{
					// specificied with no constraint
					// automatically subsumes all other triggerings of this lexid
					trigcons[i] = NULL;
					packed = 1;
					continue;
				}
				if(!trigcons[i])
				{
					// a previous rule triggered this same lexid with no constraint;
					// we don't need a constrained version.
					return;
				}
				int res = equivalent_dg(trigcons[i], cons,1,1,0);
				if(res == 2 || res == 1)
				{
					// a previous rule triggered a more general constraint.
					return;
				}
				if(res == -1)
				{
					// a previous rule triggered a less general constraint
					if(!packed)
						trigcons[i] = cons;
					else trigcons[i] = NULL;
					packed = 1;
					continue;
				}
			}
		if(packed)return;
		ntriggers++;
		triggers = realloc(triggers, sizeof(char*)*ntriggers);
		triggers[ntriggers-1] = strdup(lexid);
		trigcons = realloc(trigcons, sizeof(struct dg*)*ntriggers);
		trigcons[ntriggers-1] = cons;
		//printf("trigger %s with constraint %p\n", lexid, cons);
	}
	activate_trigger_rules(mrs, add_vac);
	//printf("triggered %d vacuous lexemes\n", ntriggers);
	//check_triggers(ntriggers, triggers, mrs->ntriggers, mrs->triggers);
	count += evacuate(ntriggers, triggers, trigcons);
	//count += evacuate(mrs->ntriggers, mrs->triggers);
	if(0)
	{
		int	j;
		for(i=0;i<mrs->ntriggers;i++)
		{
			for(j=0;j<ntriggers;j++)
				if(!strcmp(triggers[j], mrs->triggers[i]))break;
			if(j==ntriggers)
			{
				//fprintf(stderr, "TRIGGER_DEBUG: '%s' missing\n", mrs->triggers[i]);
			}
		}
		for(i=0;i<ntriggers;i++)
		{
			for(j=0;j<mrs->ntriggers;j++)
				if(!strcmp(triggers[i], mrs->triggers[j]))break;
			if(j==mrs->ntriggers)
			{
				//fprintf(stderr, "TRIGGER_DEBUG: '%s' extra\n", triggers[i]);
			}
		}
	}
	for(i=0;i<ntriggers;i++)free(triggers[i]);
	if(triggers)free(triggers);

	if(debug_level)printf("added %d grammar entities\n", count);
}

debug_trigger_rules(char	*args)
{
	if(g_mode != GENERATING)
	{
		fprintf(stderr, "trigger debugger: not in generation mode!\n");
		return -1;
	}
	extern struct mrs	*current_internal_input_mrs;
	struct mrs	*m = current_internal_input_mrs;
	if(!m) { fprintf(stderr, "give me an MRS first.\n"); return -1; }

	if(*args==' ')
	{
		char	*name = args+1;
		printf("trying to apply trigger rule '%s' to last input\n", name);
		debug_run_one_trigger_rule(m, name, 1);
	}
	else debug_run_trigger_rules(m);
}
