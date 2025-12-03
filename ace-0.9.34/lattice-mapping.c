#define	DEBUG(x, ...)	do {} while(0)
#define	DEBUG_VERBOSE(x, ...)	do {} while(0)
//#define	DEBUG	printf
//#define	DEBUG_VERBOSE	printf
//#define	SHOW_OUTPUT_TOKENS

#include	<wctype.h>
#include	<stdio.h>
#include	<string.h>
#include	<stdlib.h>
#include	<sys/time.h>
#include	<assert.h>

#include	"tdl.h"
#include	"dag.h"
#include	"type.h"
#include	"conf.h"
#include	"freeze.h"
#include	"chart.h"
#include	"type.h"
#include	"lexicon.h"

#include	"lattice-mapping.h"
#include	"token.h"
#include	"profiler.h"

#include	"unicode.h"

struct re_match_set;

void	update_possible_map_add(struct lattice	*lat, int	id, struct lattice_edge	*e, struct lattice_rule	*r, struct re_match_set	*mats);
void	update_possible_map_remove(struct lattice	*lat, int	id, struct lattice_rule	*r);
int	initialize_possible_map(struct lattice	*lat, struct lattice_rule	*r);

struct lattice_rule_set	*token_mapping_rules = NULL;
struct lattice_rule_set	*lexical_filtering_rules = NULL;
struct lattice_rule_set	*post_generation_mapping_rules = NULL;

int	mapping_tokens = 0;
int	noriginaltokens, nmappingtokens;

char	*lm_breakpoint = NULL;
int		lm_break_before = 0, lm_break_after = 0, lm_just_list = 0;
int		lm_break_after_finish = 0, lm_break_before_start = 0;

struct edge	*new_edge(struct dg	*d)
{
	struct edge	*E = slab_alloc(sizeof(*E));
	bzero(E, sizeof(*E));
	E->id = next_eid();
	E->dg = d;
	return E;
}

struct lattice_rule	*freeze_lattice_rule(struct lattice_rule	*r)
{
	struct lattice_rule	*fr = slab_alloc(sizeof(*fr));
	fr->name = freeze_string(r->name);
	fr->dg = freeze_dg(r->dg);
	fr->ninput = r->ninput;
	fr->noutput = r->noutput;
	fr->ncontext = r->ncontext;
	fr->nposition_constraints = r->nposition_constraints;
	fr->position_constraints = freeze_block(r->position_constraints,
		sizeof(struct lattice_position_constraint)*(r->nposition_constraints));
	fr->regex_constraints = slab_alloc(sizeof(struct lattice_regex_constraints)*(fr->ninput+fr->ncontext));
	fr->jump_on_match = r->jump_on_match;
	int i, j;
	for(i=0;i<fr->ninput+fr->ncontext;i++)
	{
		struct lattice_regex_constraints	*frec = fr->regex_constraints+i;
		struct lattice_regex_constraints	*rec = r->regex_constraints+i;
		bzero(frec, sizeof(*frec));
		frec->count = rec->count;
		frec->paths = slab_alloc(sizeof(struct path)*frec->count);
		frec->regexs = slab_alloc(sizeof(wchar_t*)*frec->count);
		for(j=0;j<frec->count;j++)
		{
			frec->paths[j] = freeze_path(rec->paths[j]);
			frec->regexs[j] = freeze_wcs(rec->regexs[j]);
		}
	}
	return fr;
}

struct lattice_rule_set	*freeze_lattice_rule_set(struct lattice_rule_set	*rs)
{
	if(!rs)return NULL;
	struct lattice_rule_set	*frs = slab_alloc(sizeof(*frs));
	int	i;
	frs->nrules = rs->nrules;
	frs->rules = slab_alloc(sizeof(struct lattice_rule*)*frs->nrules);
	for(i=0;i<frs->nrules;i++)
		frs->rules[i] = freeze_lattice_rule(rs->rules[i]);
	return frs;
}

void	compile_lattice_rule_set(struct lattice_rule_set	*rs)
{
	int	i, j, k;
	if(!rs)return;
	for(i=0;i<rs->nrules;i++)
		for(j=0;j<rs->rules[i]->ninput+rs->rules[i]->ncontext;j++)
		{
			struct lattice_regex_constraints	*rec = rs->rules[i]->regex_constraints+j;
			rec->re = calloc(sizeof(regex_t),rec->count);
			for(k=0;k<rec->count;k++)
			{
				//printf("... compiling `%S'\n", rec->regexs[k]);
				int	err = regcomp(&rec->re[k], rec->regexs[k], REGEX_FLAGS);
				if(err)
				{
					wchar_t	buf[1024];
					regerror(err, &rec->re[k], buf, 1023);
					fprintf(stderr, "lattice-mapping-rule: while compiling `%S' for rule '%s': %S\n", rec->regexs[k], rs->rules[i]->name, buf);
					exit(-1);
				}
			}
		}
}

struct dg	*lattice_rule_spot(struct lattice_rule	*r, int	k)
{
	if(k<r->ninput)
	{
		struct dg	*d = dg_path(r->dg, lattice_mapping_input_path);
		while(k-->0)d = dg_hop(d, 2);	// REST
		return dg_hop(d, 1);	// FIRST
	}
	k -= r->ninput;
	if(k<r->ncontext)
	{
		struct dg	*d = dg_path(r->dg, lattice_mapping_context_path);
		while(k-->0)d = dg_hop(d, 2);	// REST
		return dg_hop(d, 1);	// FIRST
	}
	k -= r->ncontext;
	if(k<r->noutput)
	{
		struct dg	*d = dg_path(r->dg, lattice_mapping_output_path);
		while(k-->0)d = dg_hop(d, 2);	// REST
		return dg_hop(d, 1);	// FIRST
	}
	assert(!"Not reached");
}

static int	count_list(struct dg	*list, char	*rname, char	*fname)
{
	int	N = 0;
	while(list)
	{
		if(!strcmp(list->xtype->name, g_null_type))break;
		if(!strcmp(list->xtype->name, g_list_type))
		{
			static int did_warn = 0;
			if(!did_warn)
				fprintf(stderr, "WARNING: lattice mapping rule '%s' had %s *list* (not *null* or *cons*)\n", rname, fname);
			else if(did_warn==1)
				fprintf(stderr, "WARNING: suppressing more lattice mapping warnings\n");
			did_warn++;
			break;
		}
		struct dg	*item = dg_hop(list, 1);	// FIRST
		if(!item)
		{
			fprintf(stderr, "missing FIRST attribute in lattice mapping rule '%s' %s list [%d]\n", rname, fname, N);
			print_dg(list);
			printf("\n");
			return -1;
		}
		N++;
		list = dg_hop(list, 2);	// REST
	}
	return N;
}

void	extract_regex_constraints(struct dg	*d, struct lattice_regex_constraints	*rec, struct path	path)
{
	d = dereference_dg(d);
	if(d->xtype->name[0]=='"')
	{
		int	l = strlen(d->xtype->name);
		if(d->xtype->name[l-1]=='$')
		{
			// d->xtype->name looks like: "myregex$
			char	*re = malloc(l + 7);
			sprintf(re, "^(?:%.*s)$", l-2, d->xtype->name+1);
			//printf("extracted RE: %s\nat path: ", re); print_path(path);printf("\n");
			rec->count++;
			rec->paths = realloc(rec->paths, sizeof(struct path)*rec->count);
			rec->regexs = realloc(rec->regexs, sizeof(wchar_t*)*rec->count);
			rec->paths[rec->count-1].count = path.count;
			rec->paths[rec->count-1].fnums = malloc(sizeof(int)*path.count);
			memcpy(rec->paths[rec->count-1].fnums, path.fnums, sizeof(int)*path.count);
			rec->regexs[rec->count-1] = towide(re);
		}
	}

	int	i;
	struct dg	**da = DARCS(d);
	for(i=0;i<d->narcs;i++)
	{
		path.fnums[path.count++] = d->label[i];
		extract_regex_constraints(da[i], rec, path);
		path.count--;
	}
}

void	remove_regex_constraints(struct dg	*d)
{
	d = dereference_dg(d);
	if(d->xtype->name[0]=='"')
	{
		int	l = strlen(d->xtype->name);
		if(d->xtype->name[l-1]=='$')
			d->xtype = d->type = default_type_hierarchy()->strtype;
	}

	int	i;
	struct dg	**da = DARCS(d);
	for(i=0;i<d->narcs;i++)
		remove_regex_constraints(da[i]);
}

struct lattice_rule	*study_lattice_rule(char	*name, struct dg	*dg)
{
	struct lattice_rule	*r = calloc(sizeof(*r), 1);
	r->name = strdup(name);
	r->dg = dg;
	struct dg	*input_list = dg_path(dg, lattice_mapping_input_path);
	struct dg	*output_list = dg_path(dg, lattice_mapping_output_path);
	struct dg	*context_list = dg_path(dg, lattice_mapping_context_path);
	struct dg	*position_constraint_list = dg_path(dg, lattice_mapping_position_path);
	if( (r->ninput = count_list(input_list, name, "+INPUT")) < 0)return NULL;
	if( (r->noutput = count_list(output_list, name, "+OUTPUT")) < 0)return NULL;
	if( (r->ncontext = count_list(context_list, name, "+CONTEXT")) < 0)return NULL;

	r->regex_constraints = malloc(sizeof(struct lattice_regex_constraints)*(r->ninput+r->ncontext));
	int	i;
	for(i=0;i<r->ninput+r->ncontext;i++)
	{
		struct lattice_regex_constraints	*rec = r->regex_constraints+i;
		struct dg	*d = lattice_rule_spot(r, i);
		int	fnum_buffer[128];
		struct path	path = {0,fnum_buffer};
		bzero(rec, sizeof(*rec));
		extract_regex_constraints(d, rec, path);
		remove_regex_constraints(d);
	}

	DEBUG_VERBOSE("lattice rule '%s': ", r->name);
	DEBUG_VERBOSE("%d inputs, %d outputs, %d contexts\n", r->ninput, r->noutput, r->ncontext);
	char	*constraint = position_constraint_list->type->name;
	if(constraint[0]=='"')
	{
		constraint = strdup(constraint);
		char	*cp = constraint+1;
		while(cp && *cp != '"' && *cp != 0)
		{
			char	*comma = strchr(cp, ',');
			if(!comma)comma = strchr(cp, '"');
			if(comma)*comma = 0;
			again:;
			cp = trim_string(cp);
			char	lhs_what, rhs_what, type[3] = {0,0,0};
			int	lhs_which, rhs_which;
			if(cp[0]=='^' || cp[0]=='$')
			{
				if(strlen(cp) < 4)goto badconstraint;
				lhs_what = cp[0];
				lhs_which = 0;
				cp = trim_string(cp+1);
			}
			else
			{
				if(4 > strlen(cp) || !isdigit(cp[1]))
				{
					badconstraint:
					fprintf(stderr, "lattice mapping rule: bad positional constraint '%s'\n", cp);
					return NULL;
				}
				lhs_what = cp[0];
				lhs_which = cp[1] - '1';
				cp = trim_string(cp+2);
			}
			type[0] = cp[0];
			if(!isalpha(cp[1]) && cp[1]!=' ' && cp[1]!='$' && cp[1]!='^') { type[1] = cp[1]; cp++; }
			cp = trim_string(cp+1);

			char *again_rhs = cp;
			rhs_what = cp[0];
			if(rhs_what == '^' || rhs_what == '$')
			{
				cp = trim_string(cp+1);
				rhs_which = 0;
			}
			else
			{
				if(!isdigit(cp[1]))goto badconstraint;
				rhs_which = cp[1] - '1';
				cp = trim_string(cp+2);
			}
			assert(!((lhs_what == '^' || lhs_what == '$') && (rhs_what == '^' || rhs_what == '$')));
			//printf("... position constraint: lhs %c # %d,  rhs %c # %d,  type %s\n", lhs_what, lhs_which, rhs_what, rhs_which, type);
			r->nposition_constraints++;
			r->position_constraints = realloc(r->position_constraints, sizeof(struct lattice_position_constraint)*r->nposition_constraints);
			struct lattice_position_constraint	*pc = r->position_constraints+r->nposition_constraints-1;
			pc->lhs_what = lhs_what;
			pc->rhs_what = rhs_what;
			pc->lhs_which = lhs_which;
			pc->rhs_which = rhs_which;
			     if(!strcmp(type, "<"))pc->type = lpcImmediatelyPreceeds;
			else if(!strcmp(type, ">"))
			{
				pc->lhs_what = rhs_what;
				pc->lhs_which = rhs_which;
				pc->rhs_what = lhs_what;
				pc->rhs_which = lhs_which;
				pc->type = lpcImmediatelyPreceeds;
			}
			else if(!strcmp(type, "<<"))pc->type = lpcPreceeds;
			else if(!strcmp(type, ">>"))
			{
				pc->lhs_what = rhs_what;
				pc->lhs_which = rhs_which;
				pc->rhs_what = lhs_what;
				pc->rhs_which = lhs_which;
				pc->type = lpcPreceeds;
			}
			else if(!strcmp(type, "@"))
			{
				pc->lhs_what = lhs_what;
				pc->lhs_which = lhs_which;
				pc->rhs_what = rhs_what;
				pc->rhs_which = rhs_which;
				pc->type = lpcCovers;
			}
			else goto badconstraint;
			if(*cp) { cp = again_rhs; goto again; }
			else if(comma)cp = comma+1;
			else break;
		}
	}
	return r;
}

void	process_lattice_rule_set_flow_control(struct lattice_rule_set	*rs)
{
	int	i, k;
	for(i=0;i<rs->nrules;i++)
	{
		struct lattice_rule	*r = rs->rules[i];
		struct dg	*jump = dg_hop(r->dg, lookup_fname("+JUMP"));
		if(!jump || jump->xtype->name[0]!='"')
		{
			r->jump_on_match = i;	// default action is to repeat a rule when we find a match
			continue;
		}
		char	*jumpto = jump->xtype->name+1;
		int	tlen = strlen(jumpto)-1;
		assert(tlen > 0);
		for(k=0;k<rs->nrules;k++)
		{
			if(strncasecmp(rs->rules[k]->name, jumpto, tlen))continue;
			if(strlen(rs->rules[k]->name) != tlen)continue;
			r->jump_on_match = k;
			break;
		}
		if(k==rs->nrules)
		{
			fprintf(stderr, "lattice-mapping rule '%s': +JUMP to undefined rule '%.*s'\n", r->name, tlen, jumpto);
			exit(-1);
		}
	}
}

struct lattice_rule_set	*load_lattice_rules(char	*tdl_status)
{
	struct lattice_rule_set	*rs = calloc(sizeof(*rs),1);
	int	callback(char	*name, struct dg	*dg, struct tdl_line	*tdl)
	{
		assert( (dg = wellform_dg(dg)) != NULL );
		struct lattice_rule	*r = study_lattice_rule(name, dg);
		if(!r)return -1;
		rs->nrules++;
		rs->rules = realloc(rs->rules, sizeof(struct lattice_rule*)*rs->nrules);
		rs->rules[rs->nrules-1] = r;
		return 0;
	}
	if(process_tdl_dgs_status(tdl_status, callback))
	{
		fprintf(stderr, "token-mapping-rules: unable to load rules, bailing out.\n");
		exit(-1);
	}
	process_lattice_rule_set_flow_control(rs);
	return rs;
}

struct lattice_vertex	*new_lattice_vertex(struct lattice	*tc)
{
	struct lattice_vertex	*lv = slab_alloc(sizeof(*lv));
	lv->id = tc->lattice_vertex_id_gen++;
	lv->nfollowers = 0;
	lv->followers = NULL;

	tc->nvertices++;
	tc->vertices = slab_realloc(tc->vertices, sizeof(struct lattice_vertex*)*(tc->nvertices-1), sizeof(struct lattice_vertex*)*(tc->nvertices));
	tc->vertices[tc->nvertices-1] = lv;

	return lv;
}

void	add_lattice_vertex_follower(struct lattice_vertex	*v, struct lattice_edge	*e)
{
	v->nfollowers++;
	v->followers = slab_realloc(v->followers, sizeof(struct lattice_edge*)*(v->nfollowers-1), sizeof(struct lattice_edge*)*(v->nfollowers));
	v->followers[v->nfollowers-1] = e;
}

void	remove_lattice_vertex_follower(struct lattice_vertex	*v, struct lattice_edge	*e)
{
	int	i;
	for(i=0;i<v->nfollowers;i++)
		if(v->followers[i] == e)break;
	assert(i<v->nfollowers);
	v->nfollowers--;
	memmove(v->followers+i, v->followers+i+1, sizeof(struct lattice_edge*)*(v->nfollowers-i));
}

void	add_lattice_edge(struct lattice	*lat, struct lattice_edge	*e)
{
	assert(lat->start != e->to);
	assert(lat->end != e->from);
	lat->nedges++;
	lat->edges = slab_realloc(lat->edges, sizeof(struct lattice_edge*)*(lat->nedges-1), sizeof(struct lattice_edge*)*(lat->nedges));
	// code calling update_possible_map_add relies on the new edge going in slot lat->nedges-1
	lat->edges[lat->nedges-1] = e;
	add_lattice_vertex_follower(e->from, e);
}

void	maybe_dead_lattice_vertex(struct lattice	*lat, struct lattice_vertex	*v)
{
	int i;
	for(i=0;i<lat->nedges;i++)
	{
		if(lat->edges[i]->to == v)return;
		if(lat->edges[i]->from == v)return;
	}
	if(lat->start == v)return;
	if(lat->end == v)return;
	assert(v->nfollowers == 0);
	// v is dead, remove it
	for(i=0;i<lat->nvertices;i++)
		if(lat->vertices[i]==v)break;
	if(i==lat->nvertices)
	{
		fprintf(stderr, "tried to remove dead vertex from lattice, but it wasn't in\n");
		exit(-1);
	}
	lat->nvertices--;
	memmove(lat->vertices+i, lat->vertices+i+1, sizeof(struct lattice_vertex*)*(lat->nvertices-i));
}

void	remove_lattice_edge(struct lattice	*lat, struct lattice_edge	*e)
{
	int	i;
	for(i=0;i<lat->nedges;i++)
		if(lat->edges[i] == e)break;
	assert(i<lat->nedges);
	lat->nedges--;
	memmove(lat->edges+i, lat->edges+i+1, sizeof(struct lattice_edge*)*(lat->nedges-i));
	remove_lattice_vertex_follower(e->from, e);
	maybe_dead_lattice_vertex(lat, e->from);
	maybe_dead_lattice_vertex(lat, e->to);
}

struct dg	*lattice_dg(struct lattice_edge	*le)
{
	if(le->token) return le->token->dg;
	if(le->edge) return le->edge->dg;
	else assert(!"lattice edge with no content dag");
}

struct re_match_set
{
	wchar_t		**strings;
	regmatch_t	**matches;
};

void	replace_backrefs(struct dg	*d, struct dg	*rd, struct lattice_rule	*r, struct re_match_set	*mats)
{
	d = dereference_dg(d);
	if(d->xtype->name[0]=='"')
	{
		if(!strstr(d->xtype->name, "${"))return;
		if(d->xtype != rd->xtype)return;	// things that look like backrefs that don't appear in the *rule* came from copying coincidentally backref-like material from inputs or contexts.
		char	*backref, *last = d->xtype->name, *patchto, *backref_end;
		wchar_t	build[1024]=L"", *buildp = build;
		char	expr[128];
		while(1)
		{
			backref = strstr(last, "${");
			if(backref == NULL)patchto = last + strlen(last);
			else patchto = backref;
			char	tmp[patchto-last + 5];
			sprintf(tmp, "%.*s", (int)(patchto-last), last);
			buildp += swprintf(buildp, 1023, L"%s", tmp);
			if(backref == NULL)break;
			backref_end = strchr(backref, '}');
			if(!backref_end)goto badsyntax;
			last = backref_end+1;
			sprintf(expr, "%.*s", (int)(backref_end - (backref+2)), backref+2);
			int	l = strlen(expr);
			char	*from = strtok(expr, ":");
			char	*pathstr = strtok(NULL, ":");
			char	*cgnum_str = strtok(NULL, ":");
			int	do_lowercase = 0, do_uppercase = 0;
			if(!strncmp(from, "lc(", 3))
			{
				// XXX an ugly hack in the "standard" calls for an ugly hack in the implementation...
				from += 3;
				do_lowercase = 1;
			}
			if(!strncmp(from, "uc(", 3))
			{
				from += 3;
				do_uppercase = 1;
			}
			if(!from || !pathstr || !cgnum_str || !isalpha(from[0]) || !isdigit(from[1]))
			{
				badsyntax:
				fprintf(stderr, "bad backref syntax: %s in rule '%s'\n", d->xtype->name, r->name);
				exit(-1);
			}
			int	cgnum = atoi(cgnum_str) - 1;
			char	from_what = from[0];
			int	from_which = from[1]-'1';
			if(from_what == 'C')from_which += r->ninput;
			int	i;
			struct re_match_set	*mat = mats+from_which;
			struct lattice_regex_constraints	*rec = r->regex_constraints+from_which;
			for(i=0;pathstr[i];i++)if(pathstr[i]=='.')pathstr[i]=' ';
			struct path	path = slab_string_to_path(pathstr);
			for(i=0;i<rec->count;i++)
				if(!pathcmp(&rec->paths[i], &path))break;
			if(i==rec->count)
			{
				fprintf(stderr, "bad backref %s in rule '%s': no regex at that path.\n", d->xtype->name, r->name);
				exit(-1);
			}
			if(cgnum >= rec->re[i].re_nsub)
			{
				fprintf(stderr, "bad backref %s in rule '%s': asked for capture group %d (but only have %d)\n", d->xtype->name, r->name, (int)(cgnum+1), (int)(rec->re[i].re_nsub));
				exit(-1);
			}
			DEBUG_VERBOSE("should patch from %d path %s refid %d -- and found it (source string '%S')\n", from_which, pathstr, cgnum, mat->strings[i]);
			int	so = mat->matches[i][cgnum+1].rm_so;
			int	eo = mat->matches[i][cgnum+1].rm_eo;
			wchar_t	*ptr = mat->strings[i]+so;
			if(!do_lowercase && !do_uppercase)
			{
				while(so<eo)
				{
					*buildp++ = *ptr++;
					so++;
				}
			}
			else
			{
				wchar_t	str[512], *wp = str;
				swprintf(str, 511, L"%.*S", eo-so, ptr);
				while(*wp)
				{
					if(do_lowercase)
					{
						*wp = towlower(*wp);
						/*if(iswupper(*wp))
						{
							// this triggered on 42630 L'Ꚇ' -- so I turned it off. (sweaglesw July 30 2015)
							fprintf(stderr, "yikes! '%C' is uppercase and lowercase\n", *wp);
							exit(-1);
						}*/
						wp++;
					}
					else if(do_uppercase)
					{
						*wp = towupper(*wp);
						/*if(iswlower(*wp))
						{
							fprintf(stderr, "yikes! '%C' is uppercase and lowercase\n", *wp);
							exit(-1);
						}*/
						wp++;
					}
				}
				wp = str;
				while(*wp)
					*buildp++ = *wp++;
			}
		}
		DEBUG_VERBOSE("built string: `%S'\n", build);
		d->xtype = d->type = lookup_type(freeze_tombs(build));
		DEBUG_VERBOSE("... resulting in type '%s'\n", d->xtype->name);
	}
	else
	{
		// recurse over all children
		int	i;
		struct dg	**da = DARCS(d);
		for(i=0;i<d->narcs;i++)
		{
			struct dg	*rda = dg_hop(rd, d->label[i]);
			if(rda) replace_backrefs(da[i], rda, r, mats);
			// else no replacement; this branch is not present in the rule, so it can't contain backrefs
		}
	}
}

struct token	*extract_token_from_dg(struct dg	*dg)
{
	struct token	*t = slab_alloc(sizeof(struct token));
	bzero(t, sizeof(*t));
	t->eid = next_eid();
	t->dg = dg;
	struct dg	*str_dg = dg_path(dg, token_form_path);
	assert(str_dg != NULL);
	t->string = freeze_string(str_dg->xtype->name+1);
	int	sl = strlen(t->string);
	assert(sl>0 && t->string[sl-1]=='"');
	t->string[sl-1] = 0;
	struct dg	*cfrom_dg = dg_path(dg, token_from_path);
	assert(cfrom_dg != NULL);
	struct dg	*cto_dg = dg_path(dg, token_to_path);
	assert(cto_dg != NULL);
	t->cfrom = atoi(cfrom_dg->xtype->name+1);
	t->cto = atoi(cto_dg->xtype->name+1);
	// don't bother extracting the postags list
	t->npostags = 0;
	t->postags = NULL;
	/*struct dg	*taglist_dg = dg_path(dg, token_postags_path);
	assert(taglist_dg != NULL);
	struct dg	*tagfirst_dg = dg_hop(taglist_dg, 1);	// FIRST
	if(tagfirst_dg)
	{
		t->postag = freeze_string(tagfirst_dg->xtype->name+1);
		int	sl = strlen(t->postag);
		assert(sl>0 && t->postag[sl-1]=='"');
		t->postag[sl-1] = 0;
	}
	else t->postag = NULL;*/
	t->oc = NULL;
	return t;
}

static char	*possible_map;

int	lattice_mapping_rule_output(struct lattice	*lat, struct lattice_rule	*r, struct lattice_edge	**inputs, int	*input_ids, struct re_match_set	*mats, struct dg	**out_dg)
{
	int	did_add = 0, did_remove = 0;

	// first step: iterate through all the out_dg's and replace backreferences
	int i, j;
	for(i=0;i<r->noutput;i++)
	{
		struct dg	*rout_dg = lattice_rule_spot(r, i+r->ninput+r->ncontext);
		replace_backrefs(out_dg[i], rout_dg, r, mats);
	}
	// second step: build and insert edge structures for the new tokens
	// determining the from/to vertices for each output edge is a bit tricky

	// allocate blank output edges
	struct lattice_edge	*le = slab_alloc(sizeof(*le) * r->noutput);
	bzero(le,sizeof(*le)*r->noutput);
	// determine vertices
	for(i=0;i<r->nposition_constraints;i++)
	{
		struct lattice_position_constraint	*lpc = r->position_constraints+i;
		switch(lpc->type)
		{
			case	lpcImmediatelyPreceeds:
				if(lpc->lhs_what=='O' && lpc->rhs_what=='O')
				{
					// invent a new vertex for lhs's TO and rhs's FROM
					struct lattice_vertex	*v = new_lattice_vertex(lat);
					le[lpc->lhs_which].to = v;
					le[lpc->rhs_which].from = v;
				}
				else if(lpc->lhs_what=='O')
				{
					// set lhs's TO to rhs's FROM
					int	which = lpc->rhs_which;
					if(lpc->rhs_what == 'C')which += r->ninput;
					le[lpc->lhs_which].to = inputs[which]->from;
				}
				else if(lpc->rhs_what=='O')
				{
					// set rhs's FROM to lhs's TO
					int	which = lpc->lhs_which;
					if(lpc->lhs_what == 'C')which += r->ninput;
					le[lpc->rhs_which].from = inputs[which]->to;
				}
				break;
			case	lpcCovers:
				if(lpc->lhs_what=='O' && lpc->rhs_what=='O')
				{
					assert(!"don't know how to implement Ox@Oy positional constraints");
				}
				else if(lpc->lhs_what=='O')
				{
					// make sure lhs covers rhs
					// if lhs has NULL endpoints, copy rhs's
					int	which = lpc->rhs_which;
					if(lpc->rhs_what == 'C')which += r->ninput;
					struct lattice_edge	*rhs = inputs[which];
					struct lattice_edge	*lhs = &le[lpc->lhs_which];
					if(!lhs->to || lattice_vertex_follows(lat, rhs->to, lhs->to))
						lhs->to = rhs->to;
					if(!lhs->from || lattice_vertex_follows(lat, lhs->from, rhs->from))
						lhs->from = rhs->from;
				}
				else if(lpc->rhs_what=='O')
				{
					// verify that lhs covers rhs
					// if rhs has NULL endpoints, copy lhs's
					int	which = lpc->lhs_which;
					if(lpc->lhs_what == 'C')which += r->ninput;
					struct lattice_edge	*lhs = inputs[which];
					struct lattice_edge	*rhs = &le[lpc->rhs_which];
					if(!rhs->to)rhs->to = lhs->to;
					else if(lattice_vertex_follows(lat, rhs->to, lhs->to))
						assert(!"inconsistant lattice mapping positional constraints");
					if(!rhs->from)rhs->from = lhs->from;
					else if(lattice_vertex_follows(lat, lhs->from, rhs->from))
						assert(!"inconsistant lattice mapping positional constraints");
				}
				break;
		}
	}

	struct lattice_edge	*save_le[r->noutput];

	// add them to the lattice
	for(i=0;i<r->noutput;i++)
	{
		if(!le[i].from || !le[i].to)
			assert(!"incomplete lattice mapping positional constraints");

		int	j;
		struct lattice_vertex	*from = le[i].from, *to = le[i].to;

#ifdef	SHOW_OUTPUT_TOKENS
		printf("want to add token dag [%d -> %d]: \n", from->id, to->id); print_dg(out_dg[i]); printf("\n");
#endif

		for(j=0;j<from->nfollowers;j++)
		{
			struct lattice_edge	*e = from->followers[j];
			if(e->to != to)continue;
			//printf("checking for eq with %p\n", e);
			//printf("which is:\n");print_dg(lattice_dg(e));printf("\n");
			if(equivalent_dg(out_dg[i], lattice_dg(e), 1, 1, 0) == 2)break;
		}
		if(j<from->nfollowers)
		{
			DEBUG("... not adding that edge, since we had an identical one already.\n");
			save_le[i] = from->followers[j];
			continue;
		}
		save_le[i] = NULL;

		if(mapping_tokens)
		{
			le[i].token = extract_token_from_dg(out_dg[i]);
			DEBUG("O%d = `%s' [%d - %d] = %p\n", i+1, le[i].token->string, le[i].from->id, le[i].to->id, &le[i]);
		}
		else
		{
			struct lexeme	*inlex = r->ninput?inputs[0]->edge->lex:NULL;
			le[i].edge = new_edge(out_dg[i]);
			le[i].edge->lex = inlex;
		}
		update_possible_map_add(lat, lat->nedges, &le[i], r, mats);	// this bumps generation and clobbers `mats'; fortunately, we've already gotten what we need.
		add_lattice_edge(lat, &le[i]);
		did_add++;
	}

	// third step: remove input edge structures
	for(i=0;i<r->ninput;i++)
	{
		for(j=0;j<r->noutput;j++)
			if(save_le[j] == inputs[i])
				break;
		if(j<r->noutput)continue;
		update_possible_map_remove(lat, input_ids[i], r);
		remove_lattice_edge(lat, inputs[i]);
		did_remove++;
		// adjust remaining input_ids so as to reduce possible_map correctly
		for(j=i+1;j<r->ninput;j++)
			if(input_ids[j] > input_ids[i])
				input_ids[j]--;
	}
	/*for(i=0;i<r->ninput;i++)
	{
		for(j=0;j<r->noutput;j++)
			if(save_le[j] == inputs[i])
				break;
		if(j<r->noutput)continue;
		remove_lattice_edge(lat, inputs[i]);
		did_remove++;
	}*/
	if(mapping_tokens)nmappingtokens += did_add;
	return did_add + did_remove;
}

// for the currently active rule:
struct failure
{
	int	from, to;
	struct lattice_edge	**inputs;
}	*failed_unify_inputs;
int					nfailed_unify_inputs;

static int	same_unify_inputs(struct lattice_edge	**ins, int	from, int	to, struct failure	*fail)
{
	if(from != fail->from || to != fail->to)return 0;
	int i;
	for(i=from;i<to;i++)
		if(ins[i] != fail->inputs[i-from])return 0;
	return 1;
}

static int	check_already_failed(struct lattice_edge	**inputs, int	from, int	to)
{
	int	i;
	for(i=0;i<nfailed_unify_inputs;i++)
		if(same_unify_inputs(inputs, from, to, &failed_unify_inputs[i]))
			return 1;
	return 0;
}

static void	record_failed(struct lattice_edge	**inputs, int	from, int	to)
{
	nfailed_unify_inputs++;
	failed_unify_inputs = realloc(failed_unify_inputs, sizeof(struct failure)*nfailed_unify_inputs);
	struct failure	*f = &failed_unify_inputs[nfailed_unify_inputs-1];
	f->from = from;
	f->to = to;
	f->inputs = malloc(sizeof(void*)*(to-from));
	memcpy(f->inputs, inputs+from, sizeof(void*)*(to-from));
}

static void clear_failed()
{
	int i;
	for(i=0;i<nfailed_unify_inputs;i++)
		free(failed_unify_inputs[i].inputs);
	nfailed_unify_inputs = 0;
}

/*
int	lattice_vertex_is_initial(struct lattice	*lat, struct lattice_vertex	*v)
{
	int i;
	for(i=0;i<lat->nedges;i++)
		if(lat->edges[i]->to == v)return 0;
	return 1;
}

int lattice_vertex_is_final(struct lattice	*lat, struct lattice_vertex	*v)
{
	if(v->nfollowers == 0)return 1;
	return 0;
}
*/

int	lattice_rule_matches(struct lattice	*lat, struct lattice_rule	*r, struct lattice_edge	**inputs, int	from, int	to, struct re_match_set	*mats)
{
	int	i, j;

	// verify that the inputs match the position constraints
	for(i=0;i<r->nposition_constraints;i++)
	{
		struct lattice_position_constraint	*pc = r->position_constraints+i;
		if(pc->lhs_what == 'O' || pc->rhs_what == 'O')continue;
		int	lhs_which = pc->lhs_which;
		if(pc->lhs_what == 'C')lhs_which += r->ninput;
		int	rhs_which = pc->rhs_which;
		if(pc->rhs_what == 'C')rhs_which += r->ninput;
		struct lattice_vertex	*rhs_start, *rhs_end;
		if(pc->rhs_what == '^' || pc->rhs_what == '$')
			rhs_start = rhs_end = NULL;
		else
		{
			if(rhs_which >= to || rhs_which < from)continue;
			rhs_start = inputs[rhs_which]->from;
			rhs_end = inputs[rhs_which]->to;
		}
		struct lattice_vertex	*lhs_start, *lhs_end;
		if(pc->lhs_what == '^' || pc->lhs_what == '$')
			lhs_start = lhs_end = NULL;
		else
		{
			if(lhs_which >= to || lhs_which < from)continue;
			lhs_start = inputs[lhs_which]->from;
			lhs_end = inputs[lhs_which]->to;
		}
		switch(pc->type)
		{
			case	lpcImmediatelyPreceeds:
				assert(pc->lhs_what != '$' && pc->rhs_what != '^');
				if(pc->lhs_what == '^')
				{
					//if(!lattice_vertex_is_initial(lat, rhs_start))
					if(lat->start != rhs_start)
					{
						DEBUG_VERBOSE("failed ^< test\n");
						return 0;
					}
				}
				else if(pc->rhs_what == '$')
				{
					//if(!lattice_vertex_is_final(lat, lhs_end))
					if(lat->end != lhs_end)
					{
						DEBUG_VERBOSE("failed <$ test\n");
						return 0;
					}
				}
				else if(lhs_end != rhs_start)
				{
					DEBUG_VERBOSE("failed immediate preceeder test\n");
					return 0;
				}
				break;
			case	lpcPreceeds:
				assert(pc->lhs_what != '$' && pc->lhs_what != '^' && pc->rhs_what != '$' && pc->rhs_what != '^');
				if(!(lattice_vertex_follows(lat, rhs_start, lhs_end) || lhs_end==rhs_start))
				{
					DEBUG_VERBOSE("failed somewhere-preceeder test\n");
					return 0;
				}
				break;
			case	lpcCovers:
				assert(pc->lhs_what != '$' && pc->lhs_what != '^' && pc->rhs_what != '$' && pc->rhs_what != '^');
				if(! ((lattice_vertex_follows(lat, rhs_start, lhs_start) || rhs_start==lhs_start)
				   && (lattice_vertex_follows(lat, lhs_end, rhs_end) || lhs_end==rhs_end)))
				{
					DEBUG_VERBOSE("failed covers test\n");
					return 0;
				}
				break;
		}
	}
	// verify regular expression matches
	for(i=from;i<to;i++)
	{
		struct dg	*idg = lattice_dg(inputs[i]);//lattice_rule_spot(r, i);
		struct lattice_regex_constraints	*rec = r->regex_constraints+i;
		if(mats)
		{
			mats[i].strings = slab_alloc(sizeof(wchar_t*) * rec->count);
			mats[i].matches = slab_alloc(sizeof(regmatch_t*) * rec->count);
		}
		for(j=0;j<rec->count;j++)
		{
			//printf("... should hop path: "); print_path(rec->paths[j]); printf("\n");
			//printf(" from dg: "); print_dg(idg); printf("\n");
			struct dg	*str_dg = dg_path(idg, rec->paths[j]);
			if(str_dg)
			{
				char	*str = str_dg->xtype->name;
				int	l = strlen(str);
				char	copy[256];
				int	l2 = snprintf(copy, 255, "%.*s", l-2, str+1);
				if(l2 >= 254)
				{
					DEBUG_VERBOSE(" ... trying to match too long a string; failing.\n");
					return 0;
				}
				wchar_t	*wcopy = towide(copy);
				regex_t	re = rec->re[j];
				DEBUG_VERBOSE("... comparing string '%S' against regex '%S'\n", wcopy, rec->regexs[j]);
				regmatch_t	m[re.re_nsub+1], *M = m;
				if(mats)
				{
					mats[i].strings[j] = freeze_wcs(wcopy);
					mats[i].matches[j] = slab_alloc(sizeof(regmatch_t) * (re.re_nsub+1));
					M = mats[i].matches[j];
				}
				int	result = regexec(&re, wcopy, re.re_nsub+1, M, 0);
				//int	wl = wstrlen(wcopy);
				free(wcopy);
				if(0 == result)// && M[0].rm_so==0 && M[0].rm_eo==wl)
				{
					DEBUG_VERBOSE(" ... matched!\n");
				}
				else
				{
					DEBUG_VERBOSE(" ... didn't match.\n");
					return 0;
				}
			}
			else return 0;
		}
	}
	if(check_already_failed(inputs, from, to))return 0;
	// verify inputs unify into the rule
	for(i=from;i<to;i++)
	{
		if(unify_dg_tmp(lattice_dg(inputs[i]), lattice_rule_spot(r, i), -1) != 0)
		{
			forget_tmp();
			DEBUG_VERBOSE(" ... didn't unify\n");
			//printf("lattice-mapping-failure-path "); unify_backtrace();
			//print_dg(lattice_rule_spot(r,i));printf("\n");
			record_failed(inputs, from, to);
			return 0;
		}
	}
	return 1;
}

// TODO find a more efficient algorithm for finding application sites
// TODO keep a cache of what rule already failed to unify with what edge... a *lot* of wasted unification attempts
// TODO   -- or use quickcheck?
int	apply_lattice_rule1(struct lattice	*lat, struct lattice_rule	*r, struct lattice_edge	**inputs, int	*input_ids, int	have, struct re_match_set	*mats)
{
	int i, j;
	if(have>0)
	{
		if(0 == lattice_rule_matches(lat, r, inputs, 0, have, mats))
			return 0;
	}
	if(have == r->ninput + r->ncontext)
	{
		// apply the rule as matched
		DEBUG("found an alignment of rule '%s'\n", r->name);
		if(lm_just_list || lm_break_before || lm_break_after)
			printf("LATTICE-MAPPING: applying %s\n", r->name);
		if(inputs[0]->token)
		{
			for(i=0;i<r->ninput;i++)DEBUG("I%d = '%s' = %p\n", i+1, inputs[i]->token->string, inputs[i]);
			for(i=0;i<r->ncontext;i++)DEBUG("C%d = '%s'\n", i+1, inputs[r->ninput+i]->token->string);
		}
		else
		{
			for(i=0;i<r->ninput;i++)
			{
				if(inputs[i]->edge->lex)
				{
					DEBUG("I%d = '#%d' %s %d-%d\n", i+1, inputs[i]->edge->id, inputs[i]->edge->lex->word, inputs[i]->edge->from, inputs[i]->edge->to);
				}
			}
			for(i=0;i<r->ncontext;i++)
			{
				if(inputs[r->ninput+i]->edge->lex)
				{
					DEBUG("C%d = '#%d' %s %d-%d\n", i+1, inputs[r->ninput+i]->edge->id, inputs[r->ninput+i]->edge->lex->word, inputs[r->ninput+i]->edge->from, inputs[r->ninput+i]->edge->to);
				}
			}
		}
		struct dg	*out_dg[r->noutput];
		for(i=0;i<r->noutput;i++)
		{
			struct dg	*o = lattice_rule_spot(r, i+r->ninput+r->ncontext);
			// don't want the different outputs to share structure with each other; if they do and are later on recombined, spurious reentrancies will occur.
			dagreset_c_including_carcs(o);
			out_dg[i] = copy_dg_with_comp_arcs(o);
			if(!out_dg[i])
			{
				fprintf(stderr, "ERROR: cyclic result of lattice mapping rule %s\n", r->name);
				exit(-1);
			}
		}
		bump_generation();

		return lattice_mapping_rule_output(lat, r, inputs, input_ids, mats, out_dg);
	}
	else
	{
		if(have)bump_generation();
		// find next input candidate

	//	for(i=0;i<lat->nvertices;i++)
	//		for(j=0;j<lat->vertices[i]->nfollowers;j++)
	//		{
	//			struct lattice_edge	*e = lat->vertices[i]->followers[j];
		for(i=0;i<lat->nedges;i++)
			{
				struct lattice_edge	*e = lat->edges[i];

				// make sure we haven't already ruled out this input
				if(possible_map && !possible_map[have + (r->ninput + r->ncontext)*i])
					continue;
				// make sure we don't already have 'e' in inputs[]
				int k;
				for(k=0;k<have;k++)
					if(inputs[k] == e)break;
				if(k<have)continue;
				inputs[have] = e;
				input_ids[have] = i;
				if(e->token)
					DEBUG_VERBOSE(".. considering '%s' as inputs[%d] for rule %s\n", e->token->string, have, r->name);
				else 
					DEBUG_VERBOSE(".. considering '#%d' as inputs[%d] for rule %s\n", e->edge->id, have, r->name);
				int	result = apply_lattice_rule1(lat, r, inputs, input_ids, have+1, mats);
				if(result)return result;
			}
		return 0;
	}
}

struct profiler	**tmr_profilers = NULL, *tmr_poss_prof = NULL;
struct profiler	**lfr_profilers = NULL, *lfr_poss_prof = NULL;
struct profiler	*lattice_mapping_profiler = NULL;
struct profiler	**lattice_mapping_poss_profiler = NULL;
extern int g_profiling;

void	update_possible_map_add(struct lattice	*lat, int	id, struct lattice_edge	*e, struct lattice_rule	*r, struct re_match_set	*mats)
{
	if(!possible_map)return;
	assert(id == lat->nedges);
	struct lattice_edge	*inputs[r->ninput + r->ncontext];
	int	rowsize = (r->ninput + r->ncontext);
	possible_map = realloc(possible_map, rowsize * (lat->nedges+1));
	int i;
	for(i=0;i<rowsize;i++)
	{
		inputs[i] = e;
		bump_generation();
		int pos = lattice_rule_matches(lat, r, inputs, i, i+1, mats);
		possible_map[id*rowsize + i] = pos;
	}
}

void	update_possible_map_remove(struct lattice	*lat, int	id, struct lattice_rule	*r)
{
	if(!possible_map)return;
	assert(id>=0 && id<lat->nedges);
	int	rowsize = (r->ninput + r->ncontext);
	char	*dead_row = &possible_map[0 + rowsize*id];
	int		rows_after_dead_row = lat->nedges - (id+1);
	memmove(dead_row, dead_row + rowsize, rowsize * rows_after_dead_row);
}

int	initialize_possible_map(struct lattice	*lat, struct lattice_rule	*r)
{
	int	result = 1, nspots = 0;
	struct re_match_set	*mats = malloc(sizeof(struct re_match_set)*(r->ninput+r->ncontext));
	struct lattice_edge	*inputs[r->ninput + r->ncontext];
	possible_map = NULL;
	if(g_profiling && lattice_mapping_poss_profiler)start_and_alloc_profiler(lattice_mapping_poss_profiler, "latmap possible", lattice_mapping_profiler, NULL);
	if(r->ninput + r->ncontext > 1)
	{
		possible_map = malloc((r->ninput+r->ncontext) * lat->nedges);
		int i, j;
		for(i=0;i<r->ninput+r->ncontext;i++)
		{
			int	count = 0;
			for(j=0;j<lat->nedges;j++)
			{
				inputs[i] = lat->edges[j];
				bump_generation();
				int pos = lattice_rule_matches(lat, r, inputs, i, i+1, mats);
				possible_map[j*(r->ninput+r->ncontext) + i] = pos;
				if(pos)count++;
			}
			if(!count)
			{
				// no possible matches for this rule position.
				result = 0;
				break;
			}
			nspots++;
		}
	}
	free(mats);
	if(g_profiling && lattice_mapping_poss_profiler)stop_profiler(*lattice_mapping_poss_profiler, nspots*(lat->nedges));
	return result;
}

// this function gets called over and over again for the *same lattice rule r*,
// when it applies to multiple places in the lattice.
// we are recomputing the `possible_map' every time,
// whereas in practice there will only be a couple of edges that have changed.
// (typically 0-2 deletions and 0-2 insertions, out of dozens of edges)
// we need to figure out how to reuse the still-valid parts of the possible_map;
// computing the possible_map is eating up most of the time spent here.
int	apply_lattice_rule(struct lattice	*lat, struct lattice_rule	*r)
{
	DEBUG("trying to apply '%s'...\n", r->name);
	struct lattice_edge	*inputs[r->ninput + r->ncontext];
	int	input_ids[r->ninput + r->ncontext];
	struct re_match_set	*mats = malloc(sizeof(struct re_match_set)*(r->ninput+r->ncontext));
	int result = 0;
	result = apply_lattice_rule1(lat, r, inputs, input_ids, 0, mats);
	free(mats);
	return result;
}

struct profiler	*start_lmr_profiler(struct lattice_rule_set	*rs, int	ri)
{
	struct profiler	***lmr_profilers = ((rs==token_mapping_rules)?(&tmr_profilers):((rs==lexical_filtering_rules)?(&lfr_profilers):NULL));
	if(!lmr_profilers)return NULL;
	if(!lattice_mapping_profiler)return NULL;
	lattice_mapping_poss_profiler = ((rs==token_mapping_rules)?(&tmr_poss_prof):((rs==lexical_filtering_rules)?(&lfr_poss_prof):NULL));

	lattice_mapping_profiler->sortable = 5;
	if(!*lmr_profilers)*lmr_profilers = calloc(sizeof(**lmr_profilers), rs->nrules);
	start_and_alloc_profiler((*lmr_profilers)+ri, rs->rules[ri]->name, lattice_mapping_profiler, NULL);
	return (*lmr_profilers)[ri];
}

lm_break(struct lattice	*lat, struct lattice_rule	*r)
{
	char	name[1024];
	if(lm_just_list)printf("LATTICE-MAPPING: %s\n", r?r->name:"ENDPOINT");
	sprintf(name, "%s lattice mapping rule %s", lm_break_before?"before":"after", r?r->name:"ENDPOINT");
	if(r)output_lui_dg(r->dg, r->name);
	int	id = lui_show_tokens(lat, name);
	lui_await_amnesia(id);
}

debug_lattice_mapping(char	*args)
{
	if(*args==' ')args++;
	lm_breakpoint = NULL;
	lm_break_before = lm_break_after = 0;
	lm_just_list = 0;
	lm_break_after_finish = 0;
	lm_break_before_start = 0;
	int	all = 0;
	char	*tok;
	for(tok=strtok(args," ,");tok;tok=strtok(NULL," ,"))
	{
		if(!strcmp(tok, "all"))all = 1;
		else if(!strcmp(tok, "before"))lm_break_before = 1;
		else if(!strcmp(tok, "after"))lm_break_after = 1;
		else if(!strcmp(tok, "list"))lm_just_list = 1;
		else if(!strcmp(tok, "clear")) {}
		else lm_breakpoint = strdup(tok);
	}
	if(lm_break_after && !all && !lm_breakpoint)
		lm_break_after_finish = 1;
	if(lm_break_before && !all && !lm_breakpoint)
		lm_break_before_start = 1;
	if(lm_just_list && !lm_breakpoint)all = 1;
	if(all)lm_breakpoint = NULL;
	if((all || lm_breakpoint) && !lm_break_before && !lm_break_after)
		lm_break_after = 1;
	if(lm_break_after && lm_break_before)lm_break_before = 0;
}

void	apply_lattice_mapping(struct lattice	*lat, struct lattice_rule_set	*rs)
{
	int	pc = 0;
	int possible = 1;

	if(rs == token_mapping_rules && lm_break_before_start)
		lm_break(lat, NULL);
	while(pc < rs->nrules)
	{
		clear_failed();
		struct profiler	*prof = NULL;
		if(g_profiling)prof = start_lmr_profiler(rs, pc);
		struct lattice_rule	*r = rs->rules[pc];
		if(!lm_break_before_start && !lm_break_after_finish && !lm_just_list && lm_break_before && (lm_breakpoint && !strcasecmp(r->name, lm_breakpoint)))
			lm_break(lat, r);
		if(!possible_map)possible = initialize_possible_map(lat, r);
		int result = possible?apply_lattice_rule(lat, r):0;
		if(!lm_break_before_start && !lm_break_after_finish && !lm_just_list && (lm_breakpoint || result) && lm_break_after && (!lm_breakpoint || !strcasecmp(r->name, lm_breakpoint)))
			lm_break(lat, r);
		if(result != 0)
		{
			// found and applied a match.
			if(pc != r->jump_on_match)
			{
				pc = r->jump_on_match;
				if(possible_map)free(possible_map);
				possible_map = NULL;
			}
		}
		else
		{
			// no more matches for this rule.
			pc++;
			if(possible_map)free(possible_map);
			possible_map = NULL;
		}
		if(prof)stop_profiler(prof, 1);
	}
	if(rs == token_mapping_rules && lm_break_after_finish)
		lm_break(lat, NULL);
}

int	load_token_mapping_rules()
{
	if(enable_token_avms)
		token_mapping_rules = load_lattice_rules("token-mapping-rule");
	else token_mapping_rules = calloc(sizeof(struct lattice_rule_set),1);
	return 0;
}

void	apply_token_mapping(struct lattice	*lat)
{
	lattice_mapping_profiler = token_mapping_profiler;
	mapping_tokens = 1;
	noriginaltokens = lat->nedges;
	nmappingtokens = lat->nedges;
	apply_lattice_mapping(lat, token_mapping_rules);
	mapping_tokens = 0;
}

int	load_lexical_filtering_rules()
{
	lexical_filtering_rules = load_lattice_rules("lexical-filtering-rule");
	return 0;
}

void	apply_lexical_filtering(struct lattice	*lat)
{
	lattice_mapping_profiler = lexical_filtering_profiler;
	apply_lattice_mapping(lat, lexical_filtering_rules);
}

int	load_post_generation_mapping_rules()
{
	post_generation_mapping_rules = load_lattice_rules("post-generation-mapping-rule");
	if(post_generation_mapping_rules->nrules)
	{
		extern int enable_post_generation_mapping;
		enable_post_generation_mapping = 1;
	}
	return 0;
}

void	apply_post_generation_mapping_rules(struct lattice	*lat)
{
	lattice_mapping_profiler = post_generation_mapping_profiler;
	apply_lattice_mapping(lat, post_generation_mapping_rules);
}

struct lattice	*edge_list_to_lattice(int	n, void	**list)
{
	struct lattice	*l = slab_alloc(sizeof(*l));
	bzero(l, sizeof(*l));
	int k;
	for(k=0;k<=n;k++)new_lattice_vertex(l);
	l->start = l->vertices[0];
	l->end = l->vertices[n];
	for(k=0;k<n;k++)
	{
		struct lattice_edge	*e = slab_alloc(sizeof(*e));
		bzero(e, sizeof(*e));
		e->from = l->vertices[k];
		e->to = l->vertices[k+1];
		e->edge = list[k];
		add_lattice_edge(l, e);
	}
	return l;
}

struct edge	*duplicate_lexical_edge(struct edge	*e)
{
	if(e->unpack)return (struct edge*)e->unpack;
	struct edge	*e2 = slab_alloc(sizeof(struct edge));
	*e2 = *e;
	e->unpack = (struct unpack_info*)e2;
	if(e->have)
	{
		int i;
		e2->daughters = slab_alloc(sizeof(struct edge*) * e->have);
		for(i=0;i<e->have;i++)e2->daughters[i] = duplicate_lexical_edge(e->daughters[i]);
	}
	return e2;
}

struct lattice_edge	*duplicate_lexical_lattice_edge(struct lattice_edge	*le)
{
	struct lattice_edge	*e2 = slab_alloc(sizeof(*e2));
	e2->edge = duplicate_lexical_edge(le->edge);
	e2->token = NULL;
	e2->from = le->from;
	e2->to = le->to;
	return e2;
}

struct lattice_vertex	*duplicate_lattice_vertex(struct lattice_vertex	*v)
{
	struct lattice_vertex	*v2 = slab_alloc(sizeof(*v2));
	*v2 = *v;
	v2->followers = slab_alloc(sizeof(struct lattice_edge*)*v2->nfollowers);
	return v2;
}

struct lattice_vertex	*patch_vertex(struct lattice_vertex	*vold, struct lattice	*oldl, struct lattice	*newl)
{
	int i;
	assert(oldl->nvertices == newl->nvertices);
	for(i=0;i<oldl->nvertices;i++)
		if(oldl->vertices[i] == vold)return newl->vertices[i];
	assert(!"not reached");
}

patch_lattice_edge_vertices(struct lattice_edge	*e, struct lattice	*oldl, struct lattice	*newl)
{
	e->from = patch_vertex(e->from, oldl, newl);
	e->to = patch_vertex(e->to, oldl, newl);
}

patch_lattice_vertex_followers(struct lattice_vertex	*v, struct lattice	*newl)
{
	int i, afol = v->nfollowers;
	v->nfollowers = 0;
	for(i=0;i<newl->nedges;i++)
		if(newl->edges[i]->from == v)
		{
			assert(v->nfollowers < afol);
			v->followers[v->nfollowers++] = newl->edges[i];
		}
}

void	clear_unpack_slot(struct edge	*e)
{
	int i;
	e->unpack = NULL;
	for(i=0;i<e->have;i++)clear_unpack_slot(e->daughters[i]);
}

struct lattice	*duplicate_lexical_lattice(struct lattice	*lat)
{
	struct lattice	*l = slab_alloc(sizeof(*l));
	int i;
	*l = *lat;
	for(i=0;i<l->nedges;i++)clear_unpack_slot(lat->edges[i]->edge);
	l->edges = slab_alloc(sizeof(struct lattice_edge*)*l->nedges);
	for(i=0;i<l->nedges;i++)l->edges[i] = duplicate_lexical_lattice_edge(lat->edges[i]);
	l->vertices = slab_alloc(sizeof(struct lattice_vertx*)*l->nvertices);
	for(i=0;i<l->nvertices;i++)l->vertices[i] = duplicate_lattice_vertex(lat->vertices[i]);
	for(i=0;i<l->nedges;i++)patch_lattice_edge_vertices(l->edges[i], lat, l);
	for(i=0;i<l->nvertices;i++)patch_lattice_vertex_followers(l->vertices[i], l);
	l->start = patch_vertex(lat->start, lat, l);
	l->end = patch_vertex(lat->start, lat, l);
	for(i=0;i<l->nedges;i++)clear_unpack_slot(lat->edges[i]->edge);
	return l;
}
