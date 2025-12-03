#define	UNICODE
#define	REPP_INTERNAL
#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<boost/regex.h>

#include	"unicode.h"
#include	"librepp.h"

#define	REGEX_FLAGS	REG_PERL

//#define	DEBUG	printf
#define	DEBUG(fmt, ...)	do {} while(0)

struct transformed_string
{
	int	length;
	wchar_t	*string;
	int	*align;
};

static struct transformed_string	replace(struct transformed_string	its, regmatch_t	*m, wchar_t	*r)
{
	wchar_t	*out, *p;

	out = malloc(sizeof(wchar_t)*(its.length*2 + wstrlen(r) + 1));
	int	*align = malloc(sizeof(int)*(its.length*2 + wstrlen(r) + 1));
	int	*pa;

	memcpy(out, its.string, sizeof(wchar_t)*m->rm_so);
	memcpy(align, its.align, sizeof(int) * m->rm_so);

	p = out + m->rm_so;
	pa = align + m->rm_so;
	wchar_t	*inp = its.string + m->rm_so;
	int		*ina = its.align + m->rm_so;

	wchar_t	lost_char = 0;
	int		lost_char_align = -1;
	int		*lost_char_align_hole = NULL;
	wchar_t	lost_char_hole = 0;

	void	process_lost_char(wchar_t	c, int	a)
	{
		if((c==' ' || c=='\t'))return;
		lost_char = c;
		lost_char_align = a;
		DEBUG("... lost '%C'=>%d\n", lost_char, lost_char_align);
		if(lost_char_align_hole)
		{
			if(lost_char_hole != lost_char)
			{
				DEBUG("filling hole '%C' with '%C'\n", lost_char_hole, lost_char);
			}
			*lost_char_align_hole = lost_char_align;
			lost_char_align_hole = NULL;
			lost_char_align = -1;
		}
	}

	while(*r)
	{
		if(*r == '\\' && r[1])
		{
			int		i = r[1] - '1';
			wchar_t	*x = its.string + m[1 + i].rm_so, *e = its.string + m[1 + i].rm_eo;
			int		*xa = its.align + m[1 + i].rm_so;

			// copying from 'x' to 'e' from input
			// ... see if we are skipping any non-whitespace chars
			while(inp < x)
				process_lost_char(*inp++, *ina++);
			inp += (m[1 + i].rm_eo - m[1 + i].rm_so);
			ina += (m[1 + i].rm_eo - m[1 + i].rm_so);

			// do the copy
			while(x<e)
			{
				*p++ = *x++;
				*pa++ = *xa++;
			}
			r += 2;
		}
		else
		{
			*pa = -1;
			// see if we are inserting any non-whitespace
			if(! (*r==' ' || *r=='\t'))
			{
				DEBUG("... hole for '%C'\n", *r);
				if(lost_char_align != -1)
				{
					if(*r != lost_char_align)
					{
						DEBUG("filling hole '%C' with '%C'\n", *r, lost_char_align);
					}
					*pa = lost_char_align;
					lost_char_align = -1;
				}
				else
				{
					lost_char_align_hole = pa;
					lost_char_hole = *r;
				}
			}
			pa++;
			*p++ = *r++;
		}
	}
	while(inp<its.string + m->rm_eo)
		process_lost_char(*inp++, *ina++);

	memcpy(p, its.string+m->rm_eo, sizeof(wchar_t)*(its.length - m->rm_eo));
	memcpy(pa, its.align+m->rm_eo, sizeof(int)*(its.length - m->rm_eo));
	p[its.length - m->rm_eo] = 0;

	free(its.string);
	free(its.align);

	struct transformed_string	ots;
	ots.length = wstrlen(out);
	ots.string = out;
	ots.align = align;
	return ots;
}

static struct transformed_string	preprocess_module(struct preprocessor	*repp, struct preprocessor_module	*mod, struct transformed_string	ts, int	*Nchanges)
{
	int	i;

	DEBUG("applying preprocessor module '%S'\n", mod->name);

	// apply string-level replacements
	for(i=0;i<mod->nrules;i++) switch(mod->rules[i].type)
	{
		case	rtReplace:
		{
			struct pprule	*r = &mod->rules[i];
			int				redo = ts.length, off;
			regmatch_t	m[r->re.re_nsub+1];
			again:
			off = ts.length - redo;
			if(!regexec(&r->re, ts.string+off, r->re.re_nsub+1, m, (off!=0 ? REG_NOTBOL : 0)))
			{
				int i; for(i=0;i<r->re.re_nsub+1;i++) { m[i].rm_so += off; m[i].rm_eo += off; }
				redo = ts.length - m->rm_eo;
				ts = replace(ts, m, r->rep);
				(*Nchanges)++;
				DEBUG(" `%S' -> `%S' yields `%S'\n", r->pat, r->rep, ts.string);
				if(redo)goto again;
			}
			break;
		}
		case	rtGroupCall:
		{
			struct preprocessor_module	*submod;
			DEBUG("looking up module '%S'\n", mod->rules[i].pat);
			submod = repp_find_module(repp, mod->rules[i].pat);
			if(!submod || !submod->is_enabled)break;
			int	subchanges;
			//if(submod->is_iterative)	// XXX disable all external groups temporarily
			do {
				subchanges = 0;
				ts = preprocess_module(repp, submod, ts, &subchanges);
				(*Nchanges) += subchanges;
			} while(subchanges > 0 && submod->is_iterative);
			break;
		}
	}

	return ts;
}

/*static void	repair_alignment(wchar_t	*input, struct transformed_string	ts)
{
	int	last_ip = -1;
	int	i, missing_count;

	for(i=0;i<ts.length;i++)
	{
		if(ts.align[i]==-1)
		{
			int	next_ip, missing_input_count;
			for(missing_count=0;i+missing_count<ts.length;missing_count++)
				if(ts.align[i+missing_count] != -1)break;
			if(i+missing_count==ts.length)
			{
				next_ip= wstrlen(input)+1;
			}
			else next_ip = ts.align[i+missing_count];
			missing_input_count = next_ip - (last_ip+1);
			if(missing_input_count == missing_count)
			{
				for(missing_count=0;missing_count<missing_input_count;missing_count++)
					ts.align[i+missing_count] = last_ip+1 + missing_count;
				i += missing_count-1;
			}
		}
		else last_ip = ts.align[i];
	}
}*/

int	repp_preprocess(struct preprocessor	*repp, char	*mbstring, int	*Nwords, char	***Words, int	**CFrom, int	**CTo)
{
	if(check_mbs(mbstring) != 0)return -1;

	int	nchanges = 0, i;
	DEBUG("preprocessing '%s'\n", mbstring);
	struct transformed_string	ts;
	ts.string = towide(mbstring);
	ts.length = wstrlen(ts.string);
	ts.align = malloc(sizeof(int) * ts.length);
	for(i=0;i<ts.length;i++)ts.align[i] = i;
	ts = preprocess_module(repp, repp->main_module, ts, &nchanges);
	DEBUG("rewrote to '%S' (%d changes)\n", ts.string, nchanges);

	wchar_t	*orig_str = towide(mbstring);
//	repair_alignment(orig_str, ts);

	// tokenize
	wchar_t	*p = ts.string;
	regmatch_t	b;
	int	nwords = 0;
	char	**words = NULL;
	int		*cfrom_array=NULL, *cto_array=NULL;

	int	n_missing =0;
	while(!regexec(&repp->delim, p, 1, &b, 0))
	{
		//printf("matched at pos %d-%d in '%S'\n", b.rm_so, b.rm_eo, p);
		if(b.rm_so!=0)
		{
			int	trans_c_from = p-ts.string;
			int	trans_c_to = (p-ts.string) + b.rm_so;
			
			wchar_t	*wide_token = calloc(b.rm_so+1,sizeof(wchar_t));
			memcpy(wide_token, p, (int)b.rm_so * sizeof(wchar_t));
			char	*heap_mbs = tombs(wide_token);

			int	c_from = wstrlen(orig_str);
			int	c_to = 0;
			for(i=trans_c_from;i<trans_c_to;i++)
			{
				if(ts.align[i] != -1)
				{
					if(ts.align[i] < c_from)c_from = ts.align[i];
					if(ts.align[i]+1 > c_to)c_to = ts.align[i]+1;
				}
				else n_missing++;
			}
			DEBUG("word %d = %S trans %d-%d orig %d-%d = '%.*S'\n", nwords+1, wide_token, trans_c_from, trans_c_to, c_from, c_to, (c_to-c_from), orig_str+c_from);

			nwords++;
			words = realloc(words, sizeof(char*)*nwords);
			words[nwords-1] = heap_mbs;
			cfrom_array = realloc(cfrom_array, sizeof(int)*nwords);
			cto_array = realloc(cto_array, sizeof(int)*nwords);
			cfrom_array[nwords-1] = c_from;
			cto_array[nwords-1] = c_to;
			free(wide_token);
		}
		p += b.rm_eo;
	}
	if(n_missing)
	{
		DEBUG("EXAMPLE <tr><td>%S</td><td>%S</td></tr>\n", orig_str, ts.string);
	}

	free(orig_str);
	free(ts.string);
	free(ts.align);

	if(Nwords)*Nwords = nwords;
	if(Words)*Words = words;
	else if(nwords) { for(i=0;i<nwords;i++)free(words[i]); free(words); }
	if(CFrom)*CFrom = cfrom_array;
	else free(cfrom_array);
	if(CTo)*CTo = cto_array;
	else free(cto_array);
	return 0;
}
