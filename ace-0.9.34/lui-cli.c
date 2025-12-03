#include	<stdio.h>
#include	<unistd.h>
#include	<stdlib.h>
#include	<string.h>
#include	<pthread.h>

#include	"conf.h"
#include	"chart.h"
#include	"dag.h"
#include	"rule.h"
#include	"lexicon.h"
#include	"mrs.h"
#include	"unpack.h"
#include	"lattice-mapping.h"
#include	"token.h"
#include	"hash.h"
#include	"dag-provenance.h"
#include	"linenoise.h"

void	lui_rule_completions(const char	*line, linenoiseCompletions	*lc)
{
	int	i;
	char	compl[10240] = ":r ";
	for(i=0;i<nrules;i++)if(!strncmp(line,rules[i]->name,strlen(line)))
	{
		strcpy(compl+3, rules[i]->name);
		linenoiseAddCompletion(lc,strdup(compl));
	}
}

void	lui_type_completions(const char	*line, char	*command, linenoiseCompletions	*lc)
{
	int	i;
	char	compl[10240];
	sprintf(compl, ":%s ", command);
	struct type_hierarchy	*th = default_type_hierarchy();
	for(i=0;i<th->ntypes;i++)if(!strncmp(line,th->types[i]->name,strlen(line)))
	{
		strcpy(compl+3, th->types[i]->name);
		linenoiseAddCompletion(lc,strdup(compl));
	}
}

void	lui_lex_completions(const char	*line, linenoiseCompletions	*lc)
{
	int	i;
	char	compl[10240] = ":l ";
	extern struct lexeme	**lexemes;
	for(i=0;i<nlexemes;i++)if(!strncmp(line,lexemes[i]->word,strlen(line)))
	{
		strcpy(compl+3, lexemes[i]->word);
		linenoiseAddCompletion(lc,strdup(compl));
	}
}

void	lui_instance_completions(const char	*line, linenoiseCompletions	*lc)
{
	int	i;
	char	compl[10240] = ":i ";
	for(i=0;i<ninstances;i++)if(!strncmp(line,instances[i].name,strlen(line)))
	{
		strcpy(compl+3, instances[i].name);
		linenoiseAddCompletion(lc,strdup(compl));
	}
}

extern struct lattice_rule_set	*token_mapping_rules;
extern struct lattice_rule_set	*lexical_filtering_rules;
extern struct lattice_rule_set	*post_generation_mapping_rules;

void	lui_break_completions1(char	*compl, char	*idea, char	*tok, linenoiseCompletions	*lc, struct lattice_rule_set	*rs)
{
	int	i;
	for(i=0;i<rs->nrules;i++)if(!strncmp(tok,rs->rules[i]->name,strlen(tok)))
	{
		strcpy(idea, rs->rules[i]->name);
		linenoiseAddCompletion(lc,strdup(compl));
	}
}

void	lui_break_completions(const char	*line, linenoiseCompletions	*lc)
{
	if(!strchr(line, ' '))
	{
		linenoiseAddCompletion(lc, strdup(":break "));
		return;
	}
	char	*tok = strrchr(line, ' ');
	if(!tok)return;
	tok++;
	char	compl[10240];
	memcpy(compl, line, tok-line);
	char	*idea = compl + (tok-line);
	lui_break_completions1(compl, idea, tok, lc, token_mapping_rules);
	lui_break_completions1(compl, idea, tok, lc, lexical_filtering_rules);
	lui_break_completions1(compl, idea, tok, lc, post_generation_mapping_rules);
	if(!strncmp(tok, "before", strlen(tok))){ sprintf(idea, "before"); linenoiseAddCompletion(lc, strdup(compl)); }
	if(!strncmp(tok, "after", strlen(tok))){ sprintf(idea, "after"); linenoiseAddCompletion(lc, strdup(compl)); }
	if(!strncmp(tok, "clear", strlen(tok))){ sprintf(idea, "clear"); linenoiseAddCompletion(lc, strdup(compl)); }
	if(!strncmp(tok, "all", strlen(tok))){ sprintf(idea, "all"); linenoiseAddCompletion(lc, strdup(compl)); }
}

void	lui_linenoise_completion(const char	*line, linenoiseCompletions	*lc)
{
	if(line[0] != ':')return;
	if(!line[1])
	{
		linenoiseAddCompletion(lc, ":r");
		linenoiseAddCompletion(lc, ":l");
		linenoiseAddCompletion(lc, ":i");
		linenoiseAddCompletion(lc, ":t");
		linenoiseAddCompletion(lc, ":h");
		linenoiseAddCompletion(lc, ":H");
		linenoiseAddCompletion(lc, ":g");
		linenoiseAddCompletion(lc, ":c");
		linenoiseAddCompletion(lc, ":break");
		if(g_mode == GENERATING)linenoiseAddCompletion(lc, ":trigger");
	}
	else if(line[1])switch(line[1])
	{
		case	'r':	lui_rule_completions(line+3, lc);	break;
		case	't':	lui_type_completions(line+3, "t", lc);	break;
		case	'h':	lui_type_completions(line+3, "h", lc);	break;
		case	'H':	lui_type_completions(line+3, "H", lc);	break;
		case	'i':	lui_instance_completions(line+3, lc);	break;
		case	'l':	lui_lex_completions(line+3, lc);	break;
		case	'b':	lui_break_completions(line, lc);	break;
	}
}
