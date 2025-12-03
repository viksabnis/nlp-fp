#define	UNICODE
#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<locale.h>
#include	<assert.h>
#include	<getopt.h>

#include	<librepp.h>

void	output_yy(int	nwords, char	**words, int	*cfrom, int	*cto)
{
	int i;
	char	*escape(char	*w)
	{
		static char	ebuff[10240];
		char	*p = ebuff;
		while(*w)
		{
			if(*w == '\\' || *w=='"')
				*p++='\\';
			*p++ = *w++;
		}
		*p = 0;
		return ebuff;
	}
	for(i=0;i<nwords;i++)
	{
		if(i)printf(" ");
		printf("(%d, %d, %d, <%d:%d>, 1, \"%s\", 0, \"null\")",
			i, i, i+1, cfrom[i], cto[i], escape(words[i]));
	}
	printf("\n");
}

void	usage(int	eval)
{
	fprintf(eval?stderr:stdout, "usage: %s main.rpp [-m some_module.rpp]\n", PACKAGE);
	exit(eval);
}

int	main(int	argc, char	*argv[])
{
	setlocale(LC_ALL, "");

	if(argc<2)usage(-1);
	if(!strcmp(argv[1], "-v") || !strcmp(argv[1], "--version"))
	{
		printf("%s %s\n", PACKAGE, VERSION);
		exit(0);
	}
	if(!strcmp(argv[1], "-h") || !strcmp(argv[1], "--help"))
	{
		usage(0);
	}

	struct preprocessor	*repp = repp_load(argv[1]);
	int			yy_output = 0, ch;

	optind = 2;
	while( (ch = getopt(argc, argv, "m:y")) != -1) switch(ch)
	{
		case	'm':
			repp_load_module(repp, optarg, NULL, 1);
			break;
		case	'y':
			yy_output = 1;
			break;
		default:
			usage(-1);
			break;
	}
	repp_compile_rules(repp);

	int	maxlen = 1024*10;
	char	*buffer = malloc(maxlen+1);
	FILE	*in_file = stdin;

	while(fgets(buffer, maxlen, in_file))
	{
		// trim the \n off buffer
		if(*buffer && buffer[strlen(buffer)-1]=='\n')
			buffer[strlen(buffer)-1] = 0;
		// preprocess the line of input
		int	i, nwords, *cfrom, *cto;
		char	**words;
		if(0 != repp_preprocess(repp, buffer, &nwords, &words, &cfrom, &cto))
		{
			fprintf(stderr, "unable to process line '%s'\n", buffer);
			continue;
		}
		// output the preprocessing result
		if(yy_output)
			output_yy(nwords, words, cfrom, cto);
		else for(i=0;i<nwords;i++)printf("%s%c", words[i], (i==nwords-1)?'\n':' ');
		//else for(i=0;i<nwords;i++)printf("word %d = %s [%d-%d]\n", i, words[i], cfrom[i], cto[i]);
	}
	return 0;
}
