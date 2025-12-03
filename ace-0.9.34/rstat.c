#include	<stdio.h>

main()
{
	int	nrules=0;
	int	nleft[1000], nright[1000];
	FILE	*fl, *fr;
	int	totall=0, save=0;
	int	numl, numr, idxl, idxr;
	char	rulel[1024], ruler[1024];
	char	rname[1000][100];

	fl = fopen("/tmp/rules-ltr", "r");
	if(!fl) { perror("/tmp/rules-ltr"); return -1; }
	fr = fopen("/tmp/rules-rtl", "r");
	if(!fr) { perror("/tmp/rules-rtl"); return -1; }

	while(!feof(fl) && !feof(fr))
	{
		if(fscanf(fl, "%d %d %s\n", &numl, &idxl, rulel) != 3)break;
		if(fscanf(fr, "%d %d %s\n", &numr, &idxr, ruler) != 3)break;
		if(strcmp(rulel, ruler) || idxl!=idxr || idxl!=nrules)
		{
			fprintf(stderr, "format error: left rule %d=%s, right rule %d=%s, idx %d\n",
					idxl, rulel, idxr, ruler, nrules);
			return -1;
		}
		nleft[nrules] = numl;
		nright[nrules] = numr;
		strcpy(rname[nrules], rulel);
		nrules++;
	}

	for(idxl=0;idxl<nrules;idxl++)
	{
		totall += nleft[idxl];
		if(nleft[idxl] == nright[idxl])continue;
		if(nleft[idxl] < nright[idxl])
		{
			printf("l %4d %s\n", nright[idxl] - nleft[idxl], rname[idxl]);
		}
		else
		{
			printf("r %4d %s\n", nleft[idxl] - nright[idxl], rname[idxl]);
			save += nleft[idxl] - nright[idxl];
		}
	}
	printf("; LTR: %d, BiDi: %d  (save %d = %.2f%%)\n", totall, totall - save, save, 100*(float)save/totall);
}
