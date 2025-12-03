#include	<stdlib.h>
#include	<stdio.h>
#include	<string.h>
#include	<signal.h>
#include	<time.h>

#include	"chart.h"
#include	"rule.h"
#include	"lexicon.h"

extern unsigned int qc_size;

void	output_edge_vector(FILE	*evf, struct edge	*e)
{
	if(!e->rule)return;
	int	useful = e->unpack ? 1 : 0;
	int	i;
	fprintf(evf, "%d", useful);
	for(i=0;i<qc_size;i++)
	{
		struct type	*t = e->qc?qc_type_n(e->qc, i):NULL;
		fprintf(evf, " qc%d=%s", i+1, t?t->name:"NULL");
	}
	fprintf(evf, " sl=%d", chart_size);
	fprintf(evf, " span=%d", e->to-e->from);
	fprintf(evf, " left=%d", e->from);
	fprintf(evf, " right=%d", chart_size-e->to);
	fprintf(evf, " rule=%s", e->rule->name);
	for(i=0;i<e->have;i++)
	{
		struct edge	*d = e->daughters[i];
		fprintf(evf, " dtr%d=%s", i+1, d->rule?d->rule->name:d->lex->word);
	}
	fprintf(evf, "\n");
}

void	do_output_edge_vectors()
{
	int	i, j;
	FILE	*evf = fopen("edge-vectors.txt", "a");
	if(!evf) { perror("edge-vectors.txt"); return; }
	for(i=0;i<chart_size*chart_size;i++)
		for(j=0;j<cells[i].p_nedges;j++)
			output_edge_vector(evf, cells[i].p_edges[j]);
	fclose(evf);
}
