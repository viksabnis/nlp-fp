#include	<stdio.h>

#include	"chart.h"
#include	"timeout.h"

int cancel_task;
int did_timeout;

void    alarm_handler(int   sig)
{
    fprintf(stderr, "NOTE: cancelling %s, taking too long\n",
        g_mode==PARSING?"parsing":(g_mode==TRANSFER?"transfer":"generation")
    );
    itsdb_error("timeout");
    cancel_task = 1;
    did_timeout = 1;
}
