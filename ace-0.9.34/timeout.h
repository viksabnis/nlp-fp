#ifndef TIMEOUT_H
#define TIMEOUT_H

extern int  timeout_seconds, cancel_task, did_timeout;
void    alarm_handler(int   sig);

#endif
