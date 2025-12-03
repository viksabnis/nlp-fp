#include	<stdio.h>
#include	<errno.h>
#include	<unistd.h>
#include	<string.h>
#include	<sys/fcntl.h>
#include	<stdarg.h>

#include	"chart.h"
#include	"net.h"
#include	"timer.h"

int		narbiterinputs;
char	**arbiterinputs;
char	**arbiter_job_ids;

char	*arbiter_partial_line;
int		arbiter_partial_line_length, arbiter_partial_line_length_a = 0;
int		arbiter_fd = 0;

extern int cancel_task, die, timeout_seconds, best_only;
extern int	max_chart_megabytes, max_unpack_megabytes;

int	arbiter_version = 0;
int	arbiter_processing = 0;
int	arbiter_granted_more_memory = 0;

void	arbiter_set_version(char	*res)
{
	if(1 != sscanf(res, ":v arbiter %d", &arbiter_version))
		assert(!"bad arbiter version; refusing to chat");
}

int	arbiter_request_memory()//char	*purpose)
{
	extern char	*master_addr;
	if(!master_addr || !strcmp(master_addr, "-"))return 0;	// if no arbiter, always decline additional memory
	char	*purpose = "for work";
	arbiter_granted_more_memory = 0;
	read_from_arbiter();
	if(arbiter_granted_more_memory)return 1;
	if(cancel_task)return 0;

	printf(":m chartlimit=%d unpackinglimit=%d %s\n", max_chart_megabytes, max_unpack_megabytes, purpose);
	fflush(stdout);

	while(!cancel_task && !arbiter_granted_more_memory)
	{
		usleep(100000);
		read_from_arbiter();
	}
	if(arbiter_granted_more_memory)return 1; // arbiter allocated us more RAM. how nice. :-)
	if(cancel_task)return 0;
}

void	arbiter_status(char	*format, ...)
{
	va_list	v;
	va_start(v, format);
	printf(":s ");
	vprintf(format, v);
	printf("\n");
	fflush(stdout);
	va_end(v);
}

void	arbiter_enqueue(char	*id, char	*input)
{
	narbiterinputs++;
	arbiterinputs = realloc(arbiterinputs, sizeof(char*)*narbiterinputs);
	arbiterinputs[narbiterinputs-1] = input;
	arbiter_job_ids = realloc(arbiter_job_ids, sizeof(char*)*narbiterinputs);
	arbiter_job_ids[narbiterinputs-1] = id;
	arbiter_status("queuelen=%d", narbiterinputs);
}

void	arbiter_ram(char	*mem)
{
	int	forest, unpack;
	if(2 == sscanf(mem, ":r %d %d", &forest, &unpack))
	{
		if(max_chart_megabytes < forest || max_unpack_megabytes < unpack)
			arbiter_granted_more_memory = 1;
		max_chart_megabytes = forest;
		max_unpack_megabytes = unpack;
	}
	arbiter_status("chartlimit=%d unpackinglimit=%d", max_chart_megabytes, max_unpack_megabytes);
}

void	arbiter_time(char	*res)
{
	int	max;
	if(1 == sscanf(res, ":t %d", &max))
		timeout_seconds = max;
	arbiter_status("timelimit=%d", timeout_seconds);
}

void	arbiter_count(char	*res)
{
	int	max;
	if(1 == sscanf(res, ":n %d", &max))
		best_only = max;
	arbiter_status("resultlimit=%d", best_only);
}

char	*current_arbiter_job_id = NULL;

void	arbiter_cancel(char	*res)
{
	if(current_arbiter_job_id)
	{
		extern int cancel_task;
		cancel_task = 1;
		arbiter_status("cancelling %s", current_arbiter_job_id);
	}
	else arbiter_status("no job to cancel");
}

void	arbiter_process(int	len)
{
	arbiter_partial_line[len] = 0;
	if(arbiter_partial_line[0] != ':')
	{
		arbiter_status("missing colon");
		return;
	}

	//arbiter_status("got '%s'", arbiter_partial_line);

	// starts with a ':' -- a special command
	switch(arbiter_partial_line[1])
	{
		case	'j':
			{ assert(arbiter_partial_line[2]==' '); char	*sp = strchr(arbiter_partial_line+3, ' ');
				if(!sp) { arbiter_status("no job id"); return; }
				*sp = 0;
				arbiter_enqueue(strdup(arbiter_partial_line+3), strdup(sp+1));
				break; }
		case	'r':	arbiter_ram(arbiter_partial_line);		break;
		case	't':	arbiter_time(arbiter_partial_line);		break;
		case	'n':	arbiter_count(arbiter_partial_line);	break;
		case	'c':	arbiter_cancel(arbiter_partial_line);	break;
		case	'v':	arbiter_set_version(arbiter_partial_line);	break;
		default:	arbiter_status("unknown command '%c'", arbiter_partial_line[1]);	break;
	}
}

read_from_arbiter()
{
	int	expect_more = 1;
	while(1)
	{
		char	buffer[1024];
		if(!narbiterinputs && !arbiter_processing)make_blocking(arbiter_fd);
		else make_nonblocking(arbiter_fd);
		int		r = read(arbiter_fd, buffer, 1023);
		if(r == 0) { cancel_task = die = 1; break; }
		if(r < 0)
		{
			if(errno == EAGAIN)break;	// would have blocked
			restore_stderr();
			perror("read");
			cancel_task = die = 1;
			break;
		}
		make_blocking(arbiter_fd);	// be sure to leave the socket in blocking mode, so that printf()'s etc don't have partial sends
		if(arbiter_partial_line_length + r > arbiter_partial_line_length_a)
		{
			arbiter_partial_line_length_a = 1 + 2 * (arbiter_partial_line_length + r);
			arbiter_partial_line = realloc(arbiter_partial_line, arbiter_partial_line_length_a);
		}
		memcpy(arbiter_partial_line + arbiter_partial_line_length, buffer, r);
		arbiter_partial_line_length += r;
		int i;
		for(i=arbiter_partial_line_length-r;i<arbiter_partial_line_length;i++)
			if(arbiter_partial_line[i]=='\n')
			{
				arbiter_process(i);
				arbiter_partial_line_length -= i+1;
				memmove(arbiter_partial_line, arbiter_partial_line+i+1, arbiter_partial_line_length);
				i -= i+1;
			}
	}
	make_blocking(arbiter_fd);	// be sure to leave the socket in blocking mode, so printf()'s etc don't have partial sends
}

char	*arbiter_next_input()
{
	read_from_arbiter();
	if(narbiterinputs)
	{
		char	*input = arbiterinputs[0];
		current_arbiter_job_id = arbiter_job_ids[0];
		--narbiterinputs;
		memmove(arbiterinputs, arbiterinputs+1, sizeof(char*)*narbiterinputs);
		memmove(arbiter_job_ids, arbiter_job_ids+1, sizeof(char*)*narbiterinputs);
		return input;
	}
	return NULL;
}
