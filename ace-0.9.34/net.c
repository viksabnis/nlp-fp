#include	<sys/types.h>
#include	<sys/socket.h>
#include	<unistd.h>
#include	<stdlib.h>
#include	<string.h>
#include	<stdio.h>
#define		BSD_COMP	1
#include	<sys/ioctl.h>
#include	<netinet/in.h>
#include	<arpa/inet.h>
#include	<netdb.h>
#include	"net.h"

#define	PORT	9977

int	saved_termerr = 2;

void	print_current_sentence(int	sig)
{
	extern	char	current_sentence[];

	int	r;
	
	char	*message = "ERROR: DEADLY SIGNAL! sent = `";
	r = write(saved_termerr, message, strlen(message));
	r = write(saved_termerr, current_sentence, strlen(current_sentence));
	r = write(saved_termerr, "'\n", 2);
	shutdown_net();
	exit(-1);
}

void	shutdown_net()
{
	if(saved_termerr == 2)return;
	close(1);
	shutdown(0, SHUT_RDWR);
	close(0);
	restore_stderr();
}

static int	conn(char	*hostname, int	port)
{
	int	s = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
	struct hostent	*he;
	unsigned int	ip;
	struct sockaddr_in	addr;

	if(s<0) { perror("socket"); exit(-1); }
	he = gethostbyname(hostname);
	if(!he) { perror("gethostbyname"); exit(-1); }

	ip = *(unsigned int*)he->h_addr;
	//printf("remote IP: %.8X\n", ntohl(ip));

	addr.sin_family = AF_INET;
	addr.sin_port = htons(port);
	addr.sin_addr.s_addr = ip;
	if(connect(s, (void*)&addr, sizeof(addr)))
		{ perror("connect"); exit(-1); }

	return s;
}

void	connect_to_master(char	*hostname)
{
	int	sout;

	char	*colon = strchr(hostname, ':');
	int	port = PORT;
	if(colon)
	{
		*colon = 0;
		port = atoi(colon+1);
	}
	sout = conn(hostname, port);
	//printf("connected.\n");

	saved_termerr = dup(2);
	close(0); close(1); close(2);
	dup2(sout, 0);
	dup2(sout, 1);
	dup2(sout, 2);
	close(sout);
}

void	restore_stderr()
{
	if(saved_termerr==2)return;
	close(2);
	dup2(saved_termerr, 2);
}
