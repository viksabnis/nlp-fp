#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<limits.h>
#include	<wchar.h>
#include	<ctype.h>
#include	<sys/fcntl.h>
#include	<errno.h>
#include	<unistd.h>
#include	<assert.h>
#include	<signal.h>
#include	<termios.h>

#include	"tree.h"

extern int debug_level;

char	*csaw_grammar_path = NULL;
static int	csaw_pid = -1;
static int	csaw_fd;

void	become_csaw(char	*grammar_path, char	*csaw_grammar_path, int	slave_fd)
{
	int	real_stderr = dup(2);
	login_tty(slave_fd);

	dup2(real_stderr, 2); if(real_stderr != 2)close(real_stderr);

//	int stderr_fd = open("/dev/null", O_WRONLY);
//	if(stderr_fd == -1)perror("/dev/null");
//	else if(stderr_fd != 2) { dup2(stderr_fd, 2); close(stderr_fd); }

	printf("%%%% exec csaw\n");
	fflush(stdout);
	execlp("/home/sweaglesw/cdev/csaw/csaw", "csaw", grammar_path, csaw_grammar_path, NULL);
	printf("%%%% exec failed: %s\n", strerror(errno));
	fflush(stdout);
	exit(-1);
}

char	*csaw_read(int	blocking)
{
#define	MAXLEN	102400
	static char	chunk[MAXLEN+1];
	static int savelen = 0;

	if(strchr(chunk, '\n'))
		goto already;

	chunk[MAXLEN] = 0;
	if(blocking)make_blocking(csaw_fd);
	else make_nonblocking(csaw_fd);
	while(savelen < MAXLEN)
	{
		int r = read(csaw_fd, chunk+savelen, MAXLEN-savelen);
		if(r<0 && errno == EAGAIN && !blocking)return NULL;
		if(r<=0) { perror("read from CSAW"); csaw_kill(); exit(-1); }
		//else printf("read %d bytes from csaw: %.*s\n", r, r, chunk+savelen);
		savelen += r;
		chunk[savelen] = 0;
		already:;
		char	*nl = strchr(chunk, '\n');
		if(nl)
		{
			*nl = 0;
			char	*line = strdup(chunk);
			savelen = strlen(nl+1);
			memmove(chunk, nl+1, savelen);
			chunk[savelen] = 0;
			return line;
		}
	}
	fprintf(stderr, "unexpectedly long line in result from CSAW\n");
	csaw_kill();
	exit(-1);
}

int	csaw_init(char	*grammar_path, char	*csaw_grammar_path)
{
	if(csaw_pid != -1)return 0;
	int	master_fd, slave_fd;
	int	res = openpty(&master_fd, &slave_fd, NULL, NULL, NULL);
	struct termios	tc;
	tcgetattr(master_fd, &tc);
	cfmakeraw(&tc);
	tcsetattr(master_fd, TCSANOW, &tc);
	fflush(stdout);fflush(stderr);
	int	pid = fork();
	if(pid == -1){ perror("fork"); return -1; }
	if(pid == 0)become_csaw(grammar_path, csaw_grammar_path, slave_fd);
	csaw_fd = master_fd;

	csaw_pid = pid;
	char	*line = csaw_read(1);
	int i;
	if(strcmp(line, "%% exec csaw"))
	{
		fprintf(stderr, "unexpected error while trying to start CSAW subprocess\n");
		fprintf(stderr, "unexpected reply: %s\n", line);
		free(line);
		csaw_kill();
		return -1;
	}
	free(line);
	line = csaw_read(0);
	if(line && !strncmp(line, "%% exec failed: ", 16))
	{
		fprintf(stderr, "unexpected error while trying to start CSAW subprocess: %s\n", line+16);
		free(line);
		csaw_kill();
		return -1;
	}
	if(line)free(line);
	if(debug_level)fprintf(stderr, "CSAW subprocess started successfully with PID %d\n", csaw_pid);
	return 0;
}

int	csaw_kill()
{
	if(csaw_pid == -1)return -1;
	kill(csaw_pid, SIGKILL);
	int status;
	int res = waitpid(csaw_pid, &status, 0);
	if(res == -1) { perror("unable to wait for CSAW process to exit"); exit(-1); }
	return 0;
}

struct tree	*csaw_parse(char	*sentence)
{
	assert(csaw_pid != -1);
	int i;

	//printf("ASKING csaw to parse: `%s'\n", sentence);
	int	len = strlen(sentence);
	int	res = write(csaw_fd, sentence, len);
	if(res!=len) { perror("write to CSAW"); exit(-1); }
	res = write(csaw_fd, "\n", 1);	// end-of-line signals end-of-sentence
	if(res <= 0) { perror("write to CSAW"); exit(-1); }
	assert(res == 1);

	// receive the parses
	char	*line = NULL;
	int	ready = 0;
	while(1)
	{
		do { if(line)free(line); line = csaw_read(1); } while(line[0] == '%' && line[1] == '%');
		//printf("RECEIVED csaw response: `%s'\n", line);
		if(!strncmp(line, "SKIP:",5))
		{
			free(line);
			return NULL;
		}
		if(!*line || line[0]=='\n')continue;
		if(!strncmp(line, "SENT:",5))ready=1;
		else if(!ready)continue;
		char	*divider = strstr(line, " ; ");
		if(!divider)continue;
		char	*treestr = divider + 3;
		struct tree	*tree = string_to_tree(treestr);
		free(line);
		//printf("THAT was a tree %p\n", tree);
		return tree;
	}
}
