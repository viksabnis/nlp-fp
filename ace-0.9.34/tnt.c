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

#include	"dag.h"
#include	"tnt.h"
#include	"freeze.h"

extern int debug_level;

static int	tnt_max_tags = 1;
static int	tnt_pid = -1;
static int	tnt_fd;

void	become_tnt(char	*model, int	slave_fd)
{
	int	real_stderr = dup(2);
	login_tty(slave_fd);

	dup2(real_stderr, 2); if(real_stderr != 2)close(real_stderr);

//	int stderr_fd = open("/dev/null", O_WRONLY);
//	if(stderr_fd == -1)perror("/dev/null");
//	else if(stderr_fd != 2) { dup2(stderr_fd, 2); close(stderr_fd); }

	printf("%%%% exec tnt\n");
	fflush(stdout);
	execlp("tnt", "tnt", "-z100", "-v0", model, "-", NULL);
	printf("%%%% exec failed: %s\n", strerror(errno));
	fflush(stdout);
	exit(-1);
}

void	make_blocking(int	fd)
{
	int	opt = fcntl(fd, F_GETFL);
	fcntl(fd, F_SETFL, opt & ~O_NONBLOCK);
}

void	make_nonblocking(int	fd)
{
	int	opt = fcntl(fd, F_GETFL);
	fcntl(fd, F_SETFL, opt | O_NONBLOCK);
}

char	*tnt_read(int	blocking)
{
	static char	chunk[1024];
	static int savelen = 0;

	if(strchr(chunk, '\n'))
		goto already;

	chunk[1023] = 0;
	if(blocking)make_blocking(tnt_fd);
	else make_nonblocking(tnt_fd);
	while(savelen < 1023)
	{
		int r = read(tnt_fd, chunk+savelen, 1023-savelen);
		if(r<0 && errno == EAGAIN && !blocking)return NULL;
		if(r<=0) { perror("read from TNT"); tnt_kill(); exit(-1); }
		//else printf("read %d bytes from tnt: %.*s\n", r, r, chunk+savelen);
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
	fprintf(stderr, "unexpectedly long line in result from TNT\n");
	tnt_kill();
	exit(-1);
}

int	tnt_init(char	*model, int	maxtags)
{
	if(tnt_pid != -1)return 0;
	int	master_fd, slave_fd;
	int	res = openpty(&master_fd, &slave_fd, NULL, NULL, NULL);
	struct termios	tc;
	tcgetattr(master_fd, &tc);
	cfmakeraw(&tc);
	tcsetattr(master_fd, TCSANOW, &tc);
	int	pid = fork();
	if(pid == -1){ perror("fork"); return -1; }
	if(pid == 0)become_tnt(model, slave_fd);
	tnt_fd = master_fd;

	tnt_pid = pid;
	char	*line = tnt_read(1);
	int i;
	if(strcmp(line, "%% exec tnt"))
	{
		fprintf(stderr, "unexpected error while trying to start TNT subprocess\n");
		fprintf(stderr, "unexpected reply: %s\n", line);
		free(line);
		tnt_kill();
		return -1;
	}
	free(line);
	line = tnt_read(0);
	if(line && !strncmp(line, "%% exec failed: ", 16))
	{
		fprintf(stderr, "unexpected error while trying to start TNT subprocess: %s\n", line+16);
		free(line);
		tnt_kill();
		return -1;
	}
	if(line)free(line);
	tnt_max_tags = maxtags;
	if(debug_level)fprintf(stderr, "TNT subprocess started successfully with PID %d\n", tnt_pid);
	return 0;
}

int	tnt_kill()
{
	if(tnt_pid == -1)return -1;
	kill(tnt_pid, SIGKILL);
	int status;
	int res = waitpid(tnt_pid, &status, 0);
	if(res == -1) { perror("unable to wait for TNT process to exit"); exit(-1); }
	return 0;
}

int	tnt_tag_sequence(int	nwords, char	**words, struct tnt_result	*results)
{
	assert(tnt_pid != -1);
	int i, res;

	// send the tokens
	for(i=-1;i<=nwords;i++)
	{
		char	*w = (i==-1 || i==nwords)?".":words[i];
		int	wl = strlen(w);
		if(wl > 500) { fprintf(stderr, "ACE TNT bridge can't handle exceptionally long words; truncating\n"); wl = 500; }
		res = write(tnt_fd, w, wl);
		if(res <= 0) { perror("write to TNT"); exit(-1); }
		assert(res == wl);
		res = write(tnt_fd, "\n", 1);
		if(res <= 0) { perror("write to TNT"); exit(-1); }
		assert(res == 1);
	}
	res = write(tnt_fd, "\n", 1);	// blank line signals end-of-sentence
	if(res <= 0) { perror("write to TNT"); exit(-1); }
	assert(res == 1);

	// recieve the tags
	char	*line = NULL;
	for(i=-1;i<=nwords;i++)
	{
		do { if(line)free(line); line = tnt_read(1); } while(line[0] == '%' && line[1] == '%');
		if(i==-1 || i==nwords)continue;
		struct tnt_result	*res = &results[i];
		res->ntags = 0;
		res->tags = NULL;
		char	*p, *q;
		int	k = -1;
		char	*tag;
		for(p=strtok_r(line, "\t", &q);p && res->ntags < tnt_max_tags;p=strtok_r(NULL, "\t", &q), k++)
		{
			if(k==-1)continue;
			if(k%2 == 0)tag = p;
			else
			{
				res->ntags++;
				res->tags = slab_realloc(res->tags, sizeof(struct tag_option)*(res->ntags-1), sizeof(struct tag_option)*res->ntags);
				struct tag_option	*opt = res->tags + res->ntags-1;
				opt->tag = freeze_string(tag);
				opt->prob = atof(p);
				//printf("word %s tag %s prob %f\n", words[i], opt->tag, opt->prob);
			}
		}
	}
	do { if(line)free(line); line = tnt_read(1); } while(line[0] == '%' && line[1] == '%');
	assert(strlen(line) == 0);
	free(line);
	return 0;
}
