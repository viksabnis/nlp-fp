#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<sys/fcntl.h>

#include	<dlfcn.h>

#include	"dag.h"
#include	"type.h"
#include	"qc.h"

extern int qc_size;
int		qc_image_size;
void	*qc_image;
int		*qc_scope;

struct qc_freezer
{
	int	qc_size, qc_image_size;
	int	*qc_scope;
	void	*qc_image;
};

void	*freeze_qc()
{
	struct qc_freezer	*f = slab_alloc(sizeof(*f));
	f->qc_size = qc_size;
	f->qc_image_size = qc_image_size;
	f->qc_image = slab_alloc(qc_image_size + 4 - (qc_image_size%4));
	memcpy(f->qc_image, qc_image, qc_image_size);
	f->qc_scope = slab_alloc(qc_size * sizeof(int));
	memcpy(f->qc_scope, qc_scope, qc_size * sizeof(int));
	return f;
}

void	recover_qc(void	*qcf)
{
	struct qc_freezer	*f = qcf;
	qc_size = f->qc_size;
	qc_image_size = f->qc_image_size;
	qc_image = f->qc_image;
	qc_scope = f->qc_scope;
}

int	qc_contains(int	outer, int	inner)
{
	int	i;
	if(inner >= outer && inner < qc_scope[outer])return 1;
	return 0;
}

void	qc_end_scopes(int	n, int	*qc_depth, int	depth)
{
	int i;
	for(i=0;i<n;i++)
		if(qc_scope[i] == 0 && qc_depth[i] > depth)
			qc_scope[i] = n;
}

int	compile_qc(char	*qccode_path)
{
	if(!qccode_path)
	{
		fprintf(stderr, "no quickcheck-code path configured!\n");
		exit(-1);
	}

	char	*tmpdir = getenv("TMPDIR")?:"/tmp";
	char	target_path[1280] = "/tmp/qcex.so-XXXXXX";
	sprintf(target_path, "%s/qcex.so-XXXXXX", tmpdir);
	int	fd = mkstemp(target_path);

	FILE	*qccode = fopen(qccode_path, "r");
	if(!qccode) { perror(qccode_path); exit(-1); }

	char	command[10240];
#ifdef	MACOSX_GCC
	sprintf(command, "gcc -x c -dynamic -dynamiclib -undefined suppress -flat_namespace -m64 -fPIC -DPIC - -o '%s'", target_path);
#else
	sprintf(command, "gcc -x c -shared -fPIC -DPIC - -o '%s'", target_path);
#endif
	FILE	*gcc = popen(command, "w");
	if(!gcc) { perror("popen"); exit(-1); }

	fprintf(gcc, "struct type; struct dg;\n");
	fprintf(gcc, "struct dg *noninline_dg_hop(struct dg*, int);\n");
	fprintf(gcc, "struct type *dg_type(struct dg*);\n");
	fprintf(gcc, "#define	NULL	((void*)0L)\n");
	fprintf(gcc, "void extractor(struct type	**entries, struct dg	*d)\n");
	fprintf(gcc, "{\n");
	fprintf(gcc, "	struct dg	*stack[64];\n");
	fprintf(gcc, "	int	sp = 0;\n");
	fprintf(gcc, "	stack[sp] = d;\n");

	char	line[10240];
	int		lnum = 0, *qc_depth, depth = 0;
	int		n_record = 0;
	//char	*last_push = "/";
	while(NULL != fgets(line, 10239, qccode))
	{
		lnum++;
		if(line[0]=='/' && line[1]=='*')continue;
		int	x;
		if(1==sscanf(line, "QC_SIZE(%d)\n", &x))
		{
			qc_size = x;
			qc_depth = calloc(sizeof(int),qc_size);
			qc_scope = calloc(sizeof(int),qc_size);
			continue;
		}
		char	*tok;
		char	feat[256];
		for(tok=strtok(line, " \t\n");tok;tok=strtok(NULL, " \t\n"))
		{
			if(!strcmp(tok, "POP"))
			{
				fprintf(gcc, "	--sp;\n");
				depth--;
				qc_end_scopes(n_record, qc_depth, depth);
			}
			else if(1 == sscanf(tok, "REC(%d)", &x))
			{
				if(x<0 || x>=qc_size)
				{
					fprintf(stderr, "QUICKCHECK: code indicates to record element %d, in vector of length %d (max index %d)\n", x, qc_size, qc_size-1);
					exit(-1);
				}
				fprintf(gcc, "	if(stack[sp]) entries[%d] = dg_type(stack[sp]);\n", x);
				fprintf(gcc, "	else entries[%d] = NULL;\n", x);
				qc_depth[n_record] = depth;
				n_record++;
				//struct type	*T = strcmp(last_push, "/")?most_general_type_for_feat(default_type_hierarchy(), lookup_fname(last_push)):lookup_type("sign");
				//fprintf(stderr, "QC[%d] feature=%s type=%s subtypes=%d\n", x, last_push, T->name, T->ndescendents);
			}
			else if(1 == sscanf(tok, "PUSH(%[^)])", feat))
			{
				int	l = lookup_fname(feat);
				fprintf(gcc, "	if(stack[sp++])stack[sp] = noninline_dg_hop(stack[sp-1], %d);\n", l);
				fprintf(gcc, "	else stack[sp] = NULL;");
				//last_push = strdup(feat);
				depth++;
			}
			else
			{
				fprintf(stderr, "QC-COMPILE: %s:%d: error! unknown directive '%s'\n", qccode_path, lnum, tok);
				exit(-1);
			}
		}
	}
	fclose(qccode);
	qc_end_scopes(n_record, qc_depth, -1);

	assert(n_record == qc_size);

	fprintf(gcc, "}\n");

	int res = pclose(gcc);
	if(res != 0) { perror("gcc"); exit(-1); }

	close(fd);
	fd = open(target_path, O_RDONLY);
	assert(fd > 0);
	off_t	len = lseek(fd, 0, SEEK_END);

	qc_image_size = len;
	qc_image = malloc(len);
	lseek(fd, 0, SEEK_SET);
	assert(read(fd, qc_image, len) == len);
	unlink(target_path);
	close(fd);

	return 0;
}

qc_extractor_function	dynamically_link_qc_extractor()
{
	//char	path[128] = "/tmp/qcex.so-XXXXXX";
	//int	fd = mkstemp(path);


	char	*tmpdir = getenv("TMPDIR")?:"/tmp";
	char	path[1280] = "/tmp/qcex.so-XXXXXX";
	sprintf(path, "%s/qcex.so-XXXXXX", tmpdir);
	int	fd = mkstemp(path);

	assert(qc_image_size = write(fd, qc_image, qc_image_size));
	void	*dl = dlopen(path, RTLD_NOW);
	if(!dl) { fprintf(stderr, "dlopen: %s\n", dlerror()); exit(-1); }
	void	*extr = dlsym(dl, "extractor");
	if(!extr) { fprintf(stderr, "extractor: %s\n", dlerror()); exit(-1); }
	unlink(path);
	close(fd);

	return extr;
}

/*
int lookup_fnum(char	*feat) { return 1; }

main(int	argc, char	*argv[])
{
	int res = compile_qc(argv[1]);
	printf("compiled '%s'; res = %d\n", argv[1], res);
	printf("%d qc nodes\n", qc_size);

	printf("qc image is %d bytes\n", qc_image_size);

	struct timeval	tv1, tv2;
	gettimeofday(&tv1, NULL);
	qc_extractor_function	ex = dynamically_link_qc_extractor(qc_image, qc_image_size);
	gettimeofday(&tv2, NULL);

	printf("ex = %p\n", ex);
	double	dt = tv2.tv_sec - tv1.tv_sec;
	dt += (double)(tv2.tv_usec - tv1.tv_usec) * 0.000001;
	printf("dynamic linking took %f seconds\n", dt);
}
*/
