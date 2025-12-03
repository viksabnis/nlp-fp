PREFIX=/usr/local

# comment out these two lines if you don't want to include [incr tsdb()] support
DELPHIN_CFLAGS=-isystem ${LOGONROOT}/lingo/lkb/include -DTSDB
#DELPHIN_LIBS=-L ${LOGONROOT}/lingo/lkb/lib/linux.x86.64 -Wl,-Bstatic -litsdb -lpvm3 -Wl,-Bdynamic
DELPHIN_LIBS=-L ${LOGONROOT}/lingo/lkb/lib/linux.x86.64 -Wl,-Bdynamic -litsdb -lpvm3

POST_CFLAGS=-I post/ -DPOST
#POST_LIBS=-Wl,-Bstatic -lutil -Wl,-Bdynamic	# for openpty for calling out to tnt (which uses fully buffered stdio)
POST_LIBS=-Wl,-Bdynamic -lutil

#REPP_LIBS=-Wl,-Bstatic -lrepp -Wl,-Bdynamic
REPP_LIBS=-Wl,-Bdynamic -lrepp
#REPP_CFLAGS=-I ${REPP_DIR}/include/

#BOOST_REGEX_LIBS=-Wl,-Bstatic -lboost_regex -lstdc++ -Wl,-Bdynamic
BOOST_REGEX_LIBS=-Wl,-Bdynamic -lboost_regex -lstdc++

#CPU=-m32
CC=gcc
#CFLAGS=-g -O6 -fomit-frame-pointer -funsigned-char -falign-loops=32 -funroll-loops ${CPU} -fprofile-generate=./profile-data/
#REPP_LIBS+=-lgcov
#CFLAGS=-g -O6 -fomit-frame-pointer -funsigned-char -falign-loops=32 -funroll-loops ${CPU} -fprofile-use=./profile-data/

#CFLAGS=-g -O6 -fomit-frame-pointer -funsigned-char -falign-loops=32 -funroll-loops ${CPU}
CFLAGS=-g -O6 -fno-omit-frame-pointer -funsigned-char -falign-loops=32 -funroll-loops -fcommon ${CPU}
#CFLAGS=-g -O6 -funsigned-char -falign-loops=32 -funroll-loops ${CPU}  -pg
#CFLAGS=-g -O2 -funsigned-char
#CFLAGS=-g -O2 -pg -funsigned-char
#CFLAGS=-g -funsigned-char
#CFLAGS+=-fPIC

EXPORT_DYNAMIC_CFLAG=-Wl,--export-dynamic

#include MacOSX.config

CFLAGS+=${DELPHIN_CFLAGS} ${POST_CFLAGS} ${REPP_CFLAGS}

OBJ=lexicon.o chart.o dag.o type.o tdl.o rule.o morpho.o roots.o freeze.o unify.o qc.o agenda.o net.o glb.o semindex.o hash.o mrs.o mrsvpm.o mrsdg.o itsdb.o pack.o unpack.o maxent.o generate.o parse.o lui.o conf.o preprocessor.o treebank-control.o token.o lattice-mapping.o lexical-parse.o generalize.o transfer.o transfer-result.o edge-vectors.o forest-out.o exunpack.o semilattice.o rebuild-th.o compile-qc.o idiom.o yy.o lisp.o tnt.o tree.o reconstruct.o arbiter.o profiler.o qcparse.o rule-use-model.o ubertag.o dublin.o licenses.o dag-provenance.o semi.o timeout.o csaw/csaw.o csaw/naive.o csaw/normalize.o

PICOBJS=$(patsubst %,pic/%,${OBJ} libace.o)
HIDDENPICOBJS=pic/timer.o
APPOBJ=${OBJ} main.o post/post.o timer.o linenoise.o lui-cli.o

all: ace libace.so libace.a

ace: ${APPOBJ}
	${CC} ${LDFLAGS} ${EXPORT_DYNAMIC_CFLAG} ${CFLAGS} ${APPOBJ} -o ace ${POST_LIBS} ${REPP_LIBS} ${DELPHIN_LIBS} -lpthread -lm ${BOOST_REGEX_LIBS} -ldl

static: ${APPOBJ}
	${CC} -Wl,--dynamic-list=dylist.txt ${CFLAGS} ${APPOBJ} -Wl,-Bstatic -static ${POST_LIBS} ${REPP_LIBS} ${DELPHIN_LIBS} -static -lpthread -lm -L ~/local/lib/ -lboost_regex -lstdc++ -la -ldl -o ace.static

post/post.o:
	${MAKE} -C post

${PICOBJS} : pic/%.o: %.c
	mkdir -p pic pic/csaw
	${CC} ${CFLAGS} -fPIC -c $< -o $@

${HIDDENPICOBJS} : pic/%.o: %.c
	mkdir -p pic
	${CC} ${CFLAGS} -fvisibility=hidden -fPIC -c $< -o $@

libace.so: ${PICOBJS} ${HIDDENPICOBJS} post/post.o
	rm -f libace.so
	gcc -shared ${PICOBJS} ${HIDDENPICOBJS} post/post.o -Wl,-soname,libace.so -o libace.so -lrepp ${DELPHIN_LIBS} -ldl -lutil
# note: -lutil cannot be compiled statically into a shared library, because the bozos that built it didn't use -fPIC...

libace.a: ${PICOBJS} ${HIDDENPICOBJS} post/post.o
	rm -f libace.a
	ar cru libace.a ${PICOBJS} ${HIDDENPICOBJS} post/post.o
	ranlib libace.a

install: ace libace.so libace.a
	cp ace ${PREFIX}/bin/
	cp libace.so ${PREFIX}/lib/
	cp libace.a ${PREFIX}/lib/
	mkdir -p ${PREFIX}/include/ace
	cp *.h ${PREFIX}/include/ace/

clean:
	rm -f ${OBJ} ${APPOBJ} ace ace.static
	rm -f libace.a libace.so
	rm -f ${PICOBJS}
	make -C post clean
