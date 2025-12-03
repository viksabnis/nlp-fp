CC=gcc
CFLAGS=-O3 -g -fPIC
#CFLAGS=-g
OBJS = train.o words.o tags.o hmm.o

#include ../MacOSX.config

# compilation flags:

CFLAGS += -DUSE_HMM
# uncomment the above line and recompile
# to enable bigram HMM tagging.

#CFLAGS += -DNO_MORPH_RULES
# uncomment the above line and recompile
# to disable rules for classifying unknown words.
# in this case, all unknown words will be tagged as NN.

post.o: ${OBJS}
	ld -r -o post.o ${OBJS}

clean:
	rm -f ${OBJS} post.o
