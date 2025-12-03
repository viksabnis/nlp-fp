AM_CFLAGS=-Wall -DVERSION=\"$(VERSION)\" -DPROG="\"$(PACKAGE)\"" -I$(top_srcdir)/include

#include_HEADERS = unicode.h
lib_LTLIBRARIES = librepp.la
librepp_la_SOURCES = load_repp.c preprocessor.c unicode.c
librepp_la_LIBADD = -lboost_regex
