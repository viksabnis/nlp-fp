#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.61)
AC_INIT([repp], [0.2.2], [sweaglesw@sweaglesw.org])
AM_INIT_AUTOMAKE([repp], [0.2.2])
AC_CONFIG_SRCDIR([librepp/load_repp.c])
#AC_CONFIG_HEADER([config.h])
AC_CONFIG_MACRO_DIR([m4])

# Checks for programs.
AC_PROG_CC
AC_PROG_LIBTOOL
#LT_PREREQ([2.2])
#LT_INIT([dlopen])

# Checks for libraries.
AC_CHECK_LIB([boost_regex], [regexecW], [], [
	echo "The Boost Regex library is required."
	exit -1])

# Checks for header files.
AC_HEADER_STDC
AC_CHECK_HEADERS([locale.h stdlib.h string.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS([bzero regcomp setlocale strchr strdup strrchr])

AC_TRY_COMPILE([],[int foo() { return 1; } return foo();],[],[
	OLD_CFLAGS=$CFLAGS
	CFLAGS="$OLD_CFLAGS -fnested-functions"
])

AC_CONFIG_FILES([Makefile
		include/Makefile
		librepp/Makefile
		repp/Makefile])
AC_OUTPUT
