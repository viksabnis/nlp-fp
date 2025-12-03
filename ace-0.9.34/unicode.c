#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<assert.h>
#include	<wchar.h>

#include	"unicode.h"

char	*tombs(wchar_t	*w)
{
	char	*str = malloc(4*(wcslen(w)+1));
	if(-1 == wcstombs(str, w, 1+4*wcslen(w)))
	{
		perror("multibyte encoding failed");
		fprintf(stderr, "on wcs `%S'\n", w);
		exit(-1);
	}
	return str;
}

int	check_mbs(char	*mbs)
{
	int		len = strlen(mbs);
	wchar_t	*wide = malloc(sizeof(wchar_t)*(len+1));
	if(-1 == mbstowcs(wide, mbs, len+1))
	{
		free(wide);
		return -1;
	}
	else
	{
		free(wide);
		return 0;
	}
}

wchar_t	*towide(char	*mbs)
{
	int		len = strlen(mbs);
	wchar_t	*wide = malloc(sizeof(wchar_t)*(len+1));
	if(-1 == mbstowcs(wide, mbs, len+1))
	{
		perror("multibyte decoding failed");
		fprintf(stderr, "on string `%s'\n", mbs);
		exit(-1);
	}
	return wide;
}

int	wide_is_number(const wchar_t	*str)
{
	while(*str)
		if(!isdigit(*str++))return 0;
	return 1;
}

int	wstrlen(const wchar_t	*str)
{
	int	l = 0;
	while(*str++)l++;
	return l;
}

wchar_t	*wstrcpy(wchar_t	*dest, const wchar_t	*src)
{
	wchar_t	*odest = dest;
	while(*src)
		*dest++ = *src++;
	*dest = 0;
	return odest;
}

wchar_t	*wstrdup(const wchar_t	*in)
{
	int	l = wstrlen(in);
	wchar_t	*out = malloc(sizeof(wchar_t)*(l+1));
	memcpy(out, in, sizeof(wchar_t)*l);
	out[l] = 0;
	return out;
}

int	wstrcmp(const wchar_t	*a, const wchar_t	*b)
{
	while(*a && *b)
	{
		if(*a != *b)return (*a) - (*b);
		a++;
		b++;
	}
	if(*a)return 1;
	if(*b)return -1;
	return 0;
}

wchar_t	*wide_unescape(wchar_t	*str)
{
	wchar_t	*out = wstrdup(str), *p = out, *q = str;

	while(*q)
	{
		if(*q=='\\' && q[1])
		{
			q+=2;
			switch(q[-1])
			{
				case	't':	*p++ = '\t';	break;
				case	'n':	*p++ = '\n';	break;
				case	'r':	*p++ = '\r';	break;
				case	'0':	*p++ = '\0';	break;
				default:
					// preserve escapes we don't understand
					*p++ = '\\';
					*p++ = q[-1];
					break;
			}
		}
		else *p++ = *q++;
	}
	*p = 0;
	return out;
}
