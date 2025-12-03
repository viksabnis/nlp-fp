#ifndef	UNICODE_H
#define	UNICODE_H

char	*tombs(wchar_t	*w);
wchar_t	*towide(char	*mbs);
int	check_mbs(char	*mbs);
int	wide_is_number(const wchar_t	*str);
int	wstrlen(const wchar_t	*str);
wchar_t	*wstrcpy(wchar_t	*dest, const wchar_t	*src);
wchar_t	*wstrdup(const wchar_t	*in);
int	wstrcmp(const wchar_t	*a, const wchar_t	*b);
wchar_t	*wide_unescape(wchar_t	*str);

#endif
