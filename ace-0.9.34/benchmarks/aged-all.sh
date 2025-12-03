#!/bin/bash

echo -n "ace -R aged.txt    "
time {
	for x in 1 2 3 4 5 6 7 8 9 10 ; do
		echo -n $x ;
		./ace -g erg-1004.dat -R tests/aged.txt >/dev/null 2>/dev/null ;
	done
}
echo
