#!/bin/bash

CORES=$1
shift

for (( i=1 ; $i<=$CORES ; i=$i+1)); do
	$* >/dev/null 2>/dev/null &
done

wait
