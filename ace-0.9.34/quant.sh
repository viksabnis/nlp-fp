#!/bin/sh
nolex=`grep "No lex" $1 | wc -l`
yes=`grep "1 read" $1 | wc -l`
no=`grep "0 read" $1 | wc -l`
total=$(($yes+$no+$nolex))
tried=$(($yes+$no))
echo "considered   $total";
echo "attempted    $tried ($((100*$tried/$total))%)";
echo "parsed       $yes ($((100*$yes/$total))%)";
echo "no lexeme    $nolex ($((100*$nolex/$total))%)";
echo "grammar rate $((100*$yes/$tried))%";
