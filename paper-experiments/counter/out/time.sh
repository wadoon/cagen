#!/usr/bin/env sh

/usr/bin/time -o 'time.txt' -a -f "%e,%S,%U,%P,\"$@\"" $@