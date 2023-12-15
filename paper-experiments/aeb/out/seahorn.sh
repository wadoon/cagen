#!/usr/bin/env sh


echo $1 >> seahorn.time.txt

# segfaulted with --bv-chc
podman run -ti --rm -v .:/local/:rw seahorn/seahorn-llvm10:nightly \
	bash -c "(time sea pf -DSEAHORN  --crab --show-invars /local/$1) 2> /local/seahorn.time.txt"
