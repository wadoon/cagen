#!/usr/bin/env sh


# segfaulted with --bv-chc
podman run -ti -v .:/local/:z seahorn/seahorn-llvm10:nightly \
      bash -c "time sea pf -DSEAHORN  --crab --show-invars /local/$1"
