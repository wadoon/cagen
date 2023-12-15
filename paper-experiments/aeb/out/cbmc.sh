#!/usr/bin/env sh

podman run -ti -v .:/local/:z -v /mnt/:$HOME/kissat/build/ diffblue/cbmc:5.50.0 \
      bash -c "time cbmc --unwind 256 --external-sat-solver /mnt/kissat /local/$1"
