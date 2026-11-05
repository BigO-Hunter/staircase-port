#!/bin/sh
export LEAN_TOOLCHAIN=leanprover/lean4:v4.34.1
cd "$HOME/bigo-campaign/sp-n6" || exit 1
lake build StaircasePort > .build_full.log 2>&1
echo "EXIT=$?" >> .build_full.log
