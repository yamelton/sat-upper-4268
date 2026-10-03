#!/bin/sh
set -eu
sat_lean_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
sat_project_dir=$(dirname -- "$sat_lean_dir")
if [ -x "$sat_project_dir/.tools/elan/bin/lake" ]; then
  export ELAN_HOME="$sat_project_dir/.tools/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export MATHLIB_CACHE_DIR="$sat_project_dir/.tools/mathlib-cache"
cd "$sat_lean_dir"
exec lake "$@"
