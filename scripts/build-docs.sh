#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

package=cencov-petz
library=CencovPetz
toolchain=$(cat lean-toolchain)
version=${toolchain#*:}

mkdir -p docbuild
cp lean-toolchain docbuild/lean-toolchain
cat > docbuild/lakefile.toml <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "$package"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$version"
EOF

(
  cd docbuild
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update "$package"
  lake build "$library:docs"
)

mkdir -p public-docs/docs
cp -a docbuild/.lake/build/doc/. public-docs/docs/
