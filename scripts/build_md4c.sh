#!/usr/bin/env bash
# Builds md4c's md2html, the differential-testing oracle for the LaTeX math extension
# (scripts/diff_md4c.sh). Clones and builds under build/, which is gitignored; nothing here
# reaches the dependency graph a consumer of this library resolves.
#
# Pinned rather than tracking master: the whole point of an oracle is that its answers don't
# move underneath the recorded ones.
set -euo pipefail

MD4C_TAG=release-0.5.3

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dir="$root/build/md4c"
bin="$root/build/md2html"

if [ -x "$bin" ] && [ "$(cat "$root/build/.md4c-tag" 2>/dev/null || true)" = "$MD4C_TAG" ]; then
  echo "md2html already built at $MD4C_TAG" >&2
  exit 0
fi

command -v cmake >/dev/null || {
  echo "cmake not found: it is installed by .devcontainer/Dockerfile and the CI workflow." >&2
  exit 1
}

rm -rf "$dir" "$bin"
mkdir -p "$root/build"
git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$MD4C_TAG" https://github.com/mity/md4c.git "$dir"
cmake -S "$dir" -B "$dir/_build" -DCMAKE_BUILD_TYPE=Release >/dev/null
cmake --build "$dir/_build" --target md2html >/dev/null
cp "$dir/_build/md2html/md2html" "$bin"
printf '%s' "$MD4C_TAG" > "$root/build/.md4c-tag"
echo "built md2html $("$bin" --version) at $MD4C_TAG" >&2
