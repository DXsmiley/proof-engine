#!/bin/bash
set -eoux

# https://stackoverflow.com/a/17744637
cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")"

# https://stackoverflow.com/a/6245587
if [ "$(git rev-parse --abbrev-ref HEAD)" != "master" ]; then
    echo "Not on master branch"
    exit 1
fi

# https://unix.stackexchange.com/a/155077
if [ -n "$(git status --porcelain)" ]; then 
    echo "There are uncommitted changes in the repo"
    exit 1
fi

tempdir="$(mktemp)"
rm -rf -- "$tempdir"

elm make src/Main.elm --output="$tempdir/index.html"
git checkout gh-pages
mv "$tempdir/index.html" index.html
git add index.html
git commit -m "Publish from script"
git push
git checkout master
