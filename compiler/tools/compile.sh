#!/bin/bash
set -eou pipefail
mkdir -p target/elderberry
target="target/elderberry/$(basename $1 .elderberry).js"
cargo run -- compile "$1" > "$target"
js-beautify -r "$target"
rsync -a runtime/ target/elderberry/runtime/
