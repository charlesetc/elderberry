#!/bin/bash
set -eou pipefail
mkdir -p target/elderberry
cargo run -- compile "example/$1.elderberry" > "target/elderberry/$1.js"
js-beautify -r "target/elderberry/$1.js"
rsync -a runtime/ target/elderberry/runtime/
deno run "target/elderberry/$1.js"