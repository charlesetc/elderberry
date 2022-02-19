#!/bin/bash
set -eou pipefail
mkdir -p target/elderberry
cargo run -- example/desk.elderberry | js-beautify > target/elderberry/desk.js
rsync -a runtime/ target/elderberry/runtime/
deno run target/elderberry/desk.js
