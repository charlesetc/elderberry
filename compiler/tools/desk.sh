#!/bin/bash
set -e
mkdir -p target/elderberry
cargo run -- example/desk.berry | js-beautify > target/elderberry/desk.js
rsync -a runtime/ target/elderberry/runtime/
deno run target/elderberry/desk.js
