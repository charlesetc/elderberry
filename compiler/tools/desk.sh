#!/bin/bash
mkdir -p target/elderberry
cargo run -- example/desk.berry | js-beautify > target/elderberry/desk.js
