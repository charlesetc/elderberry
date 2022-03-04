#!/bin/bash
set -eou pipefail
mkdir -p target/elderberry
cargo run -- typecheck "example/$1.elderberry"
