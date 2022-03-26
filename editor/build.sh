#!/bin/bash

cd ../compiler
./tools/compile.sh ../editor/main.elderberry
cd ../editor
rsync -a ../compiler/target/elderberry ./build/
