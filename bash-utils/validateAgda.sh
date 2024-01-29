#!/bin/bash

if [ $# -ne 1 ]; then
    files=$(find . -name "*.agda")
else
    files=$1
fi

for file in $files; do
    agda "$file" # --include-path=..

    if [ $? -ne 0 ]; then
       exit 1
    fi
done
