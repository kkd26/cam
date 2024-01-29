#!/bin/bash

staged=$(git diff --name-only --cached)

stagedAgdaFiles=$(find $staged -name "*.agda")

echo "$stagedAgdaFiles"
