#!/bin/bash

dir=$(dirname $0)

agdaFiles=$($dir/getStaged.sh)

$dir/validateAgda.sh "$agdaFiles"
