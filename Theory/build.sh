#!/bin/sh

# Build each .tex file in parallel.
for f in *.tex
do
  latexmk -pdf -interaction=nonstopmode -synctex=1 "$f" &
done

# For each parallel job, wait for it and if it errors, pass
# the error status forward.
for job in $(jobs -p)
do
  wait $job || exit 1
done