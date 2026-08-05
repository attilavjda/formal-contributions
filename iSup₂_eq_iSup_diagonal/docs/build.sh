#!/bin/sh
# Build the visual companion.  Uses tectonic if available, latexmk otherwise.
set -e
cd "$(dirname "$0")"
if command -v tectonic >/dev/null 2>&1; then
  tectonic proof-visualisations.tex
elif command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf proof-visualisations.tex
else
  pdflatex proof-visualisations.tex && pdflatex proof-visualisations.tex
fi
