#!/usr/bin/env bash
# build_paper.sh -- build the paper and its submission files into dist/.
#
#   dist/gp-parity-conjecture.pdf           the compiled paper
#   dist/gp-parity-conjecture-tex.zip       main.tex with the figure as PNG (and its TikZ source)
#   dist/gp-parity-conjecture-arxiv.tar.gz  main.tex and the figure as PDF, ready for arXiv
#
# Needs pdflatex with amsart, tikz and hyperref; pdftoppm (poppler) for the PNG figure;
# zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/preprintGPParity"
DIST="$ROOT/dist"
NAME=gp-parity-conjecture
FIGS="gp7"
mkdir -p "$DIST"

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

echo "== figures"
cd "$PAPER/figures"
for f in $FIGS; do
  latex "$f.tex"
  pdftoppm -png -r 200 -singlefile "$f.pdf" "$f"
  rm -f "$f.aux" "$f.log"
done

echo "== paper"
cd "$PAPER"
latex main.tex
latex main.tex
if grep -q "Overfull\|undefined" main.log; then
  grep "Overfull\|undefined" main.log
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi
cp main.pdf "$DIST/$NAME.pdf"

echo "== tex.zip (figure as PNG)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
mkdir -p "$STAGE/$NAME/figures"
sed 's#\\includegraphics\(\[[^]]*\]\)\?{figures/\([a-z0-9]*\)}#\\includegraphics\1{figures/\2.png}#' \
  main.tex > "$STAGE/$NAME/main.tex"
for f in $FIGS; do cp "figures/$f.png" "figures/$f.tex" "$STAGE/$NAME/figures/"; done
( cd "$STAGE/$NAME" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
rm -f "$DIST/$NAME-tex.zip"
( cd "$STAGE" && zip -qr "$DIST/$NAME-tex.zip" "$NAME" )

echo "== arXiv tarball (figure as PDF)"
mkdir -p "$STAGE/arxiv/figures"
cp main.tex "$STAGE/arxiv/"
for f in $FIGS; do cp "figures/$f.pdf" "$STAGE/arxiv/figures/"; done
( cd "$STAGE/arxiv" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
tar -czf "$DIST/$NAME-arxiv.tar.gz" -C "$STAGE/arxiv" .

rm -f main.aux main.log main.out main.pdf
ls -l "$DIST"
