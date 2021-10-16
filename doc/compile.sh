set -x
set -e

dot -Tpng concepts.dot > concepts.png
pdftex notes.tex

