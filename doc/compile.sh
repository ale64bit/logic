set -x
set -e

dot -Tpng concepts.dot > concepts.png
dot -Tpng results.dot > results.png
pdftex notes.tex

