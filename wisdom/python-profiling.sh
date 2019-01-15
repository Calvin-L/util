# deps
brew install graphviz
brew install python3
pip3 install gprof2dot

# what ya do
python3 -m cProfile -o [OUT] file.py [args...]
gprof2dot -f pstats [OUT] | dot -Tpng -o [OUT.png]
open [OUT.png]
