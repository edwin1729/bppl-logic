@default_files = ('main.tex');
$pdf_mode = 5;            # use xelatex (fontspec requires xetex/luatex)
$aux_dir  = 'build';      # .aux, .log, .toc, .xdv, etc. go here
$out_dir  = '.';          # final PDF lands in masters-report/
$xelatex  = 'xelatex -shell-escape -synctex=1 -interaction=nonstopmode -file-line-error %O %S';

# Prefer TeX Live's bibtex so it can find natbib's .bst files
# (the Debian /usr/bin/bibtex doesn't see TL's texmf tree).
$bibtex = '/usr/local/texlive/2025/bin/x86_64-linux/bibtex %O %B';
