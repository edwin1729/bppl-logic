@default_files = ('main.tex');
$pdf_mode = 5;   # xelatex
$aux_dir  = 'build';
$out_dir  = '.';
$xelatex  = 'xelatex -shell-escape -synctex=1 -interaction=nonstopmode -file-line-error %O %S';
$bibtex = 'bibtex %O %B';