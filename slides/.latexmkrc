@default_files = ('main.tex');

$pdf_mode = 4;   # lualatex
$aux_dir  = 'build';
$out_dir  = '.';

$lualatex = 'lualatex -shell-escape -synctex=1 -interaction=nonstopmode -file-line-error %O %S';
$bibtex   = 'bibtex %O %B';
