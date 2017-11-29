let SessionLoad = 1
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
cd ~/src/liquidhaskell/liquid-fixpoint
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +9 SYNTHESIS.md
badd +206 src/Language/Fixpoint/Solver.hs
badd +68 src/Language/Fixpoint/Solver/Solve.hs
badd +252 src/Language/Fixpoint/Types/Constraints.hs
badd +158 src/Language/Fixpoint/Graph/Types.hs
badd +121 src/Language/Fixpoint/Types/Solutions.hs
badd +70 src/Language/Fixpoint/Types/Theories.hs
badd +81 src/Language/Fixpoint/Types/Environments.hs
badd +29 src/Language/Fixpoint/Solver/Synthesize.hs
badd +103 liquid-fixpoint.cabal
badd +0 term://.//29978:/bin/zsh
badd +28 tests/pos/bool00.fq
badd +165 src/Language/Fixpoint/Types/Errors.hs
badd +165 src/Language/Fixpoint/Misc.hs
badd +181 src/Language/Fixpoint/Graph/Deps.hs
badd +57 /tmp/asdf
badd +1 tests/pos
badd +2 tests/pos/EqConstr0.fq
badd +2 tests/pos/bool04.fq
badd +2 tests/pos/cut-keyword.fq
badd +13 tests/pos/test2.fq
argglobal
silent! argdel *
$argadd SYNTHESIS.md
edit SYNTHESIS.md
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
3wincmd h
wincmd w
wincmd w
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
exe 'vert 1resize ' . ((&columns * 52 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 84 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 84 + 158) / 316)
exe 'vert 4resize ' . ((&columns * 93 + 158) / 316)
argglobal
setlocal fdm=expr
setlocal fde=pandoc#folding#FoldExpr()
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
27
normal! zo
59
normal! zo
let s:l = 123 - ((55 * winheight(0) + 43) / 86)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
123
normal! 0102|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Solve.hs') | buffer ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Solve.hs | else | edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Solve.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 112 - ((59 * winheight(0) + 43) / 86)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
112
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Synthesize.hs') | buffer ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Synthesize.hs | else | edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Synthesize.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 83 - ((54 * winheight(0) + 43) / 86)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
83
normal! 02|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('term://.//29978:/bin/zsh') | buffer term://.//29978:/bin/zsh | else | edit term://.//29978:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 8894 - ((85 * winheight(0) + 43) / 86)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
8894
normal! 022|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
3wincmd w
exe 'vert 1resize ' . ((&columns * 52 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 84 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 84 + 158) / 316)
exe 'vert 4resize ' . ((&columns * 93 + 158) / 316)
tabnext 1
if exists('s:wipebuf') && getbufvar(s:wipebuf, '&buftype') isnot# 'terminal'
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20 winminheight=1 winminwidth=1 shortmess=filnxtToOc
let s:sx = expand("<sfile>:p:r")."x.vim"
if file_readable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &so = s:so_save | let &siso = s:siso_save
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
