let SessionLoad = 1
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
cd ~/src/liquidhaskell/liquid-fixpoint
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +1 SYNTHESIS.md
badd +206 src/Language/Fixpoint/Solver.hs
badd +128 src/Language/Fixpoint/Solver/Solve.hs
badd +252 src/Language/Fixpoint/Types/Constraints.hs
badd +158 src/Language/Fixpoint/Graph/Types.hs
badd +121 src/Language/Fixpoint/Types/Solutions.hs
badd +70 src/Language/Fixpoint/Types/Theories.hs
badd +81 src/Language/Fixpoint/Types/Environments.hs
badd +76 src/Language/Fixpoint/Solver/Synthesize.hs
badd +103 liquid-fixpoint.cabal
badd +1 term://.//19435:/bin/zsh
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
badd +149 Session.vim
argglobal
silent! argdel *
argadd SYNTHESIS.md
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
exe 'vert 1resize ' . ((&columns * 48 + 135) / 271)
exe 'vert 2resize ' . ((&columns * 82 + 135) / 271)
exe 'vert 3resize ' . ((&columns * 82 + 135) / 271)
exe 'vert 4resize ' . ((&columns * 56 + 135) / 271)
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
37
normal! zo
59
normal! zo
59
normal! zo
63
normal! zo
let s:l = 194 - ((54 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
194
normal! 021|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Solve.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 132 - ((32 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
132
normal! 016|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Synthesize.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 75 - ((35 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
75
normal! 019|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit term://.//19435:/bin/zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 38 - ((37 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
38
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
3wincmd w
exe 'vert 1resize ' . ((&columns * 48 + 135) / 271)
exe 'vert 2resize ' . ((&columns * 82 + 135) / 271)
exe 'vert 3resize ' . ((&columns * 82 + 135) / 271)
exe 'vert 4resize ' . ((&columns * 56 + 135) / 271)
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
