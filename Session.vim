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
badd +143 src/Language/Fixpoint/Solver/Solve.hs
badd +252 src/Language/Fixpoint/Types/Constraints.hs
badd +158 src/Language/Fixpoint/Graph/Types.hs
badd +352 src/Language/Fixpoint/Types/Solutions.hs
badd +70 src/Language/Fixpoint/Types/Theories.hs
badd +99 src/Language/Fixpoint/Types/Environments.hs
badd +43 src/Language/Fixpoint/Solver/Synthesize.hs
badd +103 liquid-fixpoint.cabal
badd +0 term://.//29978:/bin/zsh
badd +28 tests/pos/bool00.fq
badd +165 src/Language/Fixpoint/Types/Errors.hs
badd +55 src/Language/Fixpoint/Misc.hs
badd +181 src/Language/Fixpoint/Graph/Deps.hs
badd +57 /tmp/asdf
badd +1 tests/pos
badd +2 tests/pos/EqConstr0.fq
badd +2 tests/pos/bool04.fq
badd +2 tests/pos/cut-keyword.fq
badd +13 tests/pos/test2.fq
badd +10 src/Language/Fixpoint/Solver/Solution.hs
badd +183 src/Language/Fixpoint/Defunctionalize.hs
badd +325 src/Language/Fixpoint/Solver/Instantiate.hs
badd +366 src/Language/Fixpoint/Smt/Interface.hs
badd +69 src/Language/Fixpoint/Solver/Monad.hs
badd +57 src/Language/Fixpoint/Smt/Types.hs
badd +5313 term://.//31769:/bin/zsh
badd +106 tests/pos/.liquid/test00.fq.smt2
badd +251 src/Language/Fixpoint/Types/Refinements.hs
badd +121 ~/.config/nvim/init.vim
badd +388 src/Language/Fixpoint/Types/Visitor.hs
badd +0 dist/test/liquid-fixpoint-0.7.0.1-test
badd +1 dist/test
badd +29 dist/test/liquid-fixpoint-0.7.0.1-test.log
badd +1 dist/test/liquid-fixpoint-0.7.0.1.log
badd +0 term://.//6941:/bin/zsh
argglobal
silent! argdel *
$argadd SYNTHESIS.md
set stal=2
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
exe 'vert 1resize ' . ((&columns * 60 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 86 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 90 + 158) / 316)
exe 'vert 4resize ' . ((&columns * 77 + 158) / 316)
argglobal
setlocal fdm=expr
setlocal fde=pandoc#folding#FoldExpr()
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
61
normal! zo
65
normal! zo
253
normal! zo
let s:l = 463 - ((56 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
463
normal! 0106|
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
let s:l = 153 - ((52 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
153
normal! 048|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Monad.hs') | buffer ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Monad.hs | else | edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Monad.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 272 - ((28 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
272
normal! 066|
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
let s:l = 10085 - ((84 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
10085
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
exe 'vert 1resize ' . ((&columns * 60 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 86 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 90 + 158) / 316)
exe 'vert 4resize ' . ((&columns * 77 + 158) / 316)
tabedit ~/src/liquidhaskell/liquid-fixpoint/SYNTHESIS.md
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
wincmd _ | wincmd |
split
1wincmd k
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
exe 'vert 1resize ' . ((&columns * 79 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 78 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 78 + 158) / 316)
exe '4resize ' . ((&lines * 42 + 44) / 88)
exe 'vert 4resize ' . ((&columns * 78 + 158) / 316)
exe '5resize ' . ((&lines * 42 + 44) / 88)
exe 'vert 5resize ' . ((&columns * 78 + 158) / 316)
argglobal
setlocal fdm=expr
setlocal fde=pandoc#folding#FoldExpr()
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
61
normal! zo
65
normal! zo
253
normal! zo
let s:l = 465 - ((58 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
465
normal! 0198|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs') | buffer ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs | else | edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 376 - ((51 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
376
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Instantiate.hs') | buffer ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Instantiate.hs | else | edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Instantiate.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 365 - ((51 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
365
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('term://.//31769:/bin/zsh') | buffer term://.//31769:/bin/zsh | else | edit term://.//31769:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 5598 - ((41 * winheight(0) + 21) / 42)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
5598
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
if bufexists('term://.//6941:/bin/zsh') | buffer term://.//6941:/bin/zsh | else | edit term://.//6941:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 4477 - ((41 * winheight(0) + 21) / 42)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
4477
normal! 04|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
2wincmd w
exe 'vert 1resize ' . ((&columns * 79 + 158) / 316)
exe 'vert 2resize ' . ((&columns * 78 + 158) / 316)
exe 'vert 3resize ' . ((&columns * 78 + 158) / 316)
exe '4resize ' . ((&lines * 42 + 44) / 88)
exe 'vert 4resize ' . ((&columns * 78 + 158) / 316)
exe '5resize ' . ((&lines * 42 + 44) / 88)
exe 'vert 5resize ' . ((&columns * 78 + 158) / 316)
tabnew
set splitbelow splitright
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
argglobal
if bufexists('term://.//31769:/bin/zsh') | buffer term://.//31769:/bin/zsh | else | edit term://.//31769:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 5258 - ((77 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
5258
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/tests/pos/bool00.fq
set splitbelow splitright
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
argglobal
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 1 - ((0 * winheight(0) + 42) / 85)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1
normal! 0
lcd ~/src/liquidhaskell/liquid-fixpoint
tabnext 2
set stal=1
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
