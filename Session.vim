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
badd +37 src/Language/Fixpoint/Solver.hs
badd +140 src/Language/Fixpoint/Solver/Solve.hs
badd +724 src/Language/Fixpoint/Types/Constraints.hs
badd +158 src/Language/Fixpoint/Graph/Types.hs
badd +120 src/Language/Fixpoint/Types/Solutions.hs
badd +70 src/Language/Fixpoint/Types/Theories.hs
badd +81 src/Language/Fixpoint/Types/Environments.hs
badd +46 src/Language/Fixpoint/Solver/Synthesize.hs
badd +103 liquid-fixpoint.cabal
badd +1116 term://.//18898:/bin/zsh
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
badd +31 src/Language/Fixpoint/Solver/GradualSolution.hs
badd +61 src/Language/Fixpoint/Solver/Worklist.hs
badd +284 src/Language/Fixpoint/Solver/Monad.hs
badd +140 src/Language/Fixpoint/Solver/Solution.hs
badd +76 src/Language/Fixpoint/Smt/Types.hs
badd +193 src/Language/Fixpoint/Smt/Interface.hs
badd +0 src/Language/Fixpoint/Smt/Serialize.hs
badd +197 src/Language/Fixpoint/Types/Names.hs
badd +125 tests/test.hs
badd +0 term://.//18971:/usr/bin/zsh
badd +1 tests/pos/listqual.hs.fq
badd +0 tests/pos/.liquid/listqual.hs.fq.smt2
badd +0 term://.//8145:zsh
badd +134 asdf.patch
badd +68 ~/.config/nvim/init.vim
badd +0 term://.//12336:/usr/bin/zsh
badd +0 tests/pos/.liquid/test00.fq.smt2
argglobal
silent! argdel *
argadd SYNTHESIS.md
set stal=2
edit SYNTHESIS.md
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
4wincmd h
wincmd w
wincmd w
wincmd w
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
exe 'vert 1resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 2resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 3resize ' . ((&columns * 113 + 286) / 572)
exe 'vert 4resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 5resize ' . ((&columns * 113 + 286) / 572)
argglobal
setlocal fdm=expr
setlocal fde=pandoc#folding#FoldExpr()
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
451
normal! zo
468
normal! zo
let s:l = 595 - ((10 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
595
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
let s:l = 125 - ((60 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
125
normal! 012|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 209 - ((57 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
209
normal! 016|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit term://.//12336:/usr/bin/zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 1116 - ((115 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1116
normal! 035|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
argglobal
edit term://.//18898:/bin/zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 1116 - ((115 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1116
normal! 025|
lcd ~/src/liquidhaskell/liquid-fixpoint
wincmd w
exe 'vert 1resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 2resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 3resize ' . ((&columns * 113 + 286) / 572)
exe 'vert 4resize ' . ((&columns * 114 + 286) / 572)
exe 'vert 5resize ' . ((&columns * 113 + 286) / 572)
tabedit ~/src/liquidhaskell/liquid-fixpoint/tests/pos/.liquid/test00.fq.smt2
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
let s:l = 119 - ((108 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
119
normal! 013|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/liquid-fixpoint.cabal
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
let s:l = 103 - ((102 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
103
normal! 020|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabnew
set splitbelow splitright
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
argglobal
edit term://.//8145:zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 1116 - ((115 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1116
normal! 021|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/tests/pos/.liquid/listqual.hs.fq.smt2
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
let s:l = 258 - ((107 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
258
normal! 07|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/tests/pos/listqual.hs.fq
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
let s:l = 354 - ((103 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
354
normal! 06|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabnew
set splitbelow splitright
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
argglobal
edit term://.//18971:/usr/bin/zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=20
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 316 - ((114 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
316
normal! 021|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Solver/Monad.hs
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
let s:l = 1 - ((0 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1
normal! 018|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabedit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Serialize.hs
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
let s:l = 1 - ((0 * winheight(0) + 58) / 116)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1
normal! 012|
lcd ~/src/liquidhaskell/liquid-fixpoint
tabnext 1
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
