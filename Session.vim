let SessionLoad = 1
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
cd ~/src/liquidhaskell/liquid-fixpoint
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +532 src/Language/Fixpoint/Interpolate.hs
badd +172 term://.//10587:/bin/zsh
badd +84 src/Language/Fixpoint/SortCheck.hs
badd +420 term://.//13902:/bin/zsh
badd +4422 ~/src/liquidhaskell/liquid-fixpoint/tests/interp/.liquid/Ackermann.hs.fq.smt2
badd +123 ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs
badd +303 src/Language/Fixpoint/Solver/Monad.hs
badd +1 term://.//23666:zsh
badd +553 src/Language/Fixpoint/Types/Constraints.hs
badd +94 src/Language/Fixpoint/Types/Environments.hs
badd +3221 __CtrlSF__
badd +17560 ~/src/liquidhaskell/liquid-fixpoint/examples/fixpoint.prof
badd +276 src/Language/Fixpoint/Solver/Sanitize.hs
badd +60 src/Language/Fixpoint/Smt/Types.hs
badd +64 ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Types/Config.hs
badd +58 ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Serialize.hs
badd +1 ~/src/liquidhaskell/.git/modules/liquid-fixpoint/refs/heads/develop
badd +0 fugitive:///home/atondwal/src/liquidhaskell/.git/modules/liquid-fixpoint//138184a41dc73fec45393a980240e573c028fee3/src/Language/Fixpoint/Solver/Instantiate.hs
argglobal
silent! argdel *
argadd src/Language/Fixpoint/Interpolate.hs
set stal=2
edit src/Language/Fixpoint/Interpolate.hs
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
2wincmd h
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
exe 'vert 1resize ' . ((&columns * 106 + 159) / 319)
exe 'vert 2resize ' . ((&columns * 105 + 159) / 319)
exe '3resize ' . ((&lines * 39 + 41) / 82)
exe 'vert 3resize ' . ((&columns * 106 + 159) / 319)
exe '4resize ' . ((&lines * 39 + 41) / 82)
exe 'vert 4resize ' . ((&columns * 106 + 159) / 319)
argglobal
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 531 - ((65 * winheight(0) + 39) / 79)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
531
normal! 020|
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Types/Config.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 6 - ((5 * winheight(0) + 39) / 79)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
6
normal! 0
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 508 - ((7 * winheight(0) + 19) / 39)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
508
normal! 024|
wincmd w
argglobal
edit term://.//10587:/bin/zsh
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 1038 - ((37 * winheight(0) + 19) / 39)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1038
normal! 0
wincmd w
exe 'vert 1resize ' . ((&columns * 106 + 159) / 319)
exe 'vert 2resize ' . ((&columns * 105 + 159) / 319)
exe '3resize ' . ((&lines * 39 + 41) / 82)
exe 'vert 3resize ' . ((&columns * 106 + 159) / 319)
exe '4resize ' . ((&lines * 39 + 41) / 82)
exe 'vert 4resize ' . ((&columns * 106 + 159) / 319)
tabedit fugitive:///home/atondwal/src/liquidhaskell/.git/modules/liquid-fixpoint//138184a41dc73fec45393a980240e573c028fee3/src/Language/Fixpoint/Solver/Instantiate.hs
set splitbelow splitright
wincmd _ | wincmd |
vsplit
1wincmd h
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=1 winminwidth=1 winheight=1 winwidth=1
exe 'vert 1resize ' . ((&columns * 159 + 159) / 319)
exe 'vert 2resize ' . ((&columns * 159 + 159) / 319)
argglobal
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 276 - ((18 * winheight(0) + 39) / 79)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
276
normal! 041|
wincmd w
argglobal
edit ~/src/liquidhaskell/liquid-fixpoint/src/Language/Fixpoint/Smt/Interface.hs
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 1 - ((0 * winheight(0) + 39) / 79)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
1
normal! 013|
wincmd w
exe 'vert 1resize ' . ((&columns * 159 + 159) / 319)
exe 'vert 2resize ' . ((&columns * 159 + 159) / 319)
tabnext 1
set stal=1
if exists('s:wipebuf') && getbufvar(s:wipebuf, '&buftype') isnot# 'terminal'
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20 winminheight=1 winminwidth=1 shortmess=filnxtToO
let s:sx = expand("<sfile>:p:r")."x.vim"
if file_readable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &so = s:so_save | let &siso = s:siso_save
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
