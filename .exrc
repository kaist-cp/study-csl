fun s:iris_stuff()
    syn match texMathSymbol '\\proves' contained conceal cchar=⊢
    syn match texMathSymbol '\\later' contained conceal cchar=⊳
    syn match texMathSymbol '\\always' contained conceal cchar=□
    syn match texMathSymbol '\\wand' contained conceal cchar=🍭
    syn match texMathSymbol '\\ownGhost' contained conceal cchar=👻
    syn match texMathSymbol '\\knowInv' contained conceal cchar=知

    syn match texMathSymbol '\\vs' contained conceal cchar=⇛
    syn match texMathSymbol '\\fpfn' contained conceal cchar=⇀

    syn match texMathSymbol '\\E' contained conceal cchar=𝓔
    syn match texMathSymbol '\\mask' contained conceal cchar=𝓔
    syn match texMathSymbol '\\I' contained conceal cchar=𝓘
    syn match texMathSymbol '\\N' contained conceal cchar=𝓝
    syn match texMathSymbol '\\mval' contained conceal cchar=𝓥
    syn match texMathSymbol '\\mvalFull' contained conceal cchar=𝓥
endfun

augroup iris_stuff
  autocmd!
  autocmd Syntax pandoc call s:iris_stuff()
augroup end
