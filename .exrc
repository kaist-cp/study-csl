fun s:iris_stuff()
    let l:iris_conceal = [
                \ ['proves', '⊢'],
                \ ['later', '⊳'],
                \ ['always', '□'],
                \ ['wand', '🍭'],
                \ ['ownGhost', '👻'],
                \ ['knowInv', '知'],
                \ ['authfull', '●'],
                \ ['authfrag', '○'],
                \ ['vs', '⇛'],
                \ ['fpfn', '⇀'],
                \ ['mupd', '⇝'],
                \ ['la', '←'],
                \ ['ra', '→'],
                \ ['Ra', '⇒'],
                \ ['Lra', '⇔'],
                \ ['nequiv', '='],
                \ ['E',  '𝓔'],
                \ ['mask', '𝓔'],
                \ ['expr', 'e'],
                \ ['I',  '𝓘'],
                \ ['N',  '𝓝'],
                \ ['namesp', '𝓝'],
                \ ['mval', '𝓥'],
                \ ['mvalFull', '𝓥']]
    for pair in l:iris_conceal
        " NOTE: pair[0] =~# '\w$' should hold
        exe "syn match texMathSymbol '\\\\".pair[0]."\\>' contained conceal cchar=".pair[1]
    endfor
endfun

augroup iris_stuff
  autocmd!
  autocmd Syntax pandoc call s:iris_stuff()
augroup end
