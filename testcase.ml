open Structure.Assignment3

let t1 = C "romeo";;
let t2 = C "juliet";;
let fml = PRED("loves", [t1; t2]);;
wff fml;;