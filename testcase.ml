open Structure.Assignment3

let t1 = C "romeo";;
let t2 = C "juliet";;
let fml = PRED("loves", [t1; t2]);;
let res = wff fml;;
let _ = if res then Printf.printf "Formula is well-formed\n" else Printf.printf "Formula is not well-formed\n"