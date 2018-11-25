open Structure.A3

(*
let t1 = C "romeo";;
let t2 = C "juliet";;
(* let fml = PRED("loves", [t1; t2]);; *)
let t1 = C "a";;
let v = V "x";;
let v1 = V "y";;
let v2 = V "ka";;
let v3 = V "bp";;
let fml2 = FORALL(v,FORALL(v1, AND(OR(PRED("p",[v;v1]),PRED("q",[v])),AND(OR(PRED("r",[v]),NOT(PRED("p",[v;v;v1]))),OR(PRED("q",[v]),PRED("q",[v1]))))));;

let foo =
try
let res = wff fml2 in ()
with e-> Printf.printf "%s" "Kapil";;

 let _ = if res then Printf.printf "Formula is well-formed\n" else Printf.printf "Formula is not well-formed\n";; *)
 
let t1 = C "romeo";;
let t2 = C "juliet";;
let t7 = C "habibi";;
let t3 = F("s", [t1;t2]);;
let t4 = F("s", [t1;t2;t2]);;
let t5 = V "x";;
let t6 = V "y";;

let fml1 = EXISTS(V "z", FORALL(V "y", EXISTS(V "x", AND(PRED("r", [V("x"); t3;t4]), AND(PRED("q", [t1;t2;t7]), PRED("q", [V("x"); V("y")]))) ) ) );;

let fml2 = EXISTS(V "a", FORALL(V "b", EXISTS(V "c", EXISTS(V "d", EXISTS(V "e", EXISTS(V "f", EXISTS(V "g", EXISTS(V "h", EXISTS(V "i", EXISTS(V "j", EXISTS(V "k", EXISTS(V "l", EXISTS(V "m", EXISTS(V "n", FORALL(V "o", FORALL(V "p", FORALL(V "q", FORALL(V "r", FORALL(V "s", FORALL(V "t", FORALL(V "u", FORALL(V "v", FORALL(V "w", FORALL(V "x", FORALL(V "y", EXISTS(V "z", FORALL(V "aa", FORALL(V "ab", PRED("s",[t1;t2;t3])))))))))))))))))))))))))))));;

wff fml1;;