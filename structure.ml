open Signature
open Printf

module Assignment3 : Assignment3 =
struct
	type term = C of string | V of string | F of string * (term list)
	type form = PRED of string * (term list)
				| NOT of form
				| AND of form * form
				| OR of form * form
				| FORALL of term * form (* This term should be a variable only*)
				| EXISTS of term * form (* This term should be a variable only*)
	
	exception Not_wff of (term list * form list)
	exception Not_closed of term list
	exception DPLL_unsat of int
	
	let wff formula = printf "dcshdshds"; true
	let fv formula = [V("a")]
	let closed formula = true
	let scnf formula = formula
	let dpll formula n = ([V("a")], [PRED("aa",[V("a")])])
	let sat formula n = (true, [V("a")], [PRED("aa",[V("a")])])
	
end;;
