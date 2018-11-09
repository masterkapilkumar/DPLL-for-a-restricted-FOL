module type Assignment3 = 
sig
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
	
	val wff: form -> bool
	val fv: form -> term list (* Term list consists of variable only*)
	val closed: form -> bool
	val scnf: form -> form
	val dpll: form -> int -> (term list * form list)
	val sat: form -> int -> (bool * term list * form list)
end;;
