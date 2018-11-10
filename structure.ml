open Signature
open Printf

module Assignment3 =
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
	
	(* Remove duplicates formulae or terms *)
	let remove_duplicates form_list =
		let rec remove_dups all_forms forms_set =
			match all_forms with
				 f::tl -> (try let _ = (List.find (fun x->x=f) forms_set) in remove_dups tl forms_set
						  with Not_found -> remove_dups tl (f::forms_set)
						  )
				|[] -> forms_set
		in
			remove_dups form_list []
	
	let wff formula =
		let rec find_terms_in_term term =
			match term with
				 C(s)-> []
				|V(s)-> []
				|F(s,termsl)-> term::(List.flatten(List.map find_terms_in_term termsl))
		in		
		let rec find_terms_in_formula form =
			match form with
				 PRED(s, termsl) -> List.flatten(List.map find_terms_in_term termsl)
				|NOT(f) -> find_terms_in_formula f
				|AND(f1,f2) -> (find_terms_in_formula f1)@(find_terms_in_formula f2)
				|OR(f1,f2) -> (find_terms_in_formula f1)@(find_terms_in_formula f2)
				|FORALL(t,f) -> find_terms_in_formula f
				|EXISTS(t,f) -> find_terms_in_formula f
		in
		let rec find_formula form =
			match form with
				 PRED(s, termsl) -> [form]
				|NOT(f) -> find_formula f
				|AND(f1,f2) -> (find_formula f1)@(find_formula f2)
				|OR(f1,f2) -> (find_formula f1)@(find_formula f2)
				|FORALL(t,f) -> find_formula f     (*TODO: qualifier binds only one variable*)
				|EXISTS(t,f) -> find_formula f
		in
		let rec check_formula_arities forms invalid =
			match forms with
				 f::tl -> (match f with
							(* If s1 is already in the list of invalid formulas then continue else find whether s1 is invalid or not *)
							 PRED(s1,l1) -> (try let _ = (List.find (fun x->match x with PRED(s,l)->s=s1 | _->false) invalid) in check_formula_arities tl invalid
											  with Not_found ->
												(* Find all the formulas matching with predicate s1 *)
												let inv = List.filter (fun x->match x with PRED(s,l)->s=s1 | _->false) forms
												(* Check if s1 has multiple arities *)
											    in if (List.length (List.filter (fun x->match x with PRED(s,l)->(List.length l) <> (List.length l1) | _->false) inv)) > 0 
												   then check_formula_arities tl (inv@invalid)
												   else check_formula_arities tl invalid
											  )
							|_-> check_formula_arities tl invalid
						  )
				|[] -> invalid
		in
		let rec check_term_arities terms invalid =
			match terms with
				 t::tl -> (match t with
							(* If s1 is already in the list of invalid terms then continue else find whether s1 is invalid or not *)
							 F(s1,l1) -> (try let _ = (List.find (fun x->match x with F(s,l)->s=s1 | _->false) invalid) in check_term_arities tl invalid
											  with Not_found ->
												(* Find all the terms matching with term s1 *)
												let inv = List.filter (fun x->match x with F(s,l)->s=s1 | _->false) terms
												(* Check if s1 has multiple arities *)
												in if List.length (List.filter (fun x->match x with F(s,l)->(List.length l) <> (List.length l1) | _->false) inv) > 0
												   then check_term_arities tl (inv@invalid)
												   else check_term_arities tl invalid
											  )
							|_-> check_term_arities tl invalid
						  )
				|[] -> invalid
		in
			let all_formulas = remove_duplicates (find_formula formula) in
			let all_terms = remove_duplicates (find_terms_in_formula formula) in
			let all_invalid_formulas = check_formula_arities all_formulas [] in
			let all_invalid_terms = check_term_arities all_terms [] in
				if(all_invalid_formulas=[] && all_invalid_terms=[]) then
					true
				else let _ = raise (Not_wff(all_invalid_terms, all_invalid_formulas)) in false
	
	
	let fv formula =
		let rec term_vars term =
			match term with
				 C(s)-> []
				|V(s)-> [s]
				|F(s,termsl)-> List.flatten(List.map term_vars termsl)
		in
		let rec fvh form = 
			match form with
				 PRED(s, termsl) -> remove_duplicates (List.flatten(List.map term_vars termsl))
				|NOT(f) -> fvh f
				|AND(f1,f2) -> remove_duplicates ((fvh f1)@(fvh f2))
				|OR(f1,f2) -> remove_duplicates ((fvh f1)@(fvh f2))
				|FORALL(t,f) -> (match t with 
									 V(s)-> List.filter (fun x->x<>s) (fvh f)
									|_-> let _ = raise (Not_wff([],[])) in fvh f
								)
				|EXISTS(t,f) -> (match t with 
									 V(s)-> List.filter (fun x->x<>s) (fvh f)
									|_-> let _ = raise (Not_wff([],[])) in fvh f
								)
		in
			fvh formula
		
	let closed formula = true
	let scnf formula = formula
	let dpll formula n = ([V("a")], [PRED("aa",[V("a")])])
	let sat formula n = (true, [V("a")], [PRED("aa",[V("a")])])
	
end;;
(*
let t1 = Assignment3.C "a";;
let v = Assignment3.V "x";;
let v1 = Assignment3.V "y";;
let fml = Assignment3.AND(Assignment3.PRED("p", [Assignment3.F("f",[t1]); Assignment3.F("f",[t1]); t1]), Assignment3.NOT(Assignment3.FORALL(v, Assignment3.PRED("p",[t1;v1;v1]))));;
Assignment3.fv fml;;

*)