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
	let rec find_terms_in_term term =
		match term with
			 C(s)-> []
			|V(s)-> []
			|F(s,termsl)-> term::(List.flatten(List.map find_terms_in_term termsl))
			
	let rec find_terms_in_formula form =
		match form with
			 PRED(s, termsl) -> List.flatten(List.map find_terms_in_term termsl)
			|NOT(f) -> find_terms_in_formula f
			|AND(f1,f2) -> (find_terms_in_formula f1)@(find_terms_in_formula f2)
			|OR(f1,f2) -> (find_terms_in_formula f1)@(find_terms_in_formula f2)
			|FORALL(t,f) -> find_terms_in_formula f
			|EXISTS(t,f) -> find_terms_in_formula f
	
	let wff formula =
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
	
	let rec term_vars term =
		match term with
			 C(s)-> []
			|V(s)-> [term]
			|F(s,termsl)-> List.flatten(List.map term_vars termsl)
	
	let fv formula =
		let rec fvh form = 
			match form with
				 PRED(s, termsl) -> remove_duplicates (List.flatten(List.map term_vars termsl))
				|NOT(f) -> fvh f
				|AND(f1,f2) -> remove_duplicates ((fvh f1)@(fvh f2))
				|OR(f1,f2) -> remove_duplicates ((fvh f1)@(fvh f2))
				|FORALL(t,f) -> (match t with 
									 V(s)-> List.filter (fun x->x<>t) (fvh f)
									|_-> let _ = raise (Not_wff([],[])) in fvh f
								)
				|EXISTS(t,f) -> (match t with 
									 V(s)-> List.filter (fun x->x<>t) (fvh f)
									|_-> let _ = raise (Not_wff([],[])) in fvh f
								)
		in
			fvh formula
		
	let closed formula =
		let free_variables = fv formula in
		if List.length free_variables > 0 then
			raise (Not_closed(free_variables))
		else
			true
	
	let rec cnf form =
		let rec cnfHelper p1 p2 =
			match (p1,p2) with
				 (p1, AND(p,q)) -> AND(cnfHelper p1 p, cnfHelper p1 q)
				|(AND(p,q), p1) -> AND(cnfHelper p p1, cnfHelper q p1)
				|_ -> OR(p1,p2)
		in
		match form with
			 AND(p,q) -> AND(cnf p, cnf q)
			|OR(p,q) -> cnfHelper (cnf p) (cnf q)
			|_ -> form					
	
	let rec nnf formula =
		match formula with
			 NOT(NOT(t)) -> nnf t
			|NOT(AND(s,t)) -> OR(nnf (NOT s), nnf (NOT t))  
			|NOT(OR(s,t)) -> AND(nnf (NOT s), nnf (NOT t))  
			|NOT(FORALL(s,t)) -> EXISTS(s, nnf(NOT t))
			|NOT(EXISTS(s,t)) -> FORALL(s, nnf (NOT t))
			|AND(s,t) -> AND(nnf s, nnf t)  
			|OR(s,t) -> OR(nnf s, nnf t)  
			|FORALL(s,t) -> FORALL(s, nnf t)
			|EXISTS(s,t) -> EXISTS(s, nnf t)
			|_ -> formula
	
	let pcnf formula =
		let rec term_replace x z term =
			match term with
				 V(c) -> if(c=x) then V(z)
						 else V(c)
				|C(s) -> C(s)
				|F(s,e) -> F(s, List.map (term_replace x z) e)
		in
		let rec variant x vars =
			if (List.mem (V x) vars) then
				variant (x^"'") vars
			else
				x
		in
		(* Replace x with z in formula p *)
		let rec replace x z p =
			match p with
			   FORALL(s,t) -> FORALL(s, replace x z t)        (*TODO: check admissibility of substitution inside quantifier - substq function*)
			  |EXISTS(s,t) -> EXISTS(s, replace x z t)        (*check admissibility of substitution inside quantifier*)
			  |PRED(s,t) -> PRED(s, List.map (term_replace x z) t)
			  |AND(s,t) -> AND(replace x z s, replace x z t)
			  |OR(s,t) -> OR(replace x z s, replace x z t)
			  |NOT(s) -> NOT(replace x z s)
		in
		let rec moveQ form =
			match form with
				 AND(FORALL(V(x),p),FORALL(V(y),q)) -> let z = variant x (fv form) in FORALL(V(z), moveQ (AND(replace x z p, replace y z q)))
				|OR(EXISTS(V(x),p),EXISTS(V(y),q)) -> let z = variant x (fv form) in EXISTS(V(z), moveQ (OR(replace x z p, replace y z q)))
				|AND(FORALL(V(x),p),q) -> let z = variant x (fv form) in FORALL(V(z), moveQ (AND(replace x z p, q)))
				|AND(q,FORALL(V(x),p)) -> let z = variant x (fv form) in FORALL(V(z), moveQ (AND(q, replace x z p)))
				|OR(FORALL(V(x),p),q) -> let z = variant x (fv form) in FORALL(V(z), moveQ (OR(replace x z p, q)))
				|OR(q,FORALL(V(x),p)) -> let z = variant x (fv form) in FORALL(V(z), moveQ (OR(q, replace x z p)))
				|AND(EXISTS(V(x),p),q) -> let z = variant x (fv form) in EXISTS(V(z), moveQ (AND(replace x z p, q)))
				|AND(q,EXISTS(V(x),p)) -> let z = variant x (fv form) in EXISTS(V(z), moveQ (AND(q, replace x z p)))
				|OR(EXISTS(V(x),p),q) -> let z = variant x (fv form) in EXISTS(V(z), moveQ (OR(replace x z p, q)))
				|OR(q,EXISTS(V(x),p)) -> let z = variant x (fv form) in EXISTS(V(z), moveQ (OR(q, replace x z p)))
				|_ -> form
		in
		let rec prenex form =
			match form with
				 FORALL(s,t) -> FORALL(s,prenex t)
				|EXISTS(s,t) -> EXISTS(s,prenex t)
				|AND(p,q) -> moveQ (AND(prenex p, prenex q))
				|OR(p,q) ->  moveQ (OR(prenex p, prenex q))
				|_ -> form
		in
		let rec makePcnf pnf =
			match pnf with
			 FORALL(s,t) -> FORALL(s, makePcnf t)
			|EXISTS(s,t) -> EXISTS(s, makePcnf t)
			|t -> cnf t
		in
		let pnf = prenex (nnf formula)
		in
			makePcnf pnf
	
	let rec get_formula_strings form =
		match form with
			 F(s,t)::xs -> s::(get_formula_strings t)@(get_formula_strings xs)
			|_ -> []
	
	let scnf formula =
		let rec replaceFuncTerm var func term =
			match term with
				 V(c) -> if(c=var) then func 
						 else V(c)
				|C(s) -> C(s)
				|F(s,t) -> F(s, List.map (replaceFuncTerm var func) t)
		in
		let rec replaceFunc form var func =
			match form with
				 PRED(s,t) -> PRED(s, List.map (replaceFuncTerm var func) t)
				|AND(p,q) -> AND(replaceFunc p var func, replaceFunc q var func)
				|OR(p,q) -> OR(replaceFunc p var func, replaceFunc q var func)
				|NOT(p) -> NOT(replaceFunc p var func)
				|FORALL(s,t) -> FORALL(s,replaceFunc t var func)
				|EXISTS(s,t) -> EXISTS(s,replaceFunc t var func)
		in
		let rec str_variant x funcs =
			if (List.mem x funcs) then
				str_variant (x^"'") funcs
			else
				x
		in
		let rec skolem form funcs vars =
			match form with
				 FORALL(V(s),t) -> let t_bar, funcs_bar = skolem t funcs (s::vars) in (FORALL(V(s),t_bar), funcs_bar)
				(* |AND(p,q) -> let p1, funcs1 = skolem p funcs vars in *)
							 (* let p2, funcs2 = skolem p1 funcs1 vars in *)
							  (* (AND(p1,p2),funcs2) *)
				(* |OR(p,q) -> let p1, funcs1 = skolem p funcs vars in *)
							(* let p2, funcs2 = skolem p1 funcs1 vars in *)
							 (* (OR(p1,p2),funcs2) *)
				
				|EXISTS(V(s),t) -> let z = if vars = [] then str_variant ("c_"^s) funcs else str_variant ("f_"^s) funcs in
									(* let _ = Printf.printf "replace  %s\n" z in *)
								skolem (replaceFunc t s (if vars=[] then C(z) else F(z, List.map (fun v-> V(v)) vars))) (z::funcs) vars
				|_ -> (form, funcs)
		in	
		fst (skolem (pcnf formula) (remove_duplicates (get_formula_strings (find_terms_in_formula formula))) [])
	
	(* let rec print_term term = *)
		(* match term with *)
			(* C(s) -> Printf.printf "%s," s *)
			(* |V(s) -> Printf.printf "%s," s *)
			(* |F(s,t) -> let _= Printf.printf "%s(" s in let _= List.map print_term t in Printf.printf ")" *)
	(* let rec print_form formula = *)
		(* match formula with *)
			(* PRED(s,t) -> let _= Printf.printf "%s(" s in let _= List.map print_term t in Printf.printf ")" *)
			(* | NOT(s) -> let _=Printf.printf "NOT(" in let _=print_form s in Printf.printf ")" *)
			(* | AND(p,q) -> let _=Printf.printf "AND(" in let _=print_form p in let _=Printf.printf "," in let _=print_form q in Printf.printf ")" *)
			(* | OR(p,q) -> let _=Printf.printf "OR(" in let _=print_form p in let _=Printf.printf "," in let _=print_form q in Printf.printf ")" *)
			(* | FORALL(s,t) -> let _=Printf.printf "FORALL(" in let _=(print_term s) in let _=Printf.printf "," in let _=(print_form t) in Printf.printf ")" *)
			(* | EXISTS(s,t) ->  let _=Printf.printf "EXISTS(" in let _=(print_term s) in let _=Printf.printf "," in let _=(print_form t) in Printf.printf ")" *)
	
	let rec printTermlist (t_list:term list) = 
		match t_list with
		|[] -> ""
		|C(s)::[] -> "const("^s^")"
		|V(s)::[] -> "var("^s^")"
		|F(s, t_l)::[] -> "func("^s^","^(printTermlist t_l)^")"
		|C(s)::ts -> "const("^s^"),"^(printTermlist ts)
		|V(s)::ts -> "var("^s^"),"^(printTermlist ts)
		|F(s, t_l)::ts -> "func("^s^","^(printTermlist t_l)^"),"^(printTermlist ts)
	let rec printFOL (l) = 
		match l with
		|PRED (s, t_l) -> "PRED("^s^","^(printTermlist t_l)^")"
		|NOT (ll) -> "NOT("^(printFOL ll)^")"
		|AND (ll, lr) -> "AND("^(printFOL ll)^","^(printFOL lr)^")"
		|OR (ll, lr) -> "OR("^(printFOL ll)^","^(printFOL lr)^")"
		|FORALL (V(s), ll) -> "FORALL("^"var("^s^")"^","^(printFOL ll)^")"
		|EXISTS (V(s), ll) -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^")"
		| _ -> ""

	let rec printFOLlist (l_list: form list) = 
		match l_list with
		|[] -> ""
		|(PRED (s, t_l))::[] -> "PRED("^s^","^(printTermlist t_l)^")"
		|(NOT (ll))::[] -> "NOT("^(printFOL ll)^")"
		|(AND (ll, lr))::[] -> "AND("^(printFOL ll)^","^(printFOL lr)^")"
		|( OR (ll, lr))::[] -> "OR("^(printFOL ll)^","^(printFOL lr)^")"
		|(FORALL (V(s), ll))::[] -> "FORALL("^"var("^s^")"^","^(printFOL ll)^")"
		|(EXISTS (V(s), ll))::[] -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^")"
		|(PRED (s, t_l))::lls -> "PRED("^s^","^(printTermlist t_l)^"),"^(printFOLlist lls)
		|(NOT (ll))::lls -> "NOT("^(printFOL ll)^"),"^(printFOLlist lls)
		|(AND (ll, lr))::lls -> "AND("^(printFOL ll)^","^(printFOL lr)^"),"^(printFOLlist lls)
		|( OR (ll, lr))::lls -> "OR("^(printFOL ll)^","^(printFOL lr)^"),"^(printFOLlist lls)
		|(FORALL (V(s), ll))::lls -> "FORALL("^"var("^s^")"^","^(printFOL ll)^"),"^(printFOLlist lls)
		|(EXISTS (V(s), ll))::lls -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^"),"^(printFOLlist lls)
		| _ -> ""
	
	let dpll formula n =
		let all_vals = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] in
		let rec generate_consts n vals ret =
			if n=0 then ret
			else generate_consts (n-1) (List.tl vals) (ret@[List.hd vals])
		in
		let vals = generate_consts n all_vals [] in
		(* let _ = List.map (fun xx-> Printf.printf "%s, " xx) vals in *)
		let rec getcnf form =
			match form with
				 FORALL(_, t) -> getcnf t
				|_ -> form
		in
		let rec getvars form =
			match form with
				 FORALL(v, t) -> v::(getvars t)
				|_ -> []
		in
		let cnf_form = getcnf formula in
		let cnf_vars = getvars formula in
		(* let _ = List.map (fun xx-> Printf.printf "%s, " (match xx with V(s)->s)) cnf_vars in *)
		let rec loop func i n assigned =
			if i=n then ()
			else 
			let _ = func (assigned@[List.nth vals i]) in 
				loop func (i+1) n assigned
		in
		let rec find_var_index ls var index =
			if(var=(List.nth ls index)) then index
			else find_var_index ls var (index+1)
		in
		let rec term_subst vars assigned_vals term =
			match term with
				 C(s)-> C(s)
				|V(s)-> C(List.nth assigned_vals (find_var_index vars term 0))
				|F(s,t)-> F(s, List.map (term_subst vars assigned_vals) t)
		in
		let rec do_subst form vars assigned_vals =
			match form with
				 AND(p,q) -> AND(do_subst p vars assigned_vals, do_subst q vars assigned_vals)
				|OR(p,q) -> OR(do_subst p vars assigned_vals, do_subst q vars assigned_vals)
				|NOT(p) -> NOT(do_subst p vars assigned_vals)
				|PRED(s, t) -> PRED(s, List.map (term_subst vars assigned_vals) t)
				|_ -> form
		in
		let rec assign_vals local_vars assigned =
			match local_vars with
				 v::vs -> loop (assign_vals vs) 0 (List.length vals) assigned
				|[] -> let  new_formula = do_subst cnf_form cnf_vars assigned in 
						Printf.printf "%s\n" (printFOL new_formula)
		in
			assign_vals cnf_vars []
		
	let sat formula n = (true, [V("a")], [PRED("aa",[V("a")])])
	
	
	
	
	
	
end;;
let t1 = Assignment3.C "a";;
let v = Assignment3.V "x";;
let v1 = Assignment3.V "y";;
let v2 = Assignment3.V "ka";;
let v3 = Assignment3.V "bp";;
(* let fml = Assignment3.AND(Assignment3.PRED("p", [Assignment3.F("f",[t1]); Assignment3.F("f",[t1])]), Assignment3.NOT(Assignment3.FORALL(v1, Assignment3.PRED("p",[v1]))));; *)
let fml = Assignment3.AND(Assignment3.FORALL(v1, Assignment3.FORALL(v3,Assignment3.FORALL(v2,Assignment3.PRED("p",[v1])))), Assignment3.NOT(Assignment3.FORALL(v, Assignment3.PRED("p",[v]))));;
let z = Assignment3.V("z");;
let x = Assignment3.V("x");;
let y = Assignment3.V("y");;
(* let fml1 = Assignment3.OR (Assignment3.PRED("p", [z]), Assignment3.FORALL(x, Assignment3.AND(Assignment3.PRED("p", [x]), Assignment3.FORALL(x, Assignment3.OR(Assignment3.PRED("p", [y]), Assignment3.PRED("p", [x]))))));; *)
(* Assignment3.fv fml;; *)
(* Assignment3.closed fml;; *)
Assignment3.pcnf fml;;
Printf.printf "%s\n" (Assignment3.printFOL (Assignment3.scnf fml));;
Assignment3.dpll (Assignment3.scnf fml) 2;;

(*
*)