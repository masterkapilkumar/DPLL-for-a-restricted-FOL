open Signature
open Printf

module A3 : Assignment3 =
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
	
	
	(* let rec printTermlist (t_list:term list) =  *)
		(* match t_list with *)
		(* |[] -> "" *)
		(* |C(s)::[] -> "const("^s^")" *)
		(* |V(s)::[] -> "var("^s^")" *)
		(* |F(s, t_l)::[] -> "func("^s^","^(printTermlist t_l)^")" *)
		(* |C(s)::ts -> "const("^s^"),"^(printTermlist ts) *)
		(* |V(s)::ts -> "var("^s^"),"^(printTermlist ts) *)
		(* |F(s, t_l)::ts -> "func("^s^","^(printTermlist t_l)^"),"^(printTermlist ts) *)
	(* let rec printFOL (l) =  *)
		(* match l with *)
		(* |PRED (s, t_l) -> "PRED("^s^","^(printTermlist t_l)^")" *)
		(* |NOT (ll) -> "NOT("^(printFOL ll)^")" *)
		(* |AND (ll, lr) -> "AND("^(printFOL ll)^","^(printFOL lr)^")" *)
		(* |OR (ll, lr) -> "OR("^(printFOL ll)^","^(printFOL lr)^")" *)
		(* |FORALL (V(s), ll) -> "FORALL("^"var("^s^")"^","^(printFOL ll)^")" *)
		(* |EXISTS (V(s), ll) -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^")" *)
		(* | _ -> "" *)

	(* let rec printFOLlist (l_list: form list) =  *)
		(* match l_list with *)
		(* |[] -> "" *)
		(* |(PRED (s, t_l))::[] -> "PRED("^s^","^(printTermlist t_l)^")" *)
		(* |(NOT (ll))::[] -> "NOT("^(printFOL ll)^")" *)
		(* |(AND (ll, lr))::[] -> "AND("^(printFOL ll)^","^(printFOL lr)^")" *)
		(* |( OR (ll, lr))::[] -> "OR("^(printFOL ll)^","^(printFOL lr)^")" *)
		(* |(FORALL (V(s), ll))::[] -> "FORALL("^"var("^s^")"^","^(printFOL ll)^")" *)
		(* |(EXISTS (V(s), ll))::[] -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^")" *)
		(* |(PRED (s, t_l))::lls -> "PRED("^s^","^(printTermlist t_l)^"),"^(printFOLlist lls) *)
		(* |(NOT (ll))::lls -> "NOT("^(printFOL ll)^"),"^(printFOLlist lls) *)
		(* |(AND (ll, lr))::lls -> "AND("^(printFOL ll)^","^(printFOL lr)^"),"^(printFOLlist lls) *)
		(* |( OR (ll, lr))::lls -> "OR("^(printFOL ll)^","^(printFOL lr)^"),"^(printFOLlist lls) *)
		(* |(FORALL (V(s), ll))::lls -> "FORALL("^"var("^s^")"^","^(printFOL ll)^"),"^(printFOLlist lls) *)
		(* |(EXISTS (V(s), ll))::lls -> "EXISTS("^"var("^s^")"^","^(printFOL ll)^"),"^(printFOLlist lls) *)
		(* | _ -> "" *)
	
	let rec make_lit cnff =
		match cnff with
			x::xs-> if xs=[] then x else OR(x, make_lit xs)
			|_-> PRED("khaali_clause",[])
	
	let rec make_form cnff =
		match cnff with
			x::xs-> 
					if xs=[] then make_lit x else AND(make_lit x, make_form xs)
			|_-> PRED("khaali_clause_list",[])
	
	let rec prop_dpll cnf model =
		
		let propogate cnf clause =
			match clause with
				 NOT(cls) -> let cnf' = List.filter (fun c-> try let _ = List.find (fun lit-> lit=clause) c in false with Not_found -> true) cnf in
							 List.map (fun c-> List.filter (fun lit-> lit <> cls) c) cnf'
				|_ -> let cnf' = List.filter (fun c-> try let _=List.find (fun lit-> lit=clause) c in false with Not_found -> true) cnf in
						List.map (fun c-> List.filter (fun lit-> lit <> NOT(clause)) c) cnf'
		in
		let rec unit_propogate cnf clauses =
			try
				let unit_clause = List.hd (List.find (fun x-> (List.length x)=1) cnf) in
				let modified_cnf = propogate cnf unit_clause in
					unit_propogate modified_cnf (unit_clause::clauses)
			with Not_found -> (cnf, clauses)
		in
		(* let rec print_list = function  *)
			(* [] -> () *)
			(* | e::l -> Printf.printf "%s" (printFOL e) ; print_string " " ; print_list l *)
			(* in *)
		let rec get_literals cnf =
			let lits = List.flatten cnf in
			
			List.filter (
				fun lit->
				try
					 match lit with NOT(l)-> let _=List.find (fun ll->l=ll) lits in false | _-> let _=List.find (fun ll->ll=NOT(lit)) lits in false
				with Not_found -> true
			) lits
		in
		let rec delete_literal cnf pure_lit =
			List.filter (fun c-> try let _ = List.find (fun lit-> lit=pure_lit) c in false with Not_found -> true) cnf
		in
		let rec pure_literal_propogate cnf clauses =

			let pure_literals = get_literals cnf in
			(* let _=Printf.printf "\n"  in *)
			(* let _=print_list pure_literals in *)
			(* let _=Printf.printf "\n"  in *)
			if(pure_literals=[]) then (cnf, clauses)
			else
			let pure_literal = List.hd pure_literals in
			let modified_cnf = delete_literal cnf pure_literal in
				pure_literal_propogate modified_cnf (pure_literal::clauses)

		in
		let rec is_empty_clause cnf =
			match cnf with
				 []::xs -> true
				|cls::xs -> is_empty_clause xs
				|_ -> false
		in
			if(cnf=[]) then (true, model)
			else if (is_empty_clause cnf) then (false, model)
			else
				let (modified_cnf, clauses1) = unit_propogate cnf [] in
				if (is_empty_clause modified_cnf) then (false, clauses1@model)
				else
				let (modified_cnf, clauses2) = pure_literal_propogate modified_cnf [] in
				if (is_empty_clause modified_cnf) then (false, clauses1@clauses2@model)
				else
				(* let _ = Printf.printf "%s\n" (printFOL (make_form cnf)) in *)
				(* let _ = Printf.printf "%s\n" (printFOL (make_form modified_cnf)) in *)
			let lit = List.hd (List.flatten cnf) in
			if(modified_cnf=[]) then (true, clauses1@clauses2@model)
			else if( match (prop_dpll ([lit]::modified_cnf) (clauses1@clauses2@model)) with (value, _)->value) then (true, clauses1@clauses2@model)
			else if( match (prop_dpll ([NOT(lit)]::modified_cnf) (clauses1@clauses2@model)) with (value, _)->value) then (true, clauses1@clauses2@model)
			else (false, clauses1@clauses2@model)
	
	let rec get_lit_list clause =
		match clause with
			 OR(p,q) -> (get_lit_list p) @ (get_lit_list q)
			|_ -> [clause]
	
	let rec get_clauses formula =
		match formula with
			 AND(p,q) -> (get_clauses p) @ (get_clauses q)
			|_ -> [get_lit_list formula]
			
	
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
			if i=n then ([],[])
			else 
			let (tl, pl) = func (assigned@[C(List.nth vals i)]) in
				if(tl=[]) then loop func (i+1) n assigned
				else (tl, pl)
		in
		let rec find_var_index ls var index =
			if(var=(List.nth ls index)) then index
			else find_var_index ls var (index+1)
		in
		let rec term_subst vars assigned_vals term =
			match term with
				 C(s)-> C(s)
				|V(s)-> List.nth assigned_vals (find_var_index vars term 0)
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
				|[] -> let new_formula = do_subst cnf_form cnf_vars assigned in 
						let (is_valid, model) = prop_dpll (get_clauses new_formula) [] in
						if(is_valid = true) then (* (term_list, pred_list) *) (List.map (fun s->C s) vals, model) (* Write functions to fins terms and ground predicates *)
						else
						(* let _ = Printf.printf "Not satisfiable -  %s\n" (printFOL new_formula) in *)
						([],[])
		in
			let (tl, pl) = assign_vals cnf_vars [] in
			if(tl=[]) then raise (DPLL_unsat n)
			else (tl, pl)
		
	let sat formula k = 
		let rec sat_helper form j =
			if (j>k) then (false, [], []) else
			try	let (terms, forms) = dpll form j in
				(true, terms, forms)
			with DPLL_unsat(x) -> sat_helper form (j+1)
		in
		let _ = wff formula in
		let _ = closed formula in
		let scnf_form = scnf formula in
			sat_helper scnf_form 1
end;;


(*
let t1 = A3.C "a";;
let v = A3.V "x";;
let v1 = A3.V "y";;
let v2 = A3.V "ka";;
let v3 = A3.V "bp";;
let fml2 = A3.FORALL(v,A3.FORALL(v1, A3.AND(A3.PRED("p",[v;v]),A3.AND(A3.NOT(A3.PRED("p",[v;v1])),A3.PRED("q",[v1])))));;
let xx=A3.cnf fml2;;
(* let fml = A3.AND(A3.PRED("p", [A3.F("f",[t1]); A3.F("f",[t1])]), A3.NOT(A3.FORALL(v1, A3.PRED("p",[v1]))));; *)
let fml = A3.AND(A3.FORALL(v1, A3.FORALL(v3,A3.FORALL(v2,A3.PRED("p",[v1])))), A3.NOT(A3.FORALL(v, A3.PRED("p",[v]))));;
let z = A3.V("z");;
let x = A3.V("x");;
let y = A3.V("y");;
(* let fml1 = A3.OR (A3.PRED("p", [z]), A3.FORALL(x, A3.AND(A3.PRED("p", [x]), A3.FORALL(x, A3.OR(A3.PRED("p", [y]), A3.PRED("p", [x]))))));; *)
(* A3.fv fml;; *)
(* A3.closed fml;; *)
(* A3.wff fml2;; *)
Printf.printf "%s\n" (A3.printFOL (A3.scnf fml2));;
(* A3.dpll (A3.scnf fml2) 2;; *)
A3.sat fml2 4;;


*)


(* let t1 = A3.C "romeo";; *)
(* let t2 = A3.C "juliet";; *)
(* let t7 = A3.C "habibi";; *)
(* let t5 = A3.V "z";; *)
(* let t6 = A3.V "y";; *)
(* let t3 = A3.F("s", [t5;t2]);; *)
(* let t4 = A3.F("s", [t1;t2;t2]);; *)

(* let fml1 = A3.EXISTS(A3.V "z", A3.FORALL(A3.V "y", A3.EXISTS(A3.V "x", A3.AND(A3.PRED("r", [A3.V("x"); t3;t4]), A3.AND(A3.PRED("q", [t1;t2;t7]), A3.PRED("q", [A3.V("x"); A3.V("y")]))) ) ) );; *)

(* let fml2 = A3.EXISTS(A3.V "a", A3.FORALL(A3.V "z", A3.EXISTS(A3.V "c", A3.EXISTS(A3.V "d", A3.EXISTS(A3.V "e", A3.EXISTS(A3.V "f", A3.EXISTS(A3.V "g", A3.EXISTS(A3.V "h", A3.EXISTS(A3.V "i", A3.EXISTS(A3.V "j", A3.EXISTS(A3.V "k", A3.EXISTS(A3.V "l", A3.EXISTS(A3.V "m", A3.EXISTS(A3.V "n", A3.FORALL(A3.V "o", A3.FORALL(A3.V "p", A3.FORALL(A3.V "q", A3.FORALL(A3.V "r", A3.FORALL(A3.V "s", A3.FORALL(A3.V "t", A3.FORALL(A3.V "u", A3.FORALL(A3.V "v", A3.FORALL(A3.V "w", A3.FORALL(A3.V "x", A3.FORALL(A3.V "y", A3.EXISTS(A3.V "z", A3.FORALL(A3.V "aa", A3.FORALL(A3.V "ab", A3.PRED("s",[t1;t2;t3])))))))))))))))))))))))))))));; *)

(* A3.sat fml2 10;; *)
(* A3.scnf fml2;; *)