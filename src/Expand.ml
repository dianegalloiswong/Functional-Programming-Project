(* Expand coercions within IL expressions.  The result is an IL expression
   without coercions, suitable for compilation to abstract machine code. *)

open AST
open IL


(* Apply a coercion [c] to the expression [l].  The result is a 
   coercion-free Lambda expression. *)

let rec apply_coercion (c: coercion) (l: lam) : lam =
  match c with
  | Cid -> l
  | Cint2float -> Lunop(Ofloatofint, l)
  | Cfun(c1, c2) ->
(*      let x, apply_l_to = match l with
	    | Labstr(x, le) -> x, fun l' -> if l' = Lvar x then le else Llet(x, l', le)
		| _ -> fresh_variable (), fun l' -> Lapp(l ,l')
	  in 
	  Labstr(x, apply_coercion c2 (apply_l_to (apply_coercion c1 (Lvar x))))
*)
	  let x = fresh_variable () in
	  let l1 = apply_coercion c1 (Lvar x) in
	  let lapp = Lapp(l, l1) in
	  let l2 = apply_coercion c2 lapp in
	  Labstr(x, l2)

(*	  let x, le = match l with
	    | Labstr(x, le) -> x, le
		| _ -> (Format.printf "\nError in Expand: function coercion so following lam should be of form Labstr@."; print_lam l; assert false)
	  in
	  let l1 = apply_coercion c1 (Lvar x) in
	  let ll = Llet(x, l1, le) in
	  let l2 = apply_coercion c2 ll in
	  Labstr(x, l2)
*)
  | Crecord ics ->
	  let from_record_variable (r: variable) =
		let compute_field (i, c) = apply_coercion c (Lfield(Lvar r, i)) in
		Ltuple (List.map compute_field ics)
	  in
	  begin 
	    match l with
		  | Ltuple ls ->
		      let compute_field (i, c) = apply_coercion c (List.nth ls (i-1)) in
			  Ltuple (List.map compute_field ics)
		  | Lvar r -> from_record_variable r
		  | _ -> let r = fresh_variable () in Llet(r, l, from_record_variable r)
	  end
	  (* If [l] is a tuple, its fields can be accessed directly with List.nth. Otherwise, we use the Lfield construction and we force the use of a variable representing the record so that it is not evaluated multiple times.*)
	  
	  
(*	  let r = fresh_variable () in
	  let tuple = List.map (fun (i, c) ->
	    apply_coercion c (Lfield(Lvar r, i))
	  ) ics in
	  Llet(r, l, Ltuple tuple)
*)
(*	  let r = match l with
	    | Ltuple r -> r
		| _ -> (Format.printf "\nError in Expand: record coercion so following lam should be of form Ltuple@."; print_lam l; assert false)
	  in
	  Ltuple (List.map (fun (i, c) ->
	    apply_coercion c (List.nth r (i-1))
	  ) ics)
*)
		

(* Recursively expand the coercions by applying them. *)

let rec expand (l: lam): lam =
  match l with
  | Lvar v -> Lvar v
  | Labstr(v, l) -> Labstr(v, expand l)
  | Lapp(l1, l2) -> Lapp(expand l1, expand l2)
  | Llet(v, l1, l2) -> Llet(v, expand l1, expand l2)
  | Lconst c -> Lconst c
  | Lunop(op, l1) -> Lunop(op, expand l1)
  | Lbinop(op, l1, l2) -> Lbinop(op, expand l1, expand l2)
  | Ltuple ll -> Ltuple (List.map expand ll)
  | Lfield(l, n) -> Lfield(expand l, n)
  | Lcoerce(l, c) -> apply_coercion c (expand l)
