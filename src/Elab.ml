(* Type-directed elaboration of SUB expressions into IL expressions *)

open Printf
open AST
open IL

(* Reporting of type errors *)

exception Type_error of string

let type_error msg = raise (Type_error msg)


(* If [l] is a key-value pairs list, [assoc_ind k l] returns the first value associated to [k] and the index of the corresponding pair, starting at 1. *)
let rec assoc_ind_aux i x = function
  | [] -> raise Not_found
  | (k, v)::_ when k = x -> (v, i)
  | _::l -> assoc_ind_aux (i+1) x l
let assoc_ind x l = assoc_ind_aux 1 x l


(* Subtyping check.  If [t1] is a subtype of [t2], return the coercion 
   that transforms values of type [t1] into values of type [t2].
   If [t1] is not a subtype of [t2], raise [Not_subtype] exception. *)

exception Not_subtype

let rec subtype t1 t2 = match t1, t2 with
  | _, Top -> Cid
  | _ when t1 = t2 -> Cid
  | Int, Float -> Cint2float
  | Arrow (u1, v1), Arrow (u2, v2) -> 
      let cv = subtype v1 v2 in
	  let cu = subtype u2 u1 in
	  Cfun (cu, cv)
  | Record l1, Record l2 ->
      Crecord (List.map 
	    (fun (lab, u2) ->
	      try 
		    let (u1, i) = assoc_ind lab l1 in
		    i, subtype u1 u2
		  with Not_found -> raise Not_subtype
	    ) l2)
  | _ -> raise Not_subtype
  

(* Elaborate the expression [e] in typing environment [env].
   Return a pair of the principal type and the IL term.
   Raise [Type_error] if the expression is ill-typed. *)

let rec elab env = function
  (* The lambda-calculus *)
  | Evar v ->
      begin match lookup_typenv v env with
      | Some t -> t, Lvar v
      | None -> type_error (sprintf "unbound variable %s" v)
      end
  | Eabstr (x, tx, e) ->
      let env1 = add_typenv x tx env in
	  let te, le = elab env1 e in
	  Arrow (tx, te), Labstr (x, le)
  | Eapp (e1, e2) ->
	  let t1, le1 = elab env e1 in
      let targ, tres = match t1 with
	    | Arrow (targ, tres) -> targ, tres
		| _ -> type_error (sprintf "expected an arrow type, got %s" (pretty_typ t1))
	  in
	  let le2 = check env e2 targ in
	  tres, Lapp (le1, le2)
  | Elet (x, e1, e2) ->
      let t1, le1 = elab env e1 in
	  let t2, le2 = elab (add_typenv x t1 env) e2 in
	  t2, Llet (x, le1, le2)
  (* Arithmetic *)
  | Econst c ->
      type_of_constant c, Lconst c
  | Eunop(op, e1) ->
      let (targ, tres) = type_of_unop op in
      let le1 = check env e1 targ in
      tres, Lunop (op, le1)
  | Ebinop(op, e1, e2) ->
      let (targ1, targ2, tres) = type_of_binop op in
      let le1 = check env e1 targ1 in
      let le2 = check env e2 targ2 in
      tres, Lbinop (op, le1, le2)
  (* Records *)
  | Erecord l -> 
	  let lab_t_le_list = List.map (fun (lab, e) -> 
	    let t, le = elab env e in (lab, t), le
	  ) l in
	  Record (List.map fst lab_t_le_list), Ltuple (List.map snd lab_t_le_list)
      (* Labels are all distinct: checked by the parser. *)
  | Efield (e, lab) ->
	let t, le = elab env e in
	let rt = match t with Record rt -> rt | _ -> type_error "expected a record type" in
	let tres, i = try assoc_ind lab rt with Not_found -> type_error ("unknown label "^lab) in
	tres, Lfield (le, i)
  (* Type constraint *)
  | Econstraint(e, t) ->
      let le = check env e t in
	  t, le

	  

(* Check that expression [e] has type [t] in typing environment [env].
   Return its lambda translation if so.
   Raise [Type_error] if not. *)

and check env e t =
  let t1, e1 = elab env e in
  let c = 
    try subtype t1 t
	with Not_subtype -> type_error
      (sprintf "expected type %s, got %s" (pretty_typ t) (pretty_typ t1))
  in
  Lcoerce (e1, c)
