(* Type-checking for the SUB language *)

open Printf
open AST

(* Reporting of type errors *)

exception Type_error of string

let type_error msg = raise (Type_error msg)

(* Subtyping check *)

let rec subtype t1 t2 = match t1, t2 with
  | _, Top -> true
  | _ when t1 = t2 -> true
  | Int, Float -> true
  | Arrow (u1, v1), Arrow (u2, v2) -> (subtype v1 v2) && (subtype u2 u1)
  | Record l1, Record l2 ->
      List.for_all (fun (lab, t) ->
	    try subtype (List.assoc lab l1) t
		with Not_found -> false
	  ) l2
  | _ -> false
	  

(* Infer the principal type for expression [e] in typing environment [env].
   Raise [Type_error] if the expression is ill-typed. *)

let rec infer env e =
  match e with
  (* The lambda-calculus *)
  | Evar v ->
      begin match lookup_typenv v env with
      | Some t -> t
      | None -> type_error (sprintf "unbound variable %s" v)
      end
  | Eabstr (x, tx, e) ->
      let env1 = add_typenv x tx env in
	  let te = infer env1 e in
	  Arrow (tx, te)
  | Eapp (e1, e2) ->
      let targ, tres = match infer env e1 with
	    | Arrow (targ, tres) -> targ, tres
		| t1 -> type_error (sprintf "expected an arrow type, got %s" (pretty_typ t1))
	  in
	  check env e2 targ;
	  tres
  | Elet (x, e1, e2) ->
      let t1 = infer env e1 in
	  infer (add_typenv x t1 env) e2
  (* Arithmetic *)
  | Econst c ->
      type_of_constant c
  | Eunop(op, e1) ->
      let (targ, tres) = type_of_unop op in
      check env e1 targ;
      tres
  | Ebinop(op, e1, e2) ->
      let (targ1, targ2, tres) = type_of_binop op in
      check env e1 targ1;
      check env e2 targ2;
      tres
  (* Records *)
  | Erecord l -> Record (List.map (fun (lab, e) -> (lab, infer env e)) l)
      (* TODO: check that labels are all distinct? *)
  | Efield (e, lab) ->
      let t = infer env e in
	  let rt = match t with Record rt -> rt | _ -> type_error "expected a record type" in
	  (try List.assoc lab rt
	  with Not_found -> type_error ("unknown label "^lab))
  (* Type constraint *)
  | Econstraint(e, t) ->
      check env e t; t


(* Check that expression [e] has type [t] in typing environment [env].
   Return [()] if true.  Raise [Type_error] if not. *)

and check env e t =
  let t1 = infer env e in
  if not (subtype t1 t) then
    type_error
      (sprintf "expected type %s, got %s" (pretty_typ t) (pretty_typ t1))
