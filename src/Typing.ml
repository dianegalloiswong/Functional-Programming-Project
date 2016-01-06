(* Type-checking for the SUB language *)

open Printf
open AST

(* Reporting of type errors *)

exception Type_error of string

let type_error msg = raise (Type_error msg)

(* Subtyping check *)

let rec subtype t1 t2 = false 

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
  (* Type constraint *)
  | Econstraint(e, t) ->
      check env e t; t
  | _ -> type_error "TODO" 

(* Check that expression [e] has type [t] in typing environment [env].
   Return [()] if true.  Raise [Type_error] if not. *)

and check env e t =
  let t1 = infer env e in
  if not (subtype t1 t) then
    type_error
      (sprintf "expected type %s, got %s" (pretty_typ t) (pretty_typ t1))
