(* Compilation of IL (without coercions) to abstract machine code *)

open Printf
open AST
open IL
open Mach

exception Error of string


let rec index l x i = match l with
  | [] -> raise Not_found
  | h::_ when h = x -> i
  | _::t -> index t x (i+1)
let get_ind env v = index env v 1

let rec compile env (l: lam) : code = match l with
  | Lvar v -> [ Iaccess (get_ind env v) ]
  | Labstr(v, l) -> [ Iclosure (compile_tail (v::env) l) ]
  | Lapp(l1, l2) -> (compile env l1)@(compile env l2)@[ Iapply ]
  | Llet(v, l1, l2) -> (compile env l1)@[ Ilet ]@(compile (v::env) l2)@[ Iendlet ]
  | Lconst c -> [ Ipush c ]
  | Lunop(op, l1) -> 
      let instr = match op with
	    | Ointoffloat -> Iintoffloat
		| Ofloatofint -> Ifloatofint
	  in
	  (compile env l1)@[ instr ]
  | Lbinop(op, l1, l2) -> 
      let instr = match op with
	    | Oaddint -> Iaddint
		| Oaddfloat -> Iaddfloat
	  in
	  (compile env l1)@(compile env l2)@[ instr ]
  | Ltuple ll -> (List.concat (List.map (compile env) ll))@[ Imaketuple (List.length ll) ]
  | Lfield(l, i) -> (compile env l)@[ Ifield i ]
  | Lcoerce _ -> assert false
  
and compile_tail env l = match l with
  | Lapp(l1, l2) -> (compile env l1)@(compile env l2)@[ Itailapply ]
  | Llet(v, l1, l2) -> (compile env l1)@[ Ilet ]@(compile_tail (v::env) l2)
  | _ -> (compile env l)@[ Ireturn ]

let program (l: lam) : code = compile [] l
