(* Optimization of coercions in an IL expression *)

open IL



exception No_optimization_found
(* Used to track whether an auxiliary function has performed an optimization, so that the main function [optim] calls itself if and only if an optimization was actually performed. This recursive call checks whether an optimization has enabled a new one, but should not happen when no optimization was found because it would lead to an infinite loop. *)



(* Compose two coercions: return [c1 o c2]. *)
let rec compose_coercions c1 c2 = match c1, c2 with
  | Cid, _ -> c2
  | _, Cid -> c1
  | Cfun(c1arg, c1res), Cfun(c2arg, c2res) -> Cfun(compose_coercions c2arg c1arg, compose_coercions c1res c2res)
      (* c1(c2(f)) = c1res o c2res o f o c2arg o c1arg *)
  | Crecord ics1, Crecord ics2 -> 
      Crecord (List.map (fun (i, c) ->
	    let (j, d) = List.nth ics2 (i-1) in
		(j, compose_coercions c d)
	  ) ics1)
      (* With c1 = Crecord [(i_1, c_1); ...; (i_n, c_n)]
		      c2 = Crecord [(j_1, d_1); ...; (j_m, d_m)] :
	     c1(c2(r)).k = c_k(c2(r).i_k) = c_k( d_(i_k)( r.j_(i_k) ) )
	     c1 o c2 = Crecord [( j_(i_k), c_k o d_(i_k) ) for k = 1..n] *)
  | _ -> assert false

  
(* If the second argument is of the form [(i+1, Cid); ...; (n, Cid)], return [n], else return [-1].*)
let rec incr_from_i_and_Cid i = function
  | [] -> i
  | (j, Cid)::t when j = i+1 -> incr_from_i_and_Cid (i+1) t
  | _ -> -1
(* Determine whether [ics] is of the form [(1, Cid); ...; (n, Cid)] with [ls] of length [n], in which case [Crecord ics] applied to [Ltuple ls] is equivalent to [Cid]. *)
let crecord_equiv_cid ls ics = (incr_from_i_and_Cid 0 ics) = (List.length ls)

  
(* Optimization of expressions of the form Lcoerce(l, c) *)
let rec optim_coerce l c = match l, c with
  (* Coercions that don't change representation *)
  | _, Cfun(Cid, Cid) -> Lcoerce(l, Cid)
  | Ltuple ls, Crecord ics when crecord_equiv_cid ls ics -> Lcoerce(l, Cid)
  (* Build big record then coerce to smaller record *)
  | Ltuple ls, Crecord ics when List.length ls > List.length ics ->
      let take_lam (i, _) = List.nth ls (i-1) in
	  let rec reindex i = function
	    | [] -> []
		| (_, c)::t -> (i,c)::(reindex (i+1) t)
	  in
	  Lcoerce((Ltuple (List.map take_lam ics)), (Crecord (reindex 1 ics)) )
  (* Telescopes of coercions *)
  | Lcoerce(l2, c2), _ -> Lcoerce(l2, (compose_coercions c c2))
  (* Build function closure then coerce to supertype *)
  | Labstr(x, le), Cfun(c1, c2) ->
	  let l1 = 
	    if c1 = Cid then le
	    else Llet(x, Lcoerce(Lvar x, c1), le)
	  in
      Labstr(x, Lcoerce(l1, c2))
  (* Propagate coercion inside [let] to try and enable new optimizations *)
  | Llet(x, l1, l2), _ -> Llet(x, l1, Lcoerce(l2, c))
  | _ -> raise No_optimization_found
  
  
(* Optimization of expressions of the form Lapp(l1, l2) *)
let optim_app l1 l2 = match l1 with
  (* Coerce function then apply *)
  | Lcoerce(l, Cfun(c1, c2)) -> Lcoerce( Lapp(l, Lcoerce(l2, c1)), c2)
  | _ -> raise No_optimization_found
  
  
(* Optimization of expressions of the form Lfield(l, n) *)
let optim_field l n = match l with
  (* Coerce record then project field *)
  | Lcoerce(l1, Crecord ics) -> 
      let (i, c) = List.nth ics (n-1) in
	  Lcoerce(Lfield(l1, i), c)
  | _ -> raise No_optimization_found
  
  
(* Optimization of expressions *)
let rec optim (l: lam) : lam = match l with
  | Lvar v -> Lvar v
  | Labstr(v, l) -> Labstr(v, optim l)
  | Lapp(l1, l2) -> 
      let l1 = optim l1 and l2 = optim l2 in
	  (try optim (optim_app l1 l2) with No_optimization_found -> Lapp(l1, l2))
  | Llet(v, l1, l2) -> Llet(v, optim l1, optim l2)
  | Lconst c -> Lconst c
  | Lunop(op, l1) -> Lunop(op, optim l1)
  | Lbinop(op, l1, l2) -> Lbinop(op, optim l1, optim l2)
  | Ltuple ll -> Ltuple (List.map optim ll)
  | Lfield(l, n) -> 
      let l = optim l in
	  (try optim (optim_field l n) with No_optimization_found -> Lfield(l, n))
  | Lcoerce(l, c) -> 
      let l = optim l in
	  (try optim (optim_coerce l c) with No_optimization_found -> Lcoerce(l, c))