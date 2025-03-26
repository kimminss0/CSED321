(*
 * Call-by-value reduction   
 *)

exception NotImplemented
exception Stuck

let freshVarCounter = ref 0

(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s =
  let _ = freshVarCounter := !freshVarCounter + 1 in
  s ^ "__" ^ string_of_int !freshVarCounter

module VarSet = Set.Make (String)

let rec getFreeVariables = function
  | Uml.Var v -> VarSet.singleton v
  | Uml.Lam (x, e) -> VarSet.remove x (getFreeVariables e)
  | Uml.App (e1, e2) -> VarSet.union (getFreeVariables e1) (getFreeVariables e2)

let rec substitute e' x = function
  | Uml.Var v -> if v = x then e' else Uml.Var v
  | Uml.App (e1, e2) -> Uml.App (substitute e' x e1, substitute e' x e2)
  | Uml.Lam (y, e) -> (
      if x = y then Uml.Lam (x, e)
      else
        match VarSet.find_opt y (getFreeVariables e') with
        | None -> Uml.Lam (y, substitute e' x e)
        | Some _ ->
            let z = getFreshVariable y in
            Uml.Lam (z, substitute e' x (substitute (Uml.Var z) y e)))

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
let rec stepv = function
  | Uml.App (Uml.Lam (x, e), Uml.Lam (y, e')) ->
      substitute (Uml.Lam (y, e')) x e
  | Uml.App (Uml.Lam (x, e), e2) -> Uml.App (Uml.Lam (x, e), stepv e2)
  | Uml.App (e1, e2) -> Uml.App (stepv e1, e2)
  | _ -> raise Stuck

let stepOpt stepf e = try Some (stepf e) with Stuck -> None
let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e =
    match stepOpt stepf e with
    | None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in
  Stream.icons e (steps e)
