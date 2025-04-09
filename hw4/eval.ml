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

let swap v v' =
  let swapVar u = if u = v then v' else if u = v' then v else u in
  let rec swap' = function
    | Uml.Var u -> Uml.Var (swapVar u)
    | Uml.Lam (x, e) -> Uml.Lam (swapVar x, swap' e)
    | Uml.App (e1, e2) -> Uml.App (swap' e1, swap' e2)
  in
  swap'

let substitute e' x =
  let rec substitute' = function
    | Uml.Var v when v = x -> e'
    | Uml.Var _ as v -> v
    | Uml.App (e1, e2) -> Uml.App (substitute' e1, substitute' e2)
    | Uml.Lam (y, e) as v when x = y -> v
    | Uml.Lam (y, e) -> (
        match VarSet.find_opt y (getFreeVariables e') with
        | None -> Uml.Lam (y, substitute' e)
        | Some _ ->
            let z = getFreshVariable y in
            Uml.Lam (z, substitute' (swap y z e)))
  in
  substitute'

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
let rec stepv = function
  | Uml.App (Uml.Lam (x, e), (Uml.Lam _ as v)) -> substitute v x e
  | Uml.App ((Uml.Lam _ as f), e) -> Uml.App (f, stepv e)
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
