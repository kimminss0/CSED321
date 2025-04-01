open Tml

exception TypeError

(* not efficient, but does work *)
type context = var -> tp

let createEmptyContext () = fun _ -> raise TypeError
let extendContext cxt v t = fun v' -> if v = v' then t else cxt v'

let rec typing cxt = function
  | Var v -> cxt v
  | Lam (v, a, e) -> Fun (a, typing (extendContext cxt v a) e)
  | App (e, e') -> (
      match (typing cxt e, typing cxt e') with
      | Fun (a, b), c when a = c -> b
      | _ -> raise TypeError)
  | Pair (e1, e2) -> Prod (typing cxt e1, typing cxt e2)
  | Fst e -> (
      match typing cxt e with Prod (a1, a2) -> a1 | _ -> raise TypeError)
  | Snd e -> (
      match typing cxt e with Prod (a1, a2) -> a2 | _ -> raise TypeError)
  | Eunit -> Unit
  | Inl (e, a2) -> Sum (typing cxt e, a2)
  | Inr (e, a1) -> Sum (a1, typing cxt e)
  | Case (e, x1, e1, x2, e2) -> (
      match typing cxt e with
      | Sum (a1, a2) ->
          let c1 = typing (extendContext cxt x1 a1) e1 in
          let c2 = typing (extendContext cxt x2 a2) e2 in
          if c1 = c2 then c1 else raise TypeError
      | _ -> raise TypeError)
  | Fix (v, a, e) when a = typing (extendContext cxt v a) e -> a
  | True | False -> Bool
  | Ifthenelse (e, e1, e2) -> (
      match (typing cxt e, typing cxt e1, typing cxt e2) with
      | Bool, a1, a2 when a1 = a2 -> a1
      | _ -> raise TypeError)
  | Num _ -> Int
  | Plus | Minus -> Fun (Prod (Int, Int), Int)
  | Eq -> Fun (Prod (Int, Int), Bool)
  | _ -> raise TypeError

let typeOf e = typing (createEmptyContext ()) e
let typeOpt e = try Some (typeOf e) with TypeError -> None
