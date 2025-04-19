open Tml

exception NotImplemented
exception Stuck
exception NotConvertible

type stoval = Computed of value | Delayed of exp * env
and stack = Hole_SK | Frame_SK of stack * frame

and state =
  | Anal_ST of stoval Heap.heap * stack * exp * env
  | Return_ST of stoval Heap.heap * stack * value

(* Define your own datatypes *)
and env = NOT_IMPLEMENT_ENV
and value = NOT_IMPLEMENT_VALUE
and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp te =
  let rec findFreeVar te cxt =
    match te with
    | Tvar v -> if List.exists (fun v' -> v' = v) cxt then cxt else cxt @ [ v ]
    | Tlam (v, _, te) | Tfix (v, _, te) -> findFreeVar te (v :: cxt) |> List.tl
    | Tapp (te1, te2) | Tpair (te1, te2) ->
        cxt |> findFreeVar te2 |> findFreeVar te1
    | Tfst te | Tsnd te -> findFreeVar te cxt
    | Tinl (te, _) | Tinr (te, _) -> findFreeVar te cxt
    | Tcase (te, v1, te1, v2, te2) ->
        cxt |> List.cons v2 |> findFreeVar te2 |> List.tl |> List.cons v1
        |> findFreeVar te1 |> List.tl |> findFreeVar te
    | Tifthenelse (te, te1, te2) ->
        cxt |> findFreeVar te2 |> findFreeVar te1 |> findFreeVar te
    | Teunit | Ttrue | Tfalse | Tnum _ | Tplus | Tminus | Teq -> cxt
  in
  let rec texp2exp' cxt = function
    | Tvar v -> Ind (cxt |> List.mapi (fun idx v -> (v, idx)) |> List.assoc v)
    | Tlam (v, _, te) -> Lam (texp2exp' (v :: cxt) te)
    | Tapp (te1, te2) -> App (texp2exp' cxt te1, texp2exp' cxt te2)
    | Tpair (te1, te2) -> Pair (texp2exp' cxt te1, texp2exp' cxt te2)
    | Tfst te -> Fst (texp2exp' cxt te)
    | Tsnd te -> Snd (texp2exp' cxt te)
    | Teunit -> Eunit
    | Tinl (te, _) -> Inl (texp2exp' cxt te)
    | Tinr (te, _) -> Inr (texp2exp' cxt te)
    | Tcase (te, v1, te1, v2, te2) ->
        Case
          ( texp2exp' cxt te,
            texp2exp' (v1 :: cxt) te1,
            texp2exp' (v2 :: cxt) te2 )
    | Tfix (v, _, te) -> Fix (texp2exp' (v :: cxt) te)
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (te, te1, te2) ->
        Ifthenelse (texp2exp' cxt te, texp2exp' cxt te1, texp2exp' cxt te2)
    | Tnum n -> Num n
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in
  texp2exp' (findFreeVar te []) te

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)
let shift =
  let rec shift' i v = function
    | Ind v' when v' >= i -> Ind (v' + v)
    | Ind v' -> Ind v'
    | Lam e -> Lam (shift' (i + 1) v e)
    | App (e1, e2) -> App (shift' i v e1, shift' i v e2)
    | Pair (e1, e2) -> Pair (shift' i v e1, shift' i v e2)
    | Fst e -> Fst (shift' i v e)
    | Snd e -> Snd (shift' i v e)
    | Inl e -> Inl (shift' i v e)
    | Inr e -> Inr (shift' i v e)
    | Ifthenelse (e, e1, e2) ->
        Ifthenelse (shift' i v e, shift' i v e1, shift' i v e2)
    | Case (e, e1, e2) ->
        Case (shift' i v e, shift' (i + 1) v e1, shift' (i + 1) v e2)
    | Fix e -> Fix (shift' (i + 1) v e)
    | (Eunit | True | False | Num _ | Plus | Minus | Eq) as e -> e
  in
  shift' 0

let substitute =
  let rec substitute' v m n =
    match m with
    | Ind v' when v' < v -> Ind v'
    | Ind v' when v' = v -> shift v' n
    | Ind v' (* when v' > v *) -> Ind (v' - 1)
    | Lam e -> Lam (substitute' (v + 1) e n)
    | App (e1, e2) -> App (substitute' v e1 n, substitute' v e2 n)
    | Pair (e1, e2) -> Pair (substitute' v e1 n, substitute' v e2 n)
    | Fst e -> Fst (substitute' v e n)
    | Snd e -> Snd (substitute' v e n)
    | Inl e -> Inl (substitute' v e n)
    | Inr e -> Inr (substitute' v e n)
    | Ifthenelse (e, e1, e2) ->
        Ifthenelse (substitute' v e n, substitute' v e1 n, substitute' v e2 n)
    | Case (e, e1, e2) ->
        Case
          (substitute' v e n, substitute' (v + 1) e1 n, substitute' (v + 1) e2 n)
    | Fix e -> Fix (substitute' (v + 1) e n)
    | (Eunit | True | False | Num _ | Plus | Minus | Eq) as e -> e
  in
  substitute' 0

let rec step1 = function
  | App ((Lam m as f), e) -> (
      try App (f, step1 e) with Stuck -> substitute m e)
  | App (Plus, Pair (Num n1, Num n2)) -> Num (n1 + n2)
  | App (Plus, e) -> App (Plus, step1 e)
  | App (Minus, Pair (Num n1, Num n2)) -> Num (n1 - n2)
  | App (Minus, e) -> App (Minus, step1 e)
  | App (Eq, Pair (Num n1, Num n2)) -> if n1 = n2 then True else False
  | App (Eq, e) -> App (Minus, step1 e)
  | App (e1, e2) -> App (step1 e1, e2)
  | Pair (e1, e2) -> (
      try Pair (step1 e1, e2) with Stuck -> Pair (e1, step1 e2))
  | Fst (Pair (v1, v2)) -> v1
  | Fst e -> Fst (step1 e)
  | Snd (Pair (v1, v2)) -> v2
  | Snd e -> Snd (step1 e)
  | Inl e -> Inl (step1 e)
  | Inr e -> Inr (step1 e)
  | Ifthenelse (e, e1, e2) -> (
      match e with True -> e1 | False -> e2 | _ -> Ifthenelse (step1 e, e1, e2))
  | Case (e, e1, e2) -> (
      match e with
      | Inl v -> substitute e1 v
      | Inr v -> substitute e2 v
      | _ -> Case (step1 e, e1, e2))
  | Fix e as f -> substitute e f
  | _ -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise Stuck

(* exp2string : Tml.exp -> string *)
let rec exp2string exp =
  match exp with
  | Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ exp2string e ^ ")"
  | App (e1, e2) -> "(" ^ exp2string e1 ^ " " ^ exp2string e2 ^ ")"
  | Pair (e1, e2) -> "(" ^ exp2string e1 ^ "," ^ exp2string e2 ^ ")"
  | Fst e -> "(fst " ^ exp2string e ^ ")"
  | Snd e -> "(snd " ^ exp2string e ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ exp2string e ^ ")"
  | Inr e -> "(inr " ^ exp2string e ^ ")"
  | Case (e, e1, e2) ->
      "(case " ^ exp2string e ^ " of " ^ exp2string e1 ^ " | " ^ exp2string e2
      ^ ")"
  | Fix e -> "(fix. " ^ exp2string e ^ ")"
  | Ifthenelse (e, e1, e2) ->
      "(if " ^ exp2string e ^ " then " ^ exp2string e1 ^ " else "
      ^ exp2string e2 ^ ")"
  | True -> "true"
  | False -> "false"
  | Num n -> "<" ^ string_of_int n ^ ">"
  | Plus -> "+"
  | Minus -> "-"
  | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st =
  match st with
  | Anal_ST (_, _, exp, _) -> "Analysis : ???"
  | Return_ST (_, _, _) -> "Return : ??? "

(* ------------------------------------------------------------- *)
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None
let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e =
    match stepOpt1 e with
    | None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st =
    match stepOpt2 st with
    | None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in
  Stream.icons st (steps st)
