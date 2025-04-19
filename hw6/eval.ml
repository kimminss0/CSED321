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
and env = Heap.loc list

and value =
  | Vclosure of env * exp
  | Veunit
  | Vtrue
  | Vfalse
  | Vnum of int
  | Vplus
  | Vminus
  | Veq

and frame =
  | FheapRef of Heap.loc
  | Fapp of env * exp
  | Ffst
  | Fsnd
  | Fcase of env * exp * exp
  | Fifthenelse of env * exp * exp
  | Fplus
  | Fplus_Pair1 of env * exp
  | Fplus_Pair2 of int
  | Fminus
  | Fminus_Pair1 of env * exp
  | Fminus_Pair2 of int
  | Feq
  | Feq_Pair1 of env * exp
  | Feq_Pair2 of int

let ( @@ ) stack frame = Frame_SK (stack, frame)

(* Define your own empty environment *)
let emptyEnv = []

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let rec value2exp = function
  | Veunit -> Eunit
  | Vtrue -> True
  | Vfalse -> False
  | Vnum n -> Num n
  | _ -> raise NotConvertible

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
let step2 = function
  | Anal_ST (heap, stack, exp, env) -> (
      match exp with
      | Ind x -> (
          let loc =
            env |> List.mapi (fun idx loc -> (idx, loc)) |> List.assoc x
          in
          match Heap.deref heap loc with
          | Computed v -> Return_ST (heap, stack, v)
          | Delayed (exp', env') ->
              Anal_ST (heap, stack @@ FheapRef loc, exp', env'))
      | Lam _ -> Return_ST (heap, stack, Vclosure (env, exp))
      | App (Plus, e) -> Anal_ST (heap, stack @@ Fplus, e, env)
      | App (Minus, e) -> Anal_ST (heap, stack @@ Fminus, e, env)
      | App (Eq, e) -> Anal_ST (heap, stack @@ Feq, e, env)
      | App (e1, e2) -> Anal_ST (heap, stack @@ Fapp (env, e2), e1, env)
      | Pair _ -> Return_ST (heap, stack, Vclosure (env, exp))
      | Fst e -> Anal_ST (heap, stack @@ Ffst, e, env)
      | Snd e -> Anal_ST (heap, stack @@ Fsnd, e, env)
      | Eunit -> Return_ST (heap, stack, Veunit)
      | Inl _ | Inr _ -> Return_ST (heap, stack, Vclosure (env, exp))
      | Case (e, e1, e2) -> Anal_ST (heap, stack @@ Fcase (env, e1, e2), e, env)
      | Fix e ->
          let heap', loc = Heap.allocate heap (Delayed (exp, env)) in
          Anal_ST (heap', stack, e, loc :: env)
      | True -> Return_ST (heap, stack, Vtrue)
      | False -> Return_ST (heap, stack, Vfalse)
      | Ifthenelse (e, e1, e2) ->
          Anal_ST (heap, stack @@ Fifthenelse (env, e1, e2), e, env)
      | Num n -> Return_ST (heap, stack, Vnum n)
      | Plus -> Return_ST (heap, stack, Vplus)
      | Minus -> Return_ST (heap, stack, Vminus)
      | Eq -> Return_ST (heap, stack, Veq))
  | Return_ST (heap, stack, v) -> (
      match stack with
      | Hole_SK -> raise Stuck
      | Frame_SK (stack', frame) -> (
          match (frame, v) with
          | FheapRef loc, _ ->
              let heap' = Heap.update heap loc (Computed v) in
              Return_ST (heap', stack', v)
          | Fapp (env, e2), Vclosure (env', Lam e) ->
              let heap', loc = Heap.allocate heap (Delayed (e2, env)) in
              Anal_ST (heap', stack', e, loc :: env')
          | Ffst, Vclosure (env', Pair (e1, e2)) ->
              Anal_ST (heap, stack', e1, env')
          | Fsnd, Vclosure (env', Pair (e1, e2)) ->
              Anal_ST (heap, stack', e2, env')
          | Fcase (env, e1, e2), Vclosure (env', Inl e) ->
              let heap', loc = Heap.allocate heap (Delayed (e, env')) in
              Anal_ST (heap', stack', e1, loc :: env)
          | Fcase (env, e1, e2), Vclosure (env', Inr e) ->
              let heap', loc = Heap.allocate heap (Delayed (e, env')) in
              Anal_ST (heap', stack', e2, loc :: env)
          | Fifthenelse (env, e1, e2), Vtrue -> Anal_ST (heap, stack', e1, env)
          | Fifthenelse (env, e1, e2), Vfalse -> Anal_ST (heap, stack', e2, env)
          | Fplus, Vclosure (env', Pair (e1, e2)) ->
              Anal_ST (heap, stack' @@ Fplus_Pair1 (env', e2), e1, env')
          | Fplus_Pair1 (env, e2), Vnum n1 ->
              Anal_ST (heap, stack' @@ Fplus_Pair2 n1, e2, env)
          | Fplus_Pair2 n1, Vnum n2 -> Return_ST (heap, stack', Vnum (n1 + n2))
          | Fminus, Vclosure (env', Pair (e1, e2)) ->
              Anal_ST (heap, stack' @@ Fminus_Pair1 (env', e2), e1, env')
          | Fminus_Pair1 (env, e2), Vnum n1 ->
              Anal_ST (heap, stack' @@ Fminus_Pair2 n1, e2, env)
          | Fminus_Pair2 n1, Vnum n2 -> Return_ST (heap, stack', Vnum (n1 - n2))
          | Feq, Vclosure (env', Pair (e1, e2)) ->
              Anal_ST (heap, stack' @@ Feq_Pair1 (env', e2), e1, env')
          | Feq_Pair1 (env, e2), Vnum n1 ->
              Anal_ST (heap, stack' @@ Feq_Pair2 n1, e2, env)
          | Feq_Pair2 n1, Vnum n2 ->
              Return_ST (heap, stack', if n1 = n2 then Vtrue else Vfalse)
          | _ -> raise Stuck))

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
  let rec env2string env =
    env
    |> List.mapi (fun idx loc -> (loc, idx))
    |> List.fold_left
         (fun acc (loc, x) ->
           acc ^ ", " ^ string_of_int x ^ "->" ^ string_of_int loc)
         "."
    |> fun str -> "{" ^ str ^ "}"
  and value2string = function
    | Vclosure (env, exp) -> "[" ^ env2string env ^ ", " ^ exp2string exp ^ "]"
    | Veunit -> "()"
    | Vtrue -> "true"
    | Vfalse -> "false"
    | Vnum n -> "<" ^ string_of_int n ^ ">"
    | Vplus -> "+"
    | Vminus -> "-"
    | Veq -> "="
  and heap2string h =
    let stoval2string = function
      | Computed v -> "computed(" ^ value2string v ^ ")"
      | Delayed (exp, env) ->
          "delayed(" ^ exp2string exp ^ ", " ^ env2string env ^ ")"
    in
    List.fold_right
      (fun (loc, s) acc ->
        acc ^ ", " ^ string_of_int loc ^ "->" ^ stoval2string s)
      h "."
  and stack2string =
    let frame2string = function
      | FheapRef loc -> "[" ^ string_of_int loc ^ "]"
      | Fapp (env, exp) -> "_" ^ env2string env ^ " " ^ exp2string exp
      | Ffst -> "fst _"
      | Fsnd -> "snd _"
      | Fcase (env, e1, e2) ->
          "case _^{" ^ env2string env ^ "} of inl. " ^ exp2string e1
          ^ " | inr. " ^ exp2string e2
      | Fifthenelse (env, e1, e2) ->
          "if _^{" ^ env2string env ^ "} then " ^ exp2string e1 ^ " else "
          ^ exp2string e2
      | Fplus -> "+ _"
      | Fplus_Pair1 (env, e2) ->
          "+ (_^{" ^ env2string env ^ "}, " ^ exp2string e2 ^ ")"
      | Fplus_Pair2 n1 -> "+ (<" ^ string_of_int n1 ^ ">, _)"
      | Fminus -> "- _"
      | Fminus_Pair1 (env, e2) ->
          "- (_^{" ^ env2string env ^ "}, " ^ exp2string e2 ^ ")"
      | Fminus_Pair2 n1 -> "- (<" ^ string_of_int n1 ^ ">, _)"
      | Feq -> "= _"
      | Feq_Pair1 (env, e2) ->
          "= (_^{" ^ env2string env ^ "}, " ^ exp2string e2 ^ ")"
      | Feq_Pair2 n1 -> "= (<" ^ string_of_int n1 ^ ">, _)"
    in
    function
    | Hole_SK -> "_"
    | Frame_SK (stack, frame) -> stack2string stack ^ " ; " ^ frame2string frame
  in
  match st with
  | Anal_ST (heap, stack, exp, env) ->
      heap2string heap ^ " || " ^ stack2string stack ^ " >> " ^ exp2string exp
      ^ " @ " ^ env2string env
  | Return_ST (heap, stack, v) ->
      heap2string heap ^ " || " ^ stack2string stack ^ " << " ^ value2string v

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
