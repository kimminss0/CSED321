open Mach
open Mono

exception NotImplemented

(* location *)
type loc =
  | L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)
[@@ocamlformat "disable"]

type venv = (Mono.avid, loc) Dict.dict (* variable environment *)

let venv0 : venv = Dict.empty (* empty variable environment *)

type env = venv * int

let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l =
  match l with
  | L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
      let code, rvalue = loc2rvalue l in
      ( Mach.cpost code [ Mach.MOVE (Mach.LREG Mach.tr, rvalue) ],
        Mach.REFREG (Mach.tr, i) )

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l =
  match l with
  | L_INT i -> "INT " ^ string_of_int i
  | L_BOOL b -> "BOOL " ^ string_of_bool b
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ "&" ^ a
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ "&Heap_" ^ string_of_int a
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ "&Stack_" ^ string_of_int a
  | L_REG r ->
      if r = Mach.sp then "REG SP"
      else if r = Mach.bp then "REG BP"
      else if r = Mach.cp then "REG CP"
      else if r = Mach.ax then "REG AX"
      else if r = Mach.bx then "REG BX"
      else if r = Mach.tr then "REG TR"
      else if r = Mach.zr then "REG ZR"
      else "R[" ^ string_of_int r ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ loc2str l ^ ", " ^ string_of_int i ^ ")"

let fail_label = labelNewStr "FAIL"

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label -> loc -> Mono.pat -> Mach.code * venv *)
let pat2code saddr faddr l = function
  | P_WILD | P_UNIT -> (cpre [ LABEL saddr ] code0, venv0)
  | P_INT i ->
      let code, rvalue = loc2rvalue l in
      let code' = clist [ JMPNEQ (ADDR (CADDR faddr), rvalue, INT i) ] in
      (cpre [ LABEL saddr ] (code @@ code'), venv0)
  | P_BOOL true ->
      let code, rvalue = loc2rvalue l in
      let code' =
        clist
          [
            (* TODO: ensure that it is ok to use AX here; no side effects *)
            NOT (LREG ax, rvalue);
            JMPTRUE (ADDR (CADDR faddr), REG ax);
          ]
      in
      (cpre [ LABEL saddr ] (code @@ code'), venv0)
  | P_BOOL false ->
      let code, rvalue = loc2rvalue l in
      let code' = clist [ JMPTRUE (ADDR (CADDR faddr), rvalue) ] in
      (cpre [ LABEL saddr ] (code @@ code'), venv0)
  | P_VID vid -> raise NotImplemented
  | P_VIDP (vid, patty) -> raise NotImplemented
  | P_PAIR (patty1, patty2) -> raise NotImplemented

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
let patty2code saddr faddr l (PATTY (pat, _)) = pat2code saddr faddr l pat

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
let exp2code (env : env) (saddr : label) = function
  | E_INT i -> (code0, INT i)
  | E_BOOL b -> (code0, BOOL b)
  | E_UNIT -> (code0, UNIT)
  | E_PLUS -> raise NotImplemented
  | E_MINUS -> raise NotImplemented
  | E_MULT -> raise NotImplemented
  | E_EQ -> raise NotImplemented
  | E_NEQ -> raise NotImplemented
  | E_VID vid -> raise NotImplemented
  | E_FUN mrules -> raise NotImplemented
  | E_APP (expty1, expty2) -> raise NotImplemented
  | E_PAIR (expty1, expty2) -> raise NotImplemented
  | E_LET (dec, expty) -> raise NotImplemented

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
let expty2code env saddr (EXPTY (exp, _)) = exp2code env saddr exp

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
let dec2code env saddr = function
  | D_VAL (patty, expty) ->
      let venv, count = env in
      let code1, rvalue =
        expty2code env (labelNewLabel saddr "_VAL_EXP") expty
      in
      let code2 = clist [ MOVE (LREG ax, rvalue) ] in
      let code3, venv' =
        patty2code (labelNewLabel saddr "_VAL_PAT") fail_label (L_REG ax) patty
      in
      let env' = (Dict.merge venv venv', count) in
      (cpre [ LABEL saddr ] code1 @@ code2 @@ code3, env')
  | D_REC (patty, expty) -> raise NotImplemented
  | D_DTYPE -> raise NotImplemented

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
let mrule2code env saddr faddr (M_RULE (patty, expty)) =
  let venv, count = (env : env)
  and code1, venv' =
    patty2code (labelNewLabel saddr "_PAT") faddr (L_REG bx) patty
  in
  let env' = (Dict.merge venv venv', count)
  and saddr' = labelNewLabel saddr "_EXP" in
  let code2, rvalue = expty2code env' saddr' expty in
  cpre [ LABEL saddr ] code1 @@ cpost code2 [ MOVE (LREG ax, rvalue); RETURN ]

(* program2code : Mono.program -> Mach.code *)
let program2code ((dlist, et) : Mono.program) =
  let code1, env =
    List.fold_left
      (fun (code_acc, env_acc) dec ->
        let code, env = dec2code env_acc (labelNewStr "DEC") dec in
        (code_acc @@ code, env))
      (code0, env0) dlist
  in
  let code2, rvalue = expty2code env (labelNewStr "PRGEXP") et in
  let halt = clist [ HALT rvalue; LABEL fail_label; EXCEPTION ] in
  cpre [ LABEL start_label ] code1 @@ code2 @@ halt
