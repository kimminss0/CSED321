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

(* polyfill of List.init *)
let init n f =
  let rec init' n f l = if n > 0 then init' (n - 1) f (f (n - 1) :: l) else l in
  init' n f []

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

let vid2string = function
  | avid, VAR -> avid ^ " (VAR)"
  | avid, CON -> avid ^ " (CON)"
  | avid, CONF -> avid ^ " (CONF)"

let rec exp2str = function
  | E_INT i -> "E_INT (" ^ string_of_int i ^ ")"
  | E_BOOL b -> "E_BOOL (" ^ string_of_bool b ^ ")"
  | E_UNIT -> "E_UNIT"
  | E_PLUS -> "E_PLUS"
  | E_MINUS -> "E_MINUS"
  | E_MULT -> "E_MULT"
  | E_EQ -> "E_EQ"
  | E_NEQ -> "E_NEQ"
  | E_VID vid -> "E_VID (" ^ vid2string vid ^ ")"
  | E_FUN mrules -> "E_FUN " ^ String.concat " | " (List.map mrule2str mrules)
  | E_APP (expty1, expty2) ->
      "E_APP (" ^ expty2str expty1 ^ ", " ^ expty2str expty2 ^ ")"
  | E_PAIR (expty1, expty2) ->
      "E_PAIR (" ^ expty2str expty1 ^ ", " ^ expty2str expty2 ^ ")"
  | E_LET (dec, expty) -> "E_LET"

and expty2str (EXPTY (exp, _)) = exp2str exp

and mrule2str (M_RULE (patty, expty)) =
  patty2str patty ^ " => " ^ expty2str expty

and patty2str (PATTY (pat, _)) = pat2str pat

and pat2str = function
  | P_WILD -> "P_WILD"
  | P_INT i -> "P_INT (" ^ string_of_int i ^ ")"
  | P_BOOL b -> "P_BOOL (" ^ string_of_bool b ^ ")"
  | P_UNIT -> "P_UNIT"
  | P_VID vid -> "P_VID (" ^ vid2string vid ^ ")"
  | P_VIDP (vid, patty) ->
      "P_VIDP (" ^ vid2string vid ^ ", " ^ patty2str patty ^ ")"
  | P_PAIR (patty1, patty2) ->
      "P_PAIR (" ^ patty2str patty1 ^ ", " ^ patty2str patty2 ^ ")"

and venv2str venv =
  let venv_str =
    Dict.fold
      (fun acc (k, v) -> acc ^ " " ^ vid2string (k, VAR) ^ " -> " ^ loc2str v)
      "" venv
  in
  "ENV [" ^ venv_str ^ " ]"

and env2str (venv, count) =
  let venv_str =
    Dict.fold
      (fun acc (k, v) -> acc ^ " " ^ vid2string (k, VAR) ^ " -> " ^ loc2str v)
      "" venv
  in
  "ENV [" ^ venv_str ^ " ]" ^ " COUNT [" ^ string_of_int count ^ "]"

let match_fail_label = labelNewStr "MATCH_FAILURE"

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label -> loc -> Mono.pat -> Mach.code * env *)
let rec pat2code saddr faddr l pat =
  (match pat with
  | P_UNIT -> (cpre [ LABEL saddr ] code0, env0)
  | P_WILD -> (cpre [ LABEL saddr ] code0, (venv0, 1) (* why no env0? *))
  | P_INT i ->
      let code, rvalue = loc2rvalue l in
      let code' = clist [ JMPNEQ (ADDR (CADDR faddr), rvalue, INT i) ] in
      (cpre [ LABEL saddr ] (code @@ code'), env0)
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
      (cpre [ LABEL saddr ] (code @@ code'), env0)
  | P_BOOL false ->
      let code, rvalue = loc2rvalue l in
      let code' = clist [ JMPTRUE (ADDR (CADDR faddr), rvalue) ] in
      (cpre [ LABEL saddr ] (code @@ code'), env0)
  | P_VID (avid, VAR) ->
      let venv = Dict.insert (avid, l) venv0 in
      ( cpre
          [
            LABEL saddr;
            DEBUG ("Create VID " ^ vid2string (avid, VAR) ^ " -> " ^ loc2str l);
          ]
          code0,
        (venv, 1) )
  | P_VID (avid, CON) ->
      let code, rvalue = loc2rvalue l in
      let code' =
        match rvalue with
        | STR str when str = avid -> code0
        | STR _ -> clist [ JUMP (ADDR (CADDR faddr)) ]
        | _ -> clist [ JMPNEQSTR (ADDR (CADDR faddr), rvalue, STR avid) ]
      in
      (cpre [ LABEL saddr ] (code @@ code'), env0)
  | P_VIDP ((avid, CONF), patty) ->
      let code, (venv, count) =
        pat2code saddr faddr (L_DREF (l, 0)) (P_VID (avid, CON))
      and code', (venv', count') =
        patty2code (labelNewLabel saddr "_PAT") faddr (L_DREF (l, 1)) patty
      in
      ( cpre [ LABEL saddr ] (code @@ code'),
        (Dict.merge venv venv', count + count') )
  | P_VID _ | P_VIDP _ -> failwith "Parse must have been failed before"
  | P_PAIR (patty1, patty2) ->
      let code1, (venv1, count1) =
        patty2code (labelNewLabel saddr "_FST") faddr (L_DREF (l, 0)) patty1
      and code2, (venv2, count2) =
        patty2code (labelNewLabel saddr "_SND") faddr (L_DREF (l, 1)) patty2
      in
      ( cpre [ LABEL saddr ] (code1 @@ code2),
        (Dict.merge venv1 venv2, count1 + count2) ))
  |> fun (code, (venv, count)) ->
  ( [ DEBUG ("PAT_START " ^ pat2str pat) ]
    @@ code
    @@ [ DEBUG ("PAT_END   " ^ pat2str pat); DEBUG (venv2str venv) ],
    (venv, count) )

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code saddr faddr l (PATTY (pat, _)) = pat2code saddr faddr l pat

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
let rec exp2code ((venv, count) as env : env) (saddr : label) exp =
  (match exp with
  | E_INT i -> (code0, INT i)
  | E_BOOL b -> (code0, BOOL b)
  | E_UNIT -> (code0, UNIT)
  | E_APP (EXPTY (E_PLUS, _), EXPTY (E_PAIR (expty1, expty2), _)) ->
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_PLUS_FST") expty1
      in
      let code1_post = clist [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_PLUS_SND") expty2
      in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            ADD (LREG ax, REG ax, REG bx);
          ][@ocamlformat "disable"]
      in
      (code1 @@ code1_post @@ code2 @@ code2_post, REG ax)
  | E_APP (EXPTY (E_MINUS, _), EXPTY (E_PAIR (expty1, expty2), _)) ->
      let code_pre = clist [ PUSH (REG bx) ] in
      let code_post = clist [ POP (LREG bx) ] in
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_MINUS_FST") expty1
      in
      let code1_post = clist [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_MINUS_SND") expty2
      in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            SUB (LREG ax, REG ax, REG bx);
          ][@ocamlformat "disable"]
      in
      ( code_pre @@ code1 @@ code1_post @@ code2 @@ code2_post @@ code_post,
        REG ax )
  | E_APP (EXPTY (E_MULT, _), EXPTY (E_PAIR (expty1, expty2), _)) ->
      let code_pre = clist [ PUSH (REG bx) ] in
      let code_post = clist [ POP (LREG bx) ] in
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_MULT_FST") expty1
      in
      let code1_post = clist [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_MULT_SND") expty2
      in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            MUL (LREG ax, REG ax, REG bx);
          ][@ocamlformat "disable"]
      in
      ( code_pre @@ code1 @@ code1_post @@ code2 @@ code2_post @@ code_post,
        REG ax )
  | E_APP (EXPTY (E_EQ, _), EXPTY (E_PAIR (expty1, expty2), _)) ->
      let code_pre = clist [ PUSH (REG bx) ] in
      let code_post = clist [ POP (LREG bx) ] in
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_EQ_FST") expty1
      in
      let code1_post = clist [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_EQ_SND") expty2
      in
      let label_1 = labelNewLabel saddr "_EQ_1" in
      let label_2 = labelNewLabel saddr "_EQ_2" in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            JMPNEQ (ADDR (CADDR label_1), REG ax, REG bx);
            MOVE (LREG ax, BOOL true);
            JUMP (ADDR (CADDR label_2));
            LABEL label_1;
            MOVE (LREG ax, BOOL false);
            LABEL label_2;
          ][@ocamlformat "disable"]
      in
      ( code_pre @@ code1 @@ code1_post @@ code2 @@ code2_post @@ code_post,
        REG ax )
  | E_APP (EXPTY (E_NEQ, _), EXPTY (E_PAIR (expty1, expty2), _)) ->
      let code_pre = clist [ PUSH (REG bx) ] in
      let code_post = clist [ POP (LREG bx) ] in
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_NEQ_FST") expty1
      in
      let code1_post = clist [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_NEQ_SND") expty2
      in
      let label_1 = labelNewLabel saddr "_EQ_1" in
      let label_2 = labelNewLabel saddr "_EQ_2" in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            JMPNEQ (ADDR (CADDR label_1), REG ax, REG bx);
            MOVE (LREG ax, BOOL false);
            JUMP (ADDR (CADDR label_2));
            LABEL label_1;
            MOVE (LREG ax, BOOL true);
            LABEL label_2;
          ][@ocamlformat "disable"]
      in
      ( code_pre @@ code1 @@ code1_post @@ code2 @@ code2_post @@ code_post,
        REG ax )
  | E_PLUS | E_MINUS | E_MULT | E_EQ | E_NEQ -> failwith "should not match here"
  | E_VID (avid, VAR) -> (
      match Dict.lookup avid venv with
      | Some l ->
          let code, rvalue = loc2rvalue l in
          ( code
            @@ [
                 DEBUG
                   ("Retrieve VID "
                   ^ vid2string (avid, VAR)
                   ^ " -> " ^ loc2str l);
               ],
            rvalue )
      | None -> failwith ("Unknown avid: " ^ avid))
  | E_VID (avid, CON) -> (code0, STR avid)
  | E_VID (avid, CONF) ->
      let code =
        clist [
          MALLOC (LREG ax, INT 2);
          MOVE (LREFREG (ax, 0), STR avid)
        ][@ocamlformat "disable"]
      in
      (code, REG ax)
  | E_FUN mrules ->
      let env', code_ =
        match
          Dict.filter
            (fun (avid, l) ->
              let rec pred = function
                | L_REG r when r = bx -> true
                | L_DREF (L_REG r, _) when r = bx -> true
                | L_DREF (l, _) -> pred l
                | _ -> false
              in
              pred l)
            venv
        with
        | [ (avid, l) ] ->
            let code, rvalue = loc2rvalue l in
            let rec transform = function
              | L_REG r -> L_DREF (L_REG cp, count - 1)
              | L_DREF (L_REG r, i) -> L_DREF (L_DREF (L_REG cp, count - 1), i)
              | L_DREF (l, i) -> L_DREF (transform l, i)
              | _ -> failwith "should not match here"
            in
            let venv' = Dict.insert (avid, transform l) venv in
            let code' = clist [ MOVE (LREFREG (cp, count - 1), rvalue) ] in
            ((venv', count), code @@ code')
        | [] -> (env, code0)
        | xs ->
            failwith
              ("match must be unique: "
              ^ (List.map (fun (k, v) -> k ^ " -> " ^ loc2str v) xs
                |> String.concat ", "))
      in
      let fun_saddr = labelNewLabel saddr "_BEGIN_FUNC"
      and fun_eaddr = labelNewLabel saddr "_END_FUNC" in
      let code1, _, count' =
        List.fold_right
          (fun mrule (code_acc, faddr, count_acc) ->
            let saddr' = labelNewLabel saddr "_MRULE" in
            let code, extra_count = mrule2code env' saddr' faddr mrule in
            (code @@ code_acc, saddr', count_acc + extra_count))
          mrules
          (code0, match_fail_label, 0)
      in
      let code1' =
        clist [ JUMP (ADDR (CADDR fun_eaddr)); LABEL fun_saddr ]
        @@ code1 @@ clist [ LABEL fun_eaddr ]
      in
      let code2 =
        clist
          ([
             MALLOC (LREG ax, INT 2);
             MOVE (LREFREG (ax, 0), ADDR (CADDR fun_saddr));
             MALLOC (LREG bx, INT (count + count'));
             MOVE (LREFREG (ax, 1), REG bx);
           ]
          @ init count (fun n -> MOVE (LREFREG (bx, n), REFREG (cp, n))))
      in
      (code_ @@ code1' @@ code2, REG ax)
  | E_APP (expty1, expty2) ->
      let code1_pre = clist [ PUSH (REG bx) ] in
      let code1, rvalue1 =
        expty2code env (labelNewLabel saddr "_APP_FST") expty1
      in
      let code1_post = [ PUSH rvalue1 ] in
      let code2, rvalue2 =
        expty2code env (labelNewLabel saddr "_APP_SND") expty2
      in
      let code2_post =
        clist
          [
            MOVE (LREG bx, rvalue2);
            POP (LREG ax);
            PUSH (REG cp);
            MOVE (LREG cp, REFREG (ax, 1));
            CALL (REFREG (ax, 0));
            (* FREE (REG cp); *)
            (* Should not free since it may be reused on other function call *)
            POP (LREG cp);
            POP (LREG bx);
          ]
      in
      (code1_pre @@ code1 @@ code1_post @@ code2 @@ code2_post, REG ax)
  | E_PAIR (expty1, expty2) ->
      let saddr1 = labelNewLabel saddr "_FST" in
      let saddr2 = labelNewLabel saddr "_SND" in
      let code1, rvalue1 = expty2code env saddr1 expty1 in
      let code2, rvalue2 = expty2code env saddr2 expty2 in
      let code_mid = clist [ PUSH rvalue1 ] in
      let code_post =
        clist
          ((match rvalue2 with
           | REG r when r = bx -> []
           | _ -> [ MOVE (LREG bx, rvalue2) ])
          @ [
              MALLOC (LREG ax, INT 2);
              MOVE (LREFREG (ax, 1), REG bx);
              POP (LREG bx);
              MOVE (LREFREG (ax, 0), REG bx);
            ])
      in
      (code1 @@ code_mid @@ code2 @@ code_post, REG ax)
  | E_LET (dec, expty) ->
      let _, count = env in
      let saddr' = labelNewLabel saddr "_LETEXP" in
      let code1, ((_, count1) as env1) = dec2code env saddr dec in
      let code2, rvalue = expty2code env1 saddr' expty in
      let code_pre =
        clist
          ([
            MOVE (LREG ax, REG cp);
            MALLOC (LREG cp, INT count1)
          ][@ocamlformat "disable"]
          @ init count (fun n -> MOVE (LREFREG (cp, n), REFREG (ax, n)))
          @ [ PUSH (REG ax) ])
      and code_post =
        clist
          ((match rvalue with
           | REG r when r = ax -> []
           | _ -> [ MOVE (LREG ax, rvalue) ])
          @ [ FREE (REG cp); POP (LREG cp) ])
      in
      (code_pre @@ code1 @@ code2 @@ code_post, REG ax))
  |> fun (code, rvalue) ->
  ( [ DEBUG ("START " ^ exp2str exp); DEBUG (env2str env) ]
    @@ code
    @@ [ DEBUG ("END   " ^ exp2str exp) ],
    rvalue )

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
and expty2code env saddr (EXPTY (exp, _)) = exp2code env saddr exp

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code env saddr = function
  | D_VAL (patty, expty) ->
      let venv, count = env in
      let code1, rvalue =
        expty2code env (labelNewLabel saddr "_VAL_EXP") expty
      in
      let code3, (venv', count') =
        patty2code
          (labelNewLabel saddr "_VAL_PAT")
          match_fail_label
          (L_DREF (L_REG cp, count))
          patty
      in
      let code2 = clist [ MOVE (LREFREG (cp, count), rvalue) ] in
      let env' = (Dict.merge venv venv', count + count') in
      (cpre [ LABEL saddr ] code1 @@ code2 @@ code3, env')
  | D_REC ((PATTY (P_VID (avid, VAR), _) as patty), expty) ->
      let venv, count = env in
      let code3, (venv', count') =
        patty2code
          (labelNewLabel saddr "_VAL_PAT")
          match_fail_label
          (L_DREF (L_REG cp, count))
          patty
      in
      let env' = (Dict.merge venv venv', count + count') in
      let code1, rvalue =
        expty2code env' (labelNewLabel saddr "_VAL_EXP") expty
      in
      let code1_post = clist [ MOVE (LREFREG (cp, count), rvalue) ] in
      let l =
        match Dict.lookup avid venv' with
        | Some l -> l
        | None -> failwith "match should not fail"
      in
      let code2_pre, rvalue' = loc2rvalue l in
      let code2 =
        clist
          [
            MOVE (LREG ax, rvalue');
            MOVE (LREG ax, REFREG (ax, 1));
            MOVE (LREFREG (ax, count), rvalue');
          ]
      in
      ( cpre [ LABEL saddr ] code1 @@ code1_post @@ code2_pre @@ code2 @@ code3,
        env' )
  | D_REC _ -> failwith "D_REC should be P_VID (VAR)"
  | D_DTYPE -> raise NotImplemented

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code * extra-count *)
and mrule2code env saddr faddr (M_RULE (patty, expty)) =
  let venv, count = (env : env) in
  let code1, (venv', count') =
    patty2code (labelNewLabel saddr "_PAT") faddr (L_REG bx) patty
  in
  let env' = (Dict.merge venv venv', count + count')
  and saddr' = labelNewLabel saddr "_EXP" in
  let code2, rvalue = expty2code env' saddr' expty in
  ( cpre [ LABEL saddr ] code1 @@ cpost code2 [ MOVE (LREG ax, rvalue); RETURN ],
    count' )

(* program2code : Mono.program -> Mach.code *)
let program2code ((dlist, et) : Mono.program) =
  let code1, ((_, count) as env) =
    List.fold_left
      (fun (code_acc, env_acc) dec ->
        let code, env = dec2code env_acc (labelNewStr "DEC") dec in
        (code_acc @@ code, env))
      (code0, env0) dlist
  in
  let code2, rvalue = expty2code env (labelNewStr "PRGEXP") et in
  let halt =
    clist
      ((match rvalue with
       | REFADDR _ | REFREG _ ->
           [ MOVE (LREG ax, rvalue); FREE (REG cp); HALT (REG ax) ]
       | _ -> [ FREE (REG cp); HALT rvalue ])
      @ [ LABEL match_fail_label; EXCEPTION ])
  in
  cpre [ LABEL start_label; MALLOC (LREG cp, INT count) ] code1 @@ code2 @@ halt
