open Fjava

exception NotImplemented
exception TypeError
exception Stuck

module Method = struct
  let ret_type ((ret_type, _, _, _) : methodDecl) = ret_type
  let name ((_, name, _, _) : methodDecl) = name
  let params ((_, _, params, _) : methodDecl) = params
  let body ((_, _, _, body) : methodDecl) = body
end

module Constructor = struct
  let name ((name, _, _, _) : constructorDecl) = name
  let params ((_, params, _, _) : constructorDecl) = params
  let super_args ((_, _, super_args, _) : constructorDecl) = super_args
  let assignments ((_, _, _, assignments) : constructorDecl) = assignments
end

module Class = struct
  let name ((name, _, _, _, _) : classDecl) = name
  let super_type ((_, super_type, _, _, _) : classDecl) = super_type
  let fields ((_, _, fields, _, _) : classDecl) = fields
  let ctor ((_, _, _, ctor, _) : classDecl) = ctor
  let methods ((_, _, _, _, methods) : classDecl) = methods
end

module Program = struct
  let classes ((classes, _) : program) = classes
  let exp ((_, exp) : program) = exp
end

module Classes = struct
  let classDeclOf classes typ =
    List.find (fun cls -> Class.name cls = typ) classes

  let rec fields classes (typ : typ) : (typ * string) list =
    let rec fields' typ =
      match typ with
      | "Object" -> []
      | _ ->
          let cls = classDeclOf classes typ in
          let sup_typ = Class.super_type cls in
          fields' sup_typ @ Class.fields cls
    in
    fields' typ

  let rec mtype classes method_name (typ : typ) =
    let cls = classDeclOf classes typ in
    let methods = Class.methods cls in
    match
      List.find_opt (fun method' -> Method.name method' = method_name) methods
    with
    | Some method' ->
        (List.map fst (Method.params method'), Method.ret_type method')
    | None -> mtype classes method_name (Class.super_type cls)

  let rec isSubtype classes sub sup =
    match sub with
    | _ when sub = sup -> true
    | "Object" -> false
    | _ -> isSubtype classes (Class.super_type (classDeclOf classes sub)) sup

  let override classes method_name typ_d (method_arg_types, method_ret_type) =
    let method_arg_types', method_ret_type' = mtype classes method_name typ_d in
    List.for_all2 ( = ) method_arg_types method_arg_types'
    && method_ret_type = method_ret_type'
end

module Env = Map.Make (String)

type env = typ Env.t

let typeOf (classes, exp) =
  let rec typeOf' (env : env) = function
    | Var v -> (
        try Env.find v env with Not_found -> raise TypeError (* T-Var *))
    | Field (e, f) ->
        let fields = Classes.fields classes (typeOf' env e) in
        List.find (fun (typ, name) -> name = f) fields |> fst (* T-Field *)
    | Method (e, m, args) ->
        let exp_typ = typeOf' env e in
        let arg_types_sup, ret_type = Classes.mtype classes m exp_typ in
        let arg_types_sub = List.map (fun e' -> typeOf' env e') args in
        if
          List.for_all2
            (fun sub sup -> Classes.isSubtype classes sub sup)
            arg_types_sub arg_types_sup
        then ret_type
        else raise TypeError (* T-Invk*)
    | New (t, args) ->
        let fields = Classes.fields classes t in
        let arg_types_sup = List.map fst fields in
        let arg_types_sub = List.map (fun arg -> typeOf' env arg) args in
        if
          List.for_all2
            (fun sub sup -> Classes.isSubtype classes sub sup)
            arg_types_sub arg_types_sup
        then t
        else raise TypeError (* T-New *)
    | Cast (t, e) ->
        let type_exp = typeOf' env e in
        if Classes.isSubtype classes type_exp t then t (* T-UCast *)
        else if Classes.isSubtype classes t type_exp then t (* T-DCast *)
        else
          let _ = print_endline "Stupid Warning" in
          t (* T-SCast *)
  and isMethodValid method' typ_c =
    let cls = Classes.classDeclOf classes typ_c in
    let params = Method.params method' in
    let env =
      List.fold_left
        (fun (env : env) (typ, string) -> Env.add string typ env)
        Env.empty params
      |> Env.add "this" typ_c
    in
    let exp_e0 = Method.body method' in
    let typ_c0 = Method.ret_type method' in
    let typ_e0 = typeOf' env exp_e0 in
    let typ_d = Class.super_type cls in
    let typ_cs = List.split params |> fst in
    Classes.isSubtype classes typ_e0 typ_c0
    && Classes.override classes (Method.name method') typ_d (typ_cs, typ_c0)
  and isClassValid typ_c =
    let cls = Classes.classDeclOf classes typ_c in
    let typ_d = Class.super_type cls in
    let ctor = Class.ctor cls in
    let typ_c' = Constructor.name ctor in
    let super_args_g = Constructor.super_args ctor in
    let typ_ds =
      Constructor.params ctor
      |> List.filter (fun (_typ, name) ->
             List.exists (fun name' -> name = name') super_args_g)
      |> List.map fst
    in
    let fields = Classes.fields classes typ_d in
    let fields' = List.combine typ_ds super_args_g in
    let methods = Class.methods cls in
    typ_c = typ_c'
    && List.length fields = List.length fields'
    && List.for_all2
         (fun (typ, name) (typ', name') -> typ = typ' && name = name')
         fields fields'
    && List.for_all (fun method' -> isMethodValid method' typ_c) methods
  in
  List.iter
    (fun cls ->
      let typ_c = Class.name cls in
      if not (isClassValid typ_c) then raise TypeError)
    classes;
  typeOf' Env.empty exp

let step p = raise NotImplemented
let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
  let rec steps e =
    match stepOpt e with
    | None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in
  Stream.icons e (steps e)
