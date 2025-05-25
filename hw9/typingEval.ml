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

let typeOf p = raise NotImplemented
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
