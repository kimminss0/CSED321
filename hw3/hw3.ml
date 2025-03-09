open Common

exception NotImplemented
exception IllegalFormat

module Integer : SCALAR with type t = int = struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1
  let ( ++ ) x y = x + y
  let ( ** ) x y = x * y
  let ( == ) x y = x = y
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool = struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true
  let ( ++ ) x y = x || y
  let ( ** ) x y = x && y
  let ( == ) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t = struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create xs = if xs = [] then raise VectorIllegal else xs
  let to_list xs = xs
  let dim xs = List.length xs

  let nth xs n =
    match List.nth_opt xs n with None -> raise VectorIllegal | Some x -> x

  let ( ++ ) xs ys =
    if List.compare_lengths xs ys <> 0 then raise VectorIllegal else xs @ ys

  let ( == ) xs ys =
    if List.compare_lengths xs ys <> 0 then raise VectorIllegal else xs = ys

  let innerp xs ys =
    if List.compare_lengths xs ys <> 0 then raise VectorIllegal
    else List.fold_left Scal.( ++ ) Scal.zero (List.map2 Scal.( ** ) xs ys)
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t = struct
  type elem = Scal.t
  type t = elem list list

  exception MatrixIllegal

  let create mat =
    let dim = List.length mat in
    let pred = fun l -> List.compare_length_with l dim = 0 in
    if dim > 0 && List.for_all pred mat then mat else raise MatrixIllegal

  let identity dim =
    if dim <= 0 then raise MatrixIllegal
    else
      List.init dim (fun n ->
          List.init dim (fun k -> if k = n then Scal.one else Scal.zero))

  let dim mat = List.length mat

  let transpose mat =
    List.init (dim mat) (fun j -> List.map (fun row -> List.nth row j) mat)

  let to_list mat = mat

  let get m r c =
    let n = dim m in
    if r < 0 || r >= n || c < 0 || c >= n then raise MatrixIllegal
    else List.nth (List.nth m r) c

  let ( ++ ) m m' =
    if dim m <> dim m' then raise MatrixIllegal
    else List.map2 (List.map2 Scal.( ++ )) m m'

  module ScalVector = VectorFn (Scal)

  let ( ** ) m m' =
    if dim m <> dim m' then raise MatrixIllegal
    else
      let m't = transpose m' in
      List.map
        (fun row ->
          List.map
            (fun col -> ScalVector.(innerp (create row) (create col)))
            m't)
        m

  let ( == ) m m' =
    try List.for_all2 (fun r r' -> ScalVector.(create r == create r')) m m'
    with ScalVector.VectorIllegal -> raise MatrixIllegal
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) : sig
  val closure : Mat.t -> Mat.t
end = struct
  let closure m =
    let ident = Mat.(identity (dim m)) in
    let rec go c =
      let c' = Mat.(ident ++ (c ** m)) in
      if Mat.(c == c') then c else go c'
    in
    go ident
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach adj =
  try BoolMat.create adj |> BoolMatClosure.closure |> BoolMat.to_list
  with BoolMat.MatrixIllegal -> raise IllegalFormat

let al =
  [
    [ true; false; false; false; false; false ];
    [ false; true; true; true; false; false ];
    [ false; true; true; false; true; false ];
    [ false; true; false; true; true; true ];
    [ false; false; true; true; true; false ];
    [ false; false; false; true; false; true ];
  ]

let solution_al' =
  [
    [ true; false; false; false; false; false ];
    [ false; true; true; true; true; true ];
    [ false; true; true; true; true; true ];
    [ false; true; true; true; true; true ];
    [ false; true; true; true; true; true ];
    [ false; true; true; true; true; true ];
  ]

module Distance : SCALAR with type t = int = struct
  type t = int

  exception ScalarIllegal

  let zero = -1
  let one = 0
  let check_valid x y = if x < -1 || y < -1 then raise ScalarIllegal

  let ( ++ ) x y =
    check_valid x y;
    match (x, y) with -1, _ -> y | _, -1 -> x | _ -> min x y

  let ( ** ) x y =
    check_valid x y;
    if x = -1 || y = -1 then -1 else x + y

  let ( == ) x y =
    check_valid x y;
    x = y
end

(* .. Write some code here .. *)

module DistanceMat = MatrixFn (Distance)
module DistanceMatClosure = ClosureFn (DistanceMat)

let distance adj =
  try
    DistanceMat.create adj |> DistanceMatClosure.closure |> DistanceMat.to_list
  with DistanceMat.MatrixIllegal -> raise IllegalFormat

let dl =
  [
    [ 0; -1; -1; -1; -1; -1 ];
    [ -1; 0; 35; 200; -1; -1 ];
    [ -1; 50; 0; -1; 150; -1 ];
    [ -1; 75; -1; 0; 100; 25 ];
    [ -1; -1; 50; 65; 0; -1 ];
    [ -1; -1; -1; -1; -1; 0 ];
  ]

let solution_dl' =
  [
    [ 0; -1; -1; -1; -1; -1 ];
    [ -1; 0; 35; 200; 185; 225 ];
    [ -1; 50; 0; 215; 150; 240 ];
    [ -1; 75; 110; 0; 100; 25 ];
    [ -1; 100; 50; 65; 0; 90 ];
    [ -1; -1; -1; -1; -1; 0 ];
  ]

module Weight : SCALAR with type t = int = struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = -1
  let check_valid x y = if x < -1 || y < -1 then raise ScalarIllegal

  let ( ++ ) x y =
    check_valid x y;
    match (x, y) with -1, _ | _, -1 -> -1 | _ -> max x y

  let ( ** ) x y =
    check_valid x y;
    match (x, y) with
    | -1, _ -> y
    | _, -1 -> x
    | _ -> min x y

  let ( == ) x y =
    check_valid x y;
    x = y
end

(* .. Write some code here .. *)

module WeightMat = MatrixFn (Weight)
module WeightMatClosure = ClosureFn (WeightMat)

let weight adj =
  try WeightMat.create adj |> WeightMatClosure.closure |> WeightMat.to_list
  with WeightMat.MatrixIllegal -> raise IllegalFormat

let ml =
  [
    [ -1; 0; 0; 0; 0; 0 ];
    [ 0; -1; 10; 100; 0; 0 ];
    [ 0; 50; -1; 0; 150; 0 ];
    [ 0; 75; 0; -1; 125; 40 ];
    [ 0; 0; 25; -1; -1; 0 ];
    [ 0; 0; 0; 0; 0; -1 ];
  ]

let solution_ml' =
  [
    [ -1; 0; 0; 0; 0; 0 ];
    [ 0; -1; 25; 100; 100; 40 ];
    [ 0; 75; -1; 150; 150; 40 ];
    [ 0; 75; 25; -1; 125; 40 ];
    [ 0; 75; 25; -1; -1; 40 ];
    [ 0; 0; 0; 0; 0; -1 ];
  ]

let _ =
  try
    if
      reach al = solution_al'
      && distance dl = solution_dl'
      && weight ml = solution_ml'
    then print_endline "\nYour program seems fine (but no guarantee)!"
    else print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!"
