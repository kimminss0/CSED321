exception NotImplemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

(** Recursive functions **)

let rec lrevrev xs =
  let rec lrev ys = match ys with [] -> [] | y :: yt -> lrev yt @ [ y ] in
  match xs with [] -> [] | x :: xt -> lrevrev xt @ [ lrev x ]

let rec lfoldl f acc l =
  match l with [] -> acc | x :: xt -> lfoldl f (f (x, acc)) xt

(** Tail recursive functions **)

let fact n =
  let rec go m acc = match m with 0 -> acc | _ -> go (m - 1) (m * acc) in
  go n 1

let fib n =
  let rec go m acc1 acc2 =
    match m with 0 -> acc1 | _ -> go (m - 1) (acc2 + acc1) acc1
  in
  go n 1 0

let alterSum l =
  let rec go xs acc k =
    match xs with
    | [] -> acc
    | x :: xt ->
        let op = if k then ( + ) else ( - ) in
        go xt (op acc x) (not k)
  in
  go l 0 true

let ltabulate n f =
  let rec go m l = match m with 0 -> l | _ -> go (m - 1) (f (m - 1) :: l) in
  go n []

let lfilter p l =
  let rec go xs sats =
    match xs with
    | [] -> sats
    | x :: xt -> go xt (if p x then sats @ [ x ] else sats)
  in
  go l []

let rec union s t =
  match s with
  | [] -> t
  | x :: xt -> union xt (if lfilter (( = ) x) t = [] then x :: t else t)

let inorder t =
  let rec go ts post =
    match ts with
    | [] -> post
    | Leaf v :: ttail -> go ttail (post @ [ v ])
    | Node (l, v, r) :: ttail -> go (l :: Leaf v :: r :: ttail) post
  in
  go [ t ] []

let postorder t =
  let rec go ts post =
    match ts with
    | [] -> post
    | Leaf v :: ttail -> go ttail (post @ [ v ])
    | Node (l, v, r) :: ttail -> go (l :: r :: Leaf v :: ttail) post
  in
  go [ t ] []

let preorder t =
  let rec go ts post =
    match ts with
    | [] -> post
    | Leaf v :: ttail -> go ttail (post @ [ v ])
    | Node (l, v, r) :: ttail -> go (Leaf v :: l :: r :: ttail) post
  in
  go [ t ] []

(** Sorting in the ascending order **)

let rec quicksort l =
  match l with
  | [] -> []
  | p :: xt ->
      let rec partition xs ls hs =
        match xs with
        | [] -> (ls, hs)
        | x :: xt ->
            if x < p then partition xt (x :: ls) hs
            else partition xt ls (x :: hs)
      in
      let ls, hs = partition xt [] [] in
      quicksort ls @ [ p ] @ quicksort hs

let rec mergesort l =
  match l with
  | [] | [ _ ] -> l
  | _ ->
      let rec split l xs ys =
        match l with
        | [] -> (xs, ys)
        | [ x ] -> (x :: xs, ys)
        | x :: y :: t -> split t (x :: xs) (y :: ys)
      in
      let rec merge xs ys =
        match (xs, ys) with
        | [], ys -> ys
        | xs, [] -> xs
        | x :: xt, y :: yt ->
            if x < y then x :: merge xt ys else y :: merge xs yt
      in
      let xs, ys = split l [] [] in
      merge (mergesort xs) (mergesort ys)

(** Structures **)

module type HEAP = sig
  exception InvalidLocation

  type loc
  type 'a heap

  val empty : unit -> 'a heap
  val allocate : 'a heap -> 'a -> 'a heap * loc
  val dereference : 'a heap -> loc -> 'a
  val update : 'a heap -> loc -> 'a -> 'a heap
end

module type DICT = sig
  type key
  type 'a dict

  val empty : unit -> 'a dict
  val lookup : 'a dict -> key -> 'a option
  val delete : 'a dict -> key -> 'a dict
  val insert : 'a dict -> key * 'a -> 'a dict
end

module Heap : HEAP = struct
  exception InvalidLocation

  type loc = int
  type 'a heap = 'a list

  let empty () = []

  let allocate h v =
    let size = List.length h in
    (h @ [ v ], size)

  let dereference h loc =
    match List.nth_opt h loc with None -> raise InvalidLocation | Some v -> v

  let update h loc v =
    match List.nth_opt h loc with
    | None -> raise InvalidLocation
    | Some _ ->
        let _, h' =
          List.fold_left_map
            (fun acc v' -> (acc + 1, if acc = loc then v else v'))
            0 h
        in
        h'
end

module DictList : DICT with type key = string = struct
  type key = string
  type 'a dict = (key * 'a) list

  let empty () = []
  let lookup d k = List.assoc_opt k d
  let delete d k = List.remove_assoc k d
  let insert d (k, v) = (k, v) :: delete d k
end

module DictFun : DICT with type key = string = struct
  type key = string
  type 'a dict = key -> 'a option

  let empty () = fun _ -> None
  let lookup d k = d k
  let delete d k = fun k' -> if k' = k then None else d k'
  let insert d (k, v) = fun k' -> if k' = k then Some v else d k'
end
