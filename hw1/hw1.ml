exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n = if n = 0 then 0 else sum (n - 1) + n
let rec power x n = if n = 0 then 1 else x * power x (n - 1)
let rec gcd m n = if m = 0 then n else gcd (n mod m) m

let rec combi n k =
  if k = 0 then 1
  else if k > n - k then combi n (n - k)
  else combi n (k - 1) * (n - k + 1) / k

let rec sum_tree t =
  match t with Leaf v -> v | Node (l, v, r) -> sum_tree l + v + sum_tree r

let rec depth t =
  match t with Leaf _ -> 0 | Node (l, _, r) -> 1 + max (depth l) (depth r)

let rec bin_search t v =
  match t with
  | Leaf u -> v = u
  | Node (l, u, r) ->
      if v = u then true else if v < u then bin_search l v else bin_search r v

let rec postorder t =
  match t with
  | Leaf v -> [ v ]
  | Node (l, v, r) -> postorder l @ postorder r @ [ v ]

let rec max l =
  match l with
  | [] -> 0
  | [ x ] -> x
  | x :: xt ->
      let t = max xt in
      if x > t then x else t

let rec list_add xs ys =
  match (xs, ys) with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xt, y :: yt -> (x + y) :: list_add xt yt

let rec insert m l =
  match l with
  | [] -> [ m ]
  | v :: vt -> if m < v then m :: l else v :: insert m vt

let rec insort l =
  let rec go xs ys =
    match ys with [] -> xs | y :: yt -> go (insert y xs) yt
  in
  go [] l

let rec compose f g x = g (f x)
let rec curry f a b = f (a, b)
let rec uncurry f (a, b) = f a b
let rec multifun f n = if n = 1 then f else compose f (multifun f (n - 1))

let rec ltake l n =
  match (l, n) with _, 0 | [], _ -> [] | v :: vt, _ -> v :: ltake vt (n - 1)

let rec lall f l = match l with [] -> true | x :: xt -> f x && lall f xt
let rec lmap f l = match l with [] -> [] | x :: xt -> f x :: lmap f xt
let rec lrev l = match l with [] -> [] | x :: xt -> lrev xt @ [ x ]
let rec lflat l = match l with [] -> [] | x :: xt -> x @ lflat xt

let rec lzip xs ys =
  match (xs, ys) with
  | [], _ | _, [] -> []
  | x :: xt, y :: yt -> (x, y) :: lzip xt yt

let rec split l =
  match l with
  | [] -> ([], [])
  | [ x ] -> ([ x ], [])
  | x :: y :: l' ->
      let xs, ys = split l' in
      (x :: xs, y :: ys)

let rec cartprod xs ys =
  match xs with
  | [] -> []
  | x :: xt -> lmap (fun y -> (x, y)) ys @ cartprod xt ys

let rec powerset l =
  match l with
  | [] -> [ [] ]
  | x :: xt ->
      let p = powerset xt in
      p @ lmap (fun x' -> x :: x') p
