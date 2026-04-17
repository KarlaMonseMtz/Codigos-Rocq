
module Nat =
 struct
  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n
 end

(** val nilN : int list **)

let nilN =
  []

(** val insert : int -> int list -> int list **)

let rec insert x = function
| [] -> x::nilN
| y::l' -> if Nat.leb x y then x::(y::l') else y::(insert x l')

(** val insertsort : int list -> int list **)

let rec insertsort = function
| [] -> nilN
| x::l' -> insert x (insertsort l')

(** val sort : int list -> int list **)

let sort =
  insertsort

type ordenada =
| Ord_nil
| Ord_single of int
| Ord_cons of int * int * int list * ordenada

(** val insert_ordenada : int -> int list -> ordenada -> ordenada **)

let rec insert_ordenada x  = function
| Ord_nil -> Ord_single x
| Ord_single x0 ->
  let b = Nat.leb x x0 in
  if b
  then Ord_cons (x, x0, nilN, (Ord_single x0))
  else Ord_cons (x0, x, nilN, (Ord_single x))
| Ord_cons (x0, y, l, o0) ->
  let b = Nat.leb x x0 in
  if b
  then Ord_cons (x, x0, (y::l), (Ord_cons (x0, y, l, o0)))
  else let b0 = Nat.leb x y in
       if b0
       then Ord_cons (x0, x, (y::l), (Ord_cons (x, y, l, o0)))
       else Ord_cons (x0, y, (insert x l), (insert_ordenada x o0))

(** val insertsort_ordenada : int list -> ordenada **)

let rec insertsort_ordenada = function
| [] -> Ord_nil
| y::l0 -> insert_ordenada y (insertsort_ordenada l0)
