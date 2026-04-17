
(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::ls' -> succ (length ls')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app ls1 ls2 =
  match ls1 with
  | [] -> ls2
  | x::ls1' -> x::(app ls1' ls2)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev l = match l with
| [] -> l
| h::t -> app (rev t) (h::[])
