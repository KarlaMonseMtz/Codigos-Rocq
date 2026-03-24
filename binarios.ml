
(** val add : int -> int -> int **)

let rec add n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun p -> succ (add p m))
    n

(** val mul : int -> int -> int **)

let rec mul n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun p -> add m (mul p m))
    n

type bin =
| Z
| B0 of bin
| B1 of bin

(** val incr : bin -> bin **)

let rec incr = function
| Z -> B1 Z
| B0 n -> B1 n
| B1 n -> B0 (incr n)

(** val bin_to_nat : bin -> int **)

let rec bin_to_nat = function
| Z -> 0
| B0 n -> mul (succ (succ 0)) (bin_to_nat n)
| B1 n -> add (succ 0) (mul (succ (succ 0)) (bin_to_nat n))

(** val nat_to_bin : int -> bin **)

let rec nat_to_bin n =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> Z)
    (fun n' -> incr (nat_to_bin n'))
    n
