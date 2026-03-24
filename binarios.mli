
val add : int -> int -> int

val mul : int -> int -> int

type bin =
| Z
| B0 of bin
| B1 of bin

val incr : bin -> bin

val bin_to_nat : bin -> int

val nat_to_bin : int -> bin
