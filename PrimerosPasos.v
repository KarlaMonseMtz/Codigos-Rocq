(* Nombre:Karla Monserratt Martínez López 
    Tesis: De programas a demostraciones: El camino desde el cálculo lambda 
    hasta la verificación formal moderna.
*)


(* Check se utliza para verificar los tipos *)
Check nat. (* nat: Set *)
Check Set. (* Set:Type *)
Check true. (*  true: bool  *)
Check false.  (* false:bool *)
Check bool.    (* bool: Set *)

(* comparación con el cálculo lambda simplmenete tipado *)

(*Definición de la función identidad para naturales y booleanos *)
Definition identidad_nat (x : nat) : nat := x.
Definition identidad_bool (x : bool) : bool := x.

(* Eval sirve para evaluar como lo que se hace con la beta reducción *)
Eval compute in identidad_nat 120.      (* 5 : nat *)
Eval compute in identidad_bool true.  (* true : bool *)
(* Si se coloca compute identidad_nat true. debe marcar error*)


(*Función identidad en el cálculo polimorfico*)
Definition id : forall (A : Type), A -> A :=
  fun (A : Type) (x : A) => x.

(*  Evaluar usando la función identidad del cálculo polimórfico *)
Eval compute in id nat 120.      (* 5 : nat *)
Eval compute in id bool true.    (* true : bool*)