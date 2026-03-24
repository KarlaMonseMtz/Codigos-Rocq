(* Nombre: Karla Monserratt Martínez López 
  Tesis: De programas a demostraciones: El camino desde el cálculo lambda 
  hasta la verificación formal moderna.

Este archivo muestra como definir a los números binarios y algunos teoremas
y ejemplos. Además de definir las conversiones números naturales a binarios 
y viceversa. También para extraer el código en Haskell
       *)

(*Definición iductiva de los números naturales*)
Inductive bin : Type :=
  | Z                     (* Representa al numero 0*)
  | B0 (n : bin)          (* Representa el bit 0*)
  | B1 (n : bin).         (*Representa el bit 1*)


(*Hace los incrementos de forma recursiva*)
Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z               (*El sucesor del 0 el 1 *)
  | B0 n => B1 n            (* Al incrementarlo va a pasar por el numero 1*)
  | B1 n => B0 (incr n)     (* El incremento del 0 es 1 y al n lo incrementamos*)
  end.

(* Transforma los binarios en números naturales*)
Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B0 n => 2 * (bin_to_nat n)      (* bit 0: multiplicar por 2 *)
  | B1 n => 1 + 2 * (bin_to_nat n)  (* bit 1: multiplicar por 2 y sumar 1 *)
  end.


Eval compute in bin_to_nat (B1 (B0 (B1 (B1 Z)))).

(* Ejemplos de las funciones anteriores*)
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  simpl.  (* Esto reduce incr (B₁ Z) a B₀ (incr Z) *)
  simpl.  (* Esto reduce incr Z a B₁ Z *)
  reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  reflexivity.
Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr7 : bin_to_nat (B0 (B0 (B0 (B1 Z)))) = 8.
Proof.
  simpl.
  reflexivity.
Qed.

(*Teorema que prueba que incrementar un número en su representación binaria
y luego interpretarlo como un número natural produce el mismo resultado que 
sumarle 1 a su interpretación original. *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b.
- simpl incr. simpl bin_to_nat. reflexivity.
- simpl incr. simpl bin_to_nat. simpl. reflexivity.
- simpl incr.  simpl bin_to_nat. 
  simpl. 
rewrite IHb. simpl. 
(* S (a + S b) = S ( S (a + b)) *)
(* Cualquiera de las siguientes funciona *)
rewrite <- plus_n_Sm.
(*rewrite (plus_n_Sm (bin_to_nat b) (bin_to_nat b + 0)).
 *)
reflexivity.
Qed.

(*Transforma un natural a binario *)
Fixpoint nat_to_bin (n : nat): bin:=
  match n with 
  | 0=> Z
  | S n' => incr (nat_to_bin n')
end.

(* Ejemplo de la definición*)
Eval compute in nat_to_bin 8.

(*Teorema que demuestra que si tomamos un número natural, lo convertimos a su
representación binaria y luego interpretamos esa representación, obtenemos 
el número original  *)
Theorem nat_bin_nat : forall n, bin_to_nat(nat_to_bin n)= n.
Proof.
  intros n.
  induction n.
- simpl nat_to_bin. simpl bin_to_nat. reflexivity.
- simpl nat_to_bin. rewrite bin_to_nat_pres_incr. rewrite IHn. simpl. reflexivity.
Qed.
(* Extraccion a Haskell*)

From Coq Require Extraction. (*biblioteca para extraer*)
From Coq Require ExtrHaskellBasic. 
Set Extraction Output Directory ".".
Extraction Language Haskell.

Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ]. (*pares*)
Extract Inductive sum => 
"Prelude.Either"  [ "Prelude.Left" "Prelude.Right" ]. (*sumas*)
Extract Inductive nat => 
"Prelude.Int" [ "0" "Prelude.succ" ] "(\fO fS n -> if n Prelude.== 0 then fO () else fS (Prelude.pred n))".
(*funcion recursiva sobre naturales/int*)

Extract Constant plus => "(Prelude.+)".
Extract Constant andb => "(Prelude.&&)".
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".

(* Extract Inductive bin => "bins" [ "zero" "bzero" "bone" ]. *)

Extraction "binarios.hs" bin incr bin_to_nat nat_to_bin nat_bin_nat.


