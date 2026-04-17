(* Nombre: Karla Monserratt Martínez López 
  Tesis: De programas a demostraciones: El camino desde el cálculo lambda 
  hasta la verificación formal moderna.

Este archivo muestra como definir las listas y algunos teoremas importantes
y ejemplos. Además de el ordenamiento por inserción. 
También la extración para Haskell.
       *)

From Coq Require Import List Int.
Import ListNotations.
Require Import PeanoNat.

Set Implicit Arguments. 

(* Definición polimorfica de listas *)
Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

(* Definición de la longitud de las listas *)
Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil _ => O
  | Cons _ ls' => S (length ls')
  end.

(* Definición que junta dos listas *)
Fixpoint app T (ls1 ls2 : list T) : list T :=
match ls1 with
| Nil _ => ls2
| Cons x ls1' => Cons x (app ls1' ls2 )
end.


(* Teorema que demuestra la longitud de la concatenación de dos listas
es igual a la suma de sus longitudes individuales. *)
Theorem length_app : 
  forall T (ls1 ls2 : list T), 
    length (app ls1 ls2 ) = plus (length ls1 ) (length ls2 ).
Proof. 
intros T ls1 ls2.
induction ls1.
- simpl. reflexivity.
- simpl. rewrite IHls1. reflexivity.
Qed.

(* Teorema que agrega una lista vacía al final no debería cambiar
la lista original *)
Theorem app_nil_r : forall T (l : list T),
  app l (Nil T) = l.
Proof.
intros T l.
induction l.
-simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

(* Teorema que demuestra la asociatividad *)
Theorem app_assoc : forall T (l ls1 ls2 : list T),
  app l (app ls1 ls2) = app (app l ls1) ls2.
Proof.
intros  T l ls1 ls2.
induction l.
- simpl. reflexivity.
-simpl. rewrite IHl. reflexivity.
Qed.

(* Definición que toma una lista y devuelve una nueva lista con 
los mismos elementos pero en orden inverso *)
Fixpoint rev T (l : list T) : list T :=
  match l with 
  | Nil _ => l
  | Cons h t => app (rev t) (Cons h (Nil T))
end.

(* Teorema  que si tenemos dos listas y las concatenamos, al invertir 
el resultado obtenemos lo mismo que si invertimos cada lista por separado 
y luego las concatenamos en orden contrario *)
Theorem rev_app_dist : forall T (ls1 ls2 : list T),
  rev (app ls1 ls2) = app (rev ls2) (rev ls1).
Proof.
intros T ls1 ls2.
induction ls1.
- simpl. rewrite app_nil_r. reflexivity.
- simpl. rewrite IHls1. rewrite app_assoc. reflexivity.
Qed.

(* Teorema que al aplicar dos veces la reversa devuevle la lista 
original *)
Theorem rev_involutive : forall T (l: list T) ,
  rev (rev l) = l.
Proof.
intros T l.
induction l.
- simpl. reflexivity.
- simpl. rewrite rev_app_dist. rewrite IHl. simpl. reflexivity.
Qed.

(* Teorema:  si dos listas tienen la misma reversa, entonces las 
listas originales son iguales. *)
Theorem rev_injective : forall X (l1 l2 : list X),
  rev l1 = rev l2 -> l1 = l2.
Proof.
intros X l1 l2 HEq.
rewrite <- (rev_involutive l1).
rewrite HEq.
apply rev_involutive. 
Qed.

(*definicion para instanciar la lista vacia como lista 
de numeros naturales *)
Definition NilN := Nil nat.

(** 
Codigo tomado de https://github.com/foreverbell/verified
*)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | Nil _ => Cons x NilN
  | Cons y l' => if (Nat.leb x y)
                 then Cons x (Cons y l')
                 else Cons y (insert x l')
  end.
  
(* Ejemplos del uso de insert dandole listas desordenadas *) 
Check insert 5 (Cons 3 (Cons 2 (Cons 7 (Cons 1 NilN)))).
(* [5,3,2,7,1] *)
Eval compute in (insert 5 (Cons 3 (Cons 2 (Cons 7 (Cons 1 NilN))))).
(* [3,2,5,7,1] *)
Eval compute in (insert 3 (Cons 2 (Cons 5 (Cons 7 (Cons 1 (Nil nat)))))).
(* [2,3,5,7,1] *)
Eval compute in (insert 2 (Cons 3 (Cons 5 (Cons 7 (Cons 1 NilN))))).

(* Sort the rest list, 
and insert the head element into the sorted rest list. *)
Fixpoint insertsort (l : list nat) : list nat :=
  match l with
  | Nil _ => NilN
  | Cons x l' => insert x (insertsort l')
  end.

(* operacion para ordenar, sort, se define con el algoritmo de insertion sort*)
Definition sort := insertsort.

Check sort (Cons 7 (Cons 0 NilN)).
Eval compute in sort (Cons 7 (Cons 0 NilN)).
Eval compute in (sort (Cons 5 (Cons 3 (Cons 2 (Cons 7 (Cons 1 NilN)))))).

(* Definir el comportamiento de lista ordenada como un 
tipo inductivo *)
Inductive ordenada : list nat -> Set :=
| ord_nil : ordenada NilN
| ord_single : forall (x : nat), ordenada (Cons x NilN)
| ord_cons : forall (x y : nat) (l : list nat),
    x <= y -> ordenada (Cons y l) -> 
    ordenada (Cons x (Cons y l)).


(* Demostrar que una lista despues de ser ordenada con insertion sort
realmente esta ordenada *)
Theorem insert_ordenada : forall (x : nat) (l : list nat),
    ordenada l -> ordenada (insert x l).
Proof.
intros x l O.
induction O.
-simpl. apply ord_single.
- simpl insert. destruct (Nat.leb x x0) eqn:Hleb.
--apply Nat.leb_le in Hleb. apply ord_cons.
      * assumption.
      * apply ord_single.
-- apply Nat.leb_gt in Hleb. apply ord_cons.
      * apply Nat.lt_le_incl. assumption.
      * apply ord_single.
- simpl insert. destruct (Nat.leb x x0) eqn:Hleb.
--apply Nat.leb_le in Hleb. apply ord_cons.
      *assumption.
      * apply ord_cons.
        + assumption.
        + assumption.
--apply Nat.leb_gt in Hleb. simpl. destruct (x <=? y) eqn:Hleb'.
      * apply Nat.leb_le in Hleb'. apply ord_cons.
        + apply Nat.lt_le_incl. assumption.
        + apply ord_cons.
          ++ assumption.
          ++ assumption.
     * apply Nat.leb_gt in Hleb'. apply ord_cons.
        + assumption.
        + apply Nat.leb_gt in Hleb'.  assert (Heq: insert x (Cons y l) = Cons y (insert x l)).
  { simpl. rewrite Hleb'. reflexivity. } rewrite Heq in IHO. assumption.
Qed.


Theorem insertsort_ordenada : forall (l : list nat),
    ordenada (sort l).
Proof.
  intros l.
  induction l as [| x l' IH].
  - (* nil *)
    simpl. apply ord_nil.
  - (* cons x l' *)
    simpl.
    apply insert_ordenada.
    assumption.
Qed.

Fixpoint bubble_pass_aux (n : nat) (l' : list nat) : list nat :=
  match l' with
  | Nil _ => Cons n NilN
  | Cons y l' =>
      if Nat.leb n y
      then Cons n (bubble_pass_aux y l')
      else Cons y (bubble_pass_aux n l')
  end.

Definition bubble_pass (l : list nat) : list nat :=
  match l with
  | Nil _ => NilN
  | Cons x rest => bubble_pass_aux x rest
  end.

Fixpoint list_eq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | Nil _ , Nil _ => true
  | Cons x1 l1', Cons x2 l2' =>
      if Nat.leb x1 x2 then list_eq l1' l2' else false
  | _, _ => false
  end.

Fixpoint bubble_sort_aux (l : list nat) (n : nat) : list nat :=
  match n with
  | 0 => l  (* Por si acaso *)
  | S n' =>
      let l' := bubble_pass l in
      if list_eq l' l
      then l'  (* Si no hubo cambios, ya está ordenada *)
      else bubble_sort_aux l' n'
  end.

(* Versión principal: usamos la longitud como número máximo de iteraciones *)
Definition bubble_sort (l : list nat) : list nat :=
  bubble_sort_aux l (length l).

Eval compute in (bubble_pass (Cons 3 (Cons 1 (Cons 4 (Cons 2 NilN))))).
Eval compute in (bubble_sort (Cons 3 (Cons 1 (Cons 4 (Cons 2 NilN))))).

Eval compute in (bubble_pass (Cons 3( Cons 1 (Cons 4 (Cons 1 (Cons 5 (Cons 9 (Cons 2 (Cons 6 (Cons 5 NilN)))))))))).
Eval compute in (bubble_sort (Cons 3( Cons 1 (Cons 4 (Cons 1 (Cons 5 (Cons 9 (Cons 2 (Cons 6 (Cons 5 NilN)))))))))).

(* Extracción haskell *)
From Coq Require Extraction.
From Coq Require ExtrHaskellBasic.
Set Extraction Output Directory ".".
Extraction Language Haskell.


Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Prelude.Either"  [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ] "(\fO fS n -> if n Prelude.== 0 then fO () else fS (Prelude.pred n))".

Extract Constant plus => "(Prelude.+)".
Extract Constant andb => "(Prelude.&&)".
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".

Extraction "listas.hs" app length rev.

Extraction "insertsort.hs" insert insertsort sort ordenada insert_ordenada insertsort_ordenada.

