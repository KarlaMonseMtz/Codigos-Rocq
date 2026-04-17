module Insertsort where

import qualified Prelude
import Prelude (Show)

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

leb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (Prelude.pred n))
    (\_ -> Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (Prelude.pred n))
      (\_ -> Prelude.False)
      (\m' -> leb n' m')
      m)
    n

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rec =
  list_rect

nilN :: [] Prelude.Int
nilN =
  []

insert :: Prelude.Int -> ([] Prelude.Int) -> [] Prelude.Int
insert x l =
  case l of {
   [] -> (:) x nilN;
   (:) y l' ->
    case leb x y of {
     Prelude.True -> (:) x ((:) y l');
     Prelude.False -> (:) y (insert x l')}}

insertsort :: ([] Prelude.Int) -> [] Prelude.Int
insertsort l =
  case l of {
   [] -> nilN;
   (:) x l' -> insert x (insertsort l')}

sort :: ([] Prelude.Int) -> [] Prelude.Int
sort =
  insertsort

data Ordenada =
   Ord_nil
 | Ord_single Prelude.Int
 | Ord_cons Prelude.Int Prelude.Int [Prelude.Int] Ordenada
 deriving (Show)

ordenada_rect :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> Prelude.Int ->
                 ([] Prelude.Int) -> () -> Ordenada -> a1 -> a1) -> ([]
                 Prelude.Int) -> Ordenada -> a1
ordenada_rect f f0 f1 _ o =
  case o of {
   Ord_nil -> f;
   Ord_single x -> f0 x;
   Ord_cons x y l o0 -> f1 x y l __ o0 (ordenada_rect f f0 f1 ((:) y l) o0)}

ordenada_rec :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> Prelude.Int ->
                ([] Prelude.Int) -> () -> Ordenada -> a1 -> a1) -> ([]
                Prelude.Int) -> Ordenada -> a1
ordenada_rec =
  ordenada_rect

insert_ordenada :: Prelude.Int -> ([] Prelude.Int) -> Ordenada -> Ordenada
insert_ordenada x l o =
  ordenada_rec (Ord_single x) (\x0 ->
    let {b = leb x x0} in
    case b of {
     Prelude.True -> Ord_cons x x0 nilN (Ord_single x0);
     Prelude.False -> Ord_cons x0 x nilN (Ord_single x)})
    (\x0 y l0 _ o0 iHO ->
    let {b = leb x x0} in
    case b of {
     Prelude.True -> Ord_cons x x0 ((:) y l0) (Ord_cons x0 y l0 o0);
     Prelude.False ->
      let {b0 = leb x y} in
      case b0 of {
       Prelude.True -> Ord_cons x0 x ((:) y l0) (Ord_cons x y l0 o0);
       Prelude.False -> Ord_cons x0 y (insert x l0)
        (eq_rect (insert x ((:) y l0)) iHO ((:) y (insert x l0)))}}) l o

insertsort_ordenada :: ([] Prelude.Int) -> Ordenada
insertsort_ordenada l =
  list_rec Ord_nil (\x l' iH -> insert_ordenada x (sort l') iH) l
