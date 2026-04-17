module Listas where

import qualified Prelude

length :: ([] a1) -> Prelude.Int
length ls =
  case ls of {
   [] -> 0;
   (:) _ ls' -> Prelude.succ (length ls')}

app :: ([] a1) -> ([] a1) -> [] a1
app ls1 ls2 =
  case ls1 of {
   [] -> ls2;
   (:) x ls1' -> (:) x (app ls1' ls2)}

rev :: ([] a1) -> [] a1
rev l =
  case l of {
   [] -> l;
   (:) h t -> app (rev t) ((:) h [])}

