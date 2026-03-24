-- Extraccion corregida
-- eliminar import qualified Prelude
-- agregar deriving en data

module Binarios where

-- import qualified Prelude

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add = (Prelude.+)

mul :: Prelude.Int -> Prelude.Int -> Prelude.Int
mul n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (Prelude.pred n))
    (\_ -> 0)
    (\p -> add m (mul p m))
    n

data Bin =
   Z
 | B0 Bin
 | B1 Bin
 deriving Show --mostrar los elementos de Bin en la terminal
 -- Show es la clase para mostrar elementos de un tipo en la terminal

incr :: Bin -> Bin
incr m =
  case m of {
   Z -> B1 Z;
   B0 n -> B1 n;
   B1 n -> B0 (incr n)}


binToNat :: Bin -> Prelude.Int
-- bin_to_nat :: Bin -> Prelude.Int
binToNat m =
  case m of {
   Z -> 0;
   B0 n -> mul (Prelude.succ (Prelude.succ 0)) (binToNat n);
   B1 n ->
    add (Prelude.succ 0) (mul (Prelude.succ (Prelude.succ 0)) (binToNat n))}

