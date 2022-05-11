

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}  

_+_ : Nat → Nat → Nat
0  + y = y
(suc x) + y = suc (x + y)

halve : Nat → Nat
halve 0 = 0
halve (suc 0) = 0
halve (suc(suc x)) = suc (halve x)


