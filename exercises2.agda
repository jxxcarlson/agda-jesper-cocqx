
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}  

_+_ : Nat → Nat → Nat
0  + y = y
(suc x) + y = suc (x + y)

data Vec (A : Set) : Nat -> Set where 
  [] : Vec A 0
  _::_ : { n : Nat } -> A -> Vec A n -> Vec A (suc n) 
  
infixr 5 _::_ 
