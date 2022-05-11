
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}  

_+_ : Nat → Nat → Nat
0  + y = y
(suc x) + y = suc (x + y)


id : {A : Set} → A → A 
id x = x

infixr 5 _::_

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

length : {A : Set} -> List A -> Nat
length [] = 0
length (a :: rest) = 1 + length rest

_++_ : {A : Set} -> List A -> List A -> List A 
[] ++ list = list
(a :: rest) ++ list = a :: (rest ++ list)

a = 0 :: 1 :: 2 :: 3 :: []

b = 4 :: 5 :: []

c = a ++ b 

map : {A B : Set} -> (A -> B) -> List A -> List B 
map f [] = []
map f (a :: rest) = (f a) :: (map f rest)

inc : Nat -> Nat 
inc x = x + 1

d = map inc (0 :: 1 :: 2 :: 3 :: [])

data Maybe (A : Set) : Set where
  just : A -> Maybe A 
  nothing : Maybe A


lookup : { A : Set } -> List A -> Nat -> Maybe A  
lookup [] 0 = nothing
lookup [] (suc n) = nothing
lookup (a :: rest) 0 = just a 
lookup (a :: rest) (suc n) = lookup rest n  

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B 
infixr 4 _,_  

e = 2 , 3

fst : { A B : Set } -> A × B -> A 
fst (a , b) = a 


snd : { A B : Set} -> A × B -> B 
snd (a , b) = b   


 

