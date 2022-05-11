
-- Natural numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}  

_+_ : Nat → Nat → Nat
0  + y = y
(suc x) + y = suc (x + y)


-- Booleans

data Bool : Set  where
  true  : Bool 
  false : Bool

not : Bool → Bool
not true = false
not false = true

-- Lists

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

length : {A : Set} -> List A -> Nat
length [] = 0
length (a :: rest) = 1 + length rest

_++_ : {A : Set} -> List A -> List A -> List A 
[] ++ list = list
(a :: rest) ++ list = a :: (rest ++ list)

map : {A B : Set} -> (A -> B) -> List A -> List B 
map f [] = []
map f (a :: rest) = (f a) :: (map f rest)

-- Proving things

data ⊤ : Set where 


  tt : ⊤

data ⊥ : Set where 
  -- no constructors

-- product type

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B  

infixr 4 _,_


-- sum type

data Either (A B : Set) : Set where  
  left : A → Either A B 
  right : B → Either A B

ee = left 2

-- The proposition P → P:

proof1 : { P : Set } → P → P  
proof1 p = p 

-- If P → Q and Q → R then P → R 

proof2 : { P Q R : Set } → (P → Q) × (Q → R) → ( P → R )
proof2 (f , g) = λ x → g (f x)

-- If (P or Q) implies R, then (P implies R) and (Q implies R)

proof3 : { P Q R : Set } → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f(left x)) , (λ y → f(right y))

-- Define a type isEven n:

data IsEven : Nat → Set where 
  even-zero : IsEven zero
  even-suc2 : { n : Nat } → IsEven n → IsEven (suc(suc n))

6-is-even : IsEven 6
6-is-even = even-suc2 (even-suc2 (even-suc2(even-zero)))

7-is-not-even : IsEven 7 → ⊥
7-is-not-even (even-suc2 (even-suc2 (even-suc2())))

data IsTrue : Bool → Set where
  is-true : IsTrue true 

-- Equality of Nats

_=Nat_ : Nat → Nat → Bool 
zero =Nat zero = true
(suc x) =Nat (suc y) = x =Nat y
_       =Nat _       = false

-- proof that length (1 :: 2 :: 3 :: [] is 3:

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = is-true


-- proof that double x is always even (example of universal quantification)

double : Nat → Nat
double zero = zero 
double (suc n) = suc(suc(double n))

double-is-even : (n : Nat) → IsEven (double n)
double-is-even zero = even-zero 
double-is-even (suc m) = even-suc2 (double-is-even m)


-- Proof that n equals n for n: ℕ 

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero = is-true
n-equals-n (suc m) = n-equals-n m 

