
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

-- True and false

data ⊥ : Set where


data IsTrue : Bool → Set where
  is-true : IsTrue true 

-- Equality of Nats

_=Nat_ : Nat → Nat → Bool 
zero =Nat zero = true
(suc x) =Nat (suc y) = x =Nat y
_       =Nat _       = false

-- Proof that n equals n for n: ℕ 

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero = is-true
n-equals-n (suc m) = n-equals-n m  

-- proof that there is an n such that n + n = 12

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

infixr 4 _,_

half-a-dozen : Σ Nat (λ n → IsTrue ((n + n) =Nat 12))
half-a-dozen = 6 , is-true
 
data _≡_ {A : Set} : A → A → Set where
  refl : { x : A } → x ≡ x

infix 4 _≡_


one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 → ⊥
zero-not-one ()

id : {A : Set} → A → A 
id x = x


id-returns-input : {A : Set} -> (x : A) -> id x ≡ x
id-returns-input x = refl


-- symmetry of equality 

sym : { A : Set } { x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

-- symmetry of transitivity

trans : { A : Set } { x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl