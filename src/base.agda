infix 4 _≡_
data _≡_ {T : Set} (t : T) : T -> Set where
  refl : t ≡ t
{-# BUILTIN EQUALITY _≡_  #-}

data Void : Set where

data _≠_ {T : Set} : T -> T -> Set where
  neq : {t u : T} -> (t ≡ u -> Void) -> t ≠ u

data _* (T : Set) : Set where
  ε : T *
  _∷_ : T -> T * -> T *
infixr 10 _*
infixr 20 _∷_

_++_ : {T : Set} -> T * -> T * -> T *
ε ++ b = b
(x ∷ a) ++ b = x ∷ (a ++ b)

_∷←_ : {T : Set} -> T * -> T -> T *
ε ∷← b = b ∷ ε
(x ∷ a) ∷← b = x ∷ (a ∷← b)

reverse : {T : Set} -> T * -> T *
reverse ε = ε
reverse (x ∷ xs) = reverse xs ∷← x

data _∋_ {T : Set} : T * -> T -> Set where
  in-head : {t : T} {ts : T *} -> (t ∷ ts) ∋ t
  in-tail : {t u : T} {ts : T *} -> ts ∋ t -> (u ∷ ts) ∋ t

data _∣_ (A B : Set) : Set where
  r : B -> A ∣ B
  l : A -> A ∣ B
infixr 15 _∣_

data _⟶_ (A B : Set) : Set where
  _↦_ : A -> B -> A ⟶ B

infixl 19 _↦_
