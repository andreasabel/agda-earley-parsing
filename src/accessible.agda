module accessible where

open import base

data _<_ : ℕ -> ℕ -> Set where
  <ᵢ : ∀ {k} -> k < suc k
  <ₛ : ∀ {k j} -> j < k -> j < suc k

data Acc< : ℕ -> Set where
  acc : {n : ℕ} -> ((m : ℕ) -> m < n -> Acc< m) -> Acc< n

<-≤ : {m n : ℕ} -> m < n -> m ≤ n
<-≤ <ᵢ = ≤-suc (≤-self _)
<-≤ (<ₛ p) = ≤-suc (<-≤ p)

acc<0 : (n : ℕ) -> n < 0 -> Acc< n
acc<0 n ()

acc0 : Acc< 0
acc0 = acc λ m ()

acc<1 : (n : ℕ) -> (n < 1) -> Acc< n
acc<1 .0 <ᵢ = acc0
acc<1 n (<ₛ p) = acc<0 n p

acc1 : Acc< 1
acc1 = acc acc<1

acc<2 : (n : ℕ) -> (n < 2) -> Acc< n
acc<2 .1 <ᵢ = acc1
acc<2 n (<ₛ p) = acc<1 n p

acc2 : Acc< 2
acc2 = acc acc<2

acc<3 : (n : ℕ) -> (n < 3) -> Acc< n
acc<3 .2 <ᵢ = acc2
acc<3 n (<ₛ p) = acc<2 n p

acc3 : Acc< 3
acc3 = acc acc<3

acc<ℕ : (n : ℕ) -> ((m : ℕ) -> m < n -> Acc< m) -> ((k : ℕ) -> k < suc n -> Acc< k)
acc<ℕ zero f k p = acc<1 k p
acc<ℕ (suc n) f .(suc n) <ᵢ = acc f
acc<ℕ (suc n) f k (<ₛ p) = acc<ℕ n (λ m x → f m (<ₛ x)) k p

accℕ : (n : ℕ) -> Acc< n
accℕ zero = acc0
accℕ (suc n) with accℕ n
accℕ (suc n) | acc x = acc (acc<ℕ n x)

data _⊂_ {T : Set} : T * -> T * -> Set where
  ⊂ᵢ : ∀ {a as} -> as ⊂ (a ∷ as)
  ⊂ₛ : ∀ {a as bs} -> as ⊂ bs -> as ⊂ (a ∷ bs)

data Acc-⊂ {T : Set} : T * -> Set where
  acc : ∀ {Q} -> (∀ {P} -> P ⊂ Q -> Acc-⊂ P) -> Acc-⊂ Q

acc-ε : {T : Set} -> Acc-⊂ {T} ε
acc-ε = acc λ ()

acc-⊂-1 : {T : Set} {a : T} {as : T *} -> as ⊂ (a ∷ ε) -> Acc-⊂ as
acc-⊂-1 ⊂ᵢ = acc-ε
acc-⊂-1 (⊂ₛ ())

acc-⊂-* : {T : Set} {a : T} (as cs : T *) -> ({bs : T *} -> bs ⊂ as -> Acc-⊂ bs) -> cs ⊂ (a ∷ as) -> Acc-⊂ cs
acc-⊂-* ε cs f p = acc-⊂-1 p
acc-⊂-* (x ∷ as) .(x ∷ as) f ⊂ᵢ = acc f
acc-⊂-* (x ∷ as) cs f (⊂ₛ p) = acc-⊂-* as cs (λ x₁ → f (⊂ₛ x₁)) p

acc-* : {T : Set} (as : T *) -> Acc-⊂ as
acc-* ε = acc-ε
acc-* (a ∷ as) with acc-* as
acc-* (a ∷ as) | acc x = acc (acc-⊂-* as _ x)
