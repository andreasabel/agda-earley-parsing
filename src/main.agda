{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Helper #-}

open import base

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  String : Set

{-# BUILTIN STRING String #-}

postulate
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}

postulate
  readAndParse : (Char * → String) → IO Unit

{-# COMPILE GHC readAndParse = Helper.readAndParse #-}

open import grammar ℕ Char

parens : CFG
parens = 0 ⟩
  (0 , r '(' ∷ l 0 ∷ r ')' ∷ ε) ∷
  (0 , ε) ∷ ε

no-same-ab : CFG
no-same-ab = 0 ⟩
  (0 , l 1 ∷ ε) ∷
  (0 , l 2 ∷ ε) ∷
  (1 , l 3 ∷ r 'a' ∷ l 1 ∷ ε) ∷
  (1 , l 3 ∷ r 'a' ∷ l 3 ∷ ε) ∷
  (1 , l 1 ∷ r 'a' ∷ l 3 ∷ ε) ∷
  (2 , l 3 ∷ r 'b' ∷ l 2 ∷ ε) ∷
  (2 , l 3 ∷ r 'b' ∷ l 3 ∷ ε) ∷
  (2 , l 2 ∷ r 'b' ∷ l 3 ∷ ε) ∷
  (3 , r 'a' ∷ l 3 ∷ r 'b' ∷ l 3 ∷ ε) ∷
  (3 , r 'b' ∷ l 3 ∷ r 'a' ∷ l 3 ∷ ε) ∷
  (3 , ε) ∷
  ε

private
 primitive
  primCharToNat    : Char → ℕ
  primCharEquality : Char → Char → Bool
  primTrustMe : ∀ {A : Set} {x y : A} → x ≡ y

eqₜ : Dec Char
eqₜ c d with primCharEquality c d
eqₜ c d | true = yes primTrustMe
eqₜ c d | false = no w
  where postulate w : _

open import earley ℕ Char eq-ℕ eqₜ
open parser parens

s' : ∀ {w} -> Item w ε * -> ℕ
s' {w} ε = 0
s' {w} ((Y ∘ u ↦ α ∘ x ∷ β) ∷ as) = s' as
s' {w} ((Y ∘ u ↦ α ∘ ε) ∷ as) with eq-* eqₜ u w
s' {w} ((Y ∘ u ↦ α ∘ ε) ∷ as) | no x = s' as
s' {w} ((Y ∘ w ↦ α ∘ ε) ∷ as) | yes refl with eq-ℕ Y (CFG.start parens)
s' {w} ((Y ∘ w ↦ α ∘ ε) ∷ as) | yes refl | yes refl = 1
s' {w} ((Y ∘ w ↦ α ∘ ε) ∷ as) | yes refl | no x = s' as

s : Char * -> ℕ
s t =
  let x₁ = parse t in
  let x₂ = Sₙ x₁ in
  s' x₂

show : ℕ -> String
show zero = "Reject"
show (suc n) = "Accept"

main : IO Unit
main = readAndParse (show ∘ s)
