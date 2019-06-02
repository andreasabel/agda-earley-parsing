{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

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
  putStr : String → IO Unit

{-# COMPILE GHC putStr = Text.putStr #-}

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}

open import grammar ℕ Char

G₀ : CFG
G₀ = 0 ⟩
  (1 , r 'a' ∷ ε) ∷
  (0 , r 's' ∷ l 0 ∷ r 's' ∷ ε) ∷
  (0 , l 1 ∷ ε) ∷ ε

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
open parser G₀

t : Char *
t = 's' ∷ 'a' ∷ 's' ∷ ε

s : ℕ
s =
  let x₁ = parse t in
  length (Sₙ x₁)

show : ℕ -> String
show zero = "Reject\n"
show (suc n) = "Accept\n"

main : IO Unit
main = putStr (show s)
