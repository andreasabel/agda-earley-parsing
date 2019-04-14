open import base

module count (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

  open import grammar N T

  lookup : (Y : N) -> (rs : (N × (N ∣ T)*) * ) ->
      (Σ λ t -> (t ∈ rs) × (fst t ≡ Y)) *
  lookup Y ε = ε
  lookup Y ((X , qs) ∷ rs) with lookup Y rs
  lookup Y ((X , qs) ∷ rs) | ps with decidₙ Y X
  lookup Y ((X , qs) ∷ rs) | ps | no x = map (λ {(σ p₁ (p , q)) → σ p₁ (in-tail p , q)}) ps
  lookup Y ((Y , qs) ∷ rs) | ps | yes refl = σ (Y , qs) (in-head , refl) ∷
    map (λ {(σ p₁ (p , q)) → σ p₁ (in-tail p , q)}) ps
  
  ∋-comm : {T : Set} {a b c : T} {bs : T *} ->
    (a ∷ b ∷ bs) ∋ c -> (b ∷ a ∷ bs) ∋ c
  ∋-comm in-head = in-tail in-head
  ∋-comm (in-tail in-head) = in-head
  ∋-comm (in-tail (in-tail p₁)) = in-tail (in-tail p₁)
  
