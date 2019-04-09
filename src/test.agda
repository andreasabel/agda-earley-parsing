open import base

data T₀ : Set where
  s₀ : T₀
  a₀ : T₀

data N₀ : Set where
  S₀ : N₀
  A₀ : N₀

open import grammar N₀ T₀

G₀ : CFG
G₀ = record
    { start = S₀
    ; rules = (A₀ , r a₀ ∷ ε) ∷ (S₀ , r s₀ ∷ l S₀ ∷ r s₀ ∷ ε) ∷ (S₀ , l A₀ ∷ ε) ∷ ε
    ; valid = λ { S₀ → σ _ (in-tail in-head) ; A₀ → σ _ in-head}
    }

t : T₀ *
t = s₀ ∷ a₀ ∷ s₀ ∷ ε

simple : G₀ ⊢ t / ε ⟶* S₀ / ε
simple =
  let x₁ = initial in
  let x₂ = predict {G = G₀} (in-tail in-head) x₁ in
  let x₃ = predict {G = G₀} (in-tail (in-tail in-head)) x₁ in
  let x₄ = scanner x₂ in
  let x₅ = predict {G = G₀} in-head x₃ in
  let x₆ = predict {G = G₀} (in-tail in-head) x₄ in
  let x₇ = predict {G = G₀} (in-tail (in-tail in-head)) x₄ in
  let x₈ = predict {G = G₀} in-head x₇ in
  let x₉ = scanner x₈ in
  let x₁₀ = complet x₇ x₉ in
  let x₁₁ = complet x₄ x₁₀ in
  let x₁₂ = scanner x₁₁ in
  let x₁₃ = complet x₁ x₁₂ in
  x₁₃
