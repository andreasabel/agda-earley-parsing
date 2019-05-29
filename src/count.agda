{-# OPTIONS --allow-unsolved-metas #-}

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

  lookup-sound : ∀ {Y α rs} ->
    (Y , α) ∈ rs ->
    Σ λ e -> σ (Y  , α) e ∈ lookup Y rs
  lookup-sound {Y} {α} {ε} ()
  lookup-sound {Y} {α} {(X , qs) ∷ rs} p with lookup Y rs
  lookup-sound {Y} {α} {(X , qs) ∷ rs} p | ps with decidₙ Y X
  lookup-sound {Y} {α} {(X , qs) ∷ rs} p | ps | yes x = {!!}
  lookup-sound {Y} {α} {(X , qs) ∷ rs} p | ps | no x = {!!}
  
  ∋-comm : {T : Set} {a b c : T} {bs : T *} ->
    (a ∷ b ∷ bs) ∋ c -> (b ∷ a ∷ bs) ∋ c
  ∋-comm in-head = in-tail in-head
  ∋-comm (in-tail in-head) = in-head
  ∋-comm (in-tail (in-tail p₁)) = in-tail (in-tail p₁)
  
  nullable : CFG -> N *
  nullable G = go (CFG.rules G) ε
    where
      go : (N × (N ∣ T) *) * -> N * -> N *
      go ε ns = ns
      go ((X , α) ∷ rs)       ns with elem decidₙ X ns
      go ((X , α) ∷ rs)       ns | yes x = go rs ns
      go ((X , ε) ∷ rs)       ns | no x = go rs (X ∷ ns)
      go ((X , r a ∷ α) ∷ rs) ns | no x = go rs ns
      go ((X , l Y ∷ α) ∷ rs) ns | no x with elem decidₙ Y ns
      go ((X , l Y ∷ α) ∷ rs) ns | no x | yes x₁ = go ((X , α) ∷ rs) ns
      go ((X , l Y ∷ α) ∷ rs) ns | no x | no x₁ = {!!}

  nullable-sound : ∀ {G X t u} ->
    X ∈ nullable G -> Σ λ γ -> G ∙ t ⊢ u / u ⟶* X / γ ∙ ε
  nullable-sound p = {!!}

  nullable-complete : ∀ {G X t u γ} -> G ∙ t ⊢ u / u ⟶* X / γ ∙ ε -> X ∈ nullable G
  nullable-complete = {!!}

  suffix-with-ω : ∀ {a} {w v t : T *} ->
    (Σ λ s₁ -> s₁ ++ (a ∷ w) ≡ t) ->
    (Σ λ s₂ -> s₂ ++ w ≡ v) ->
    (Σ λ s₃ -> s₃ ++ v ≡ t) ->
    Σ λ s -> s ++ (a ∷ w) ≡ v
  suffix-with-ω (σ a₁ a₀) (σ b₁ b₀) (σ c₁ c₀) =
    {!!}

