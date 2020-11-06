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

  {-# TERMINATING #-}
  nullable₀ : (N × (N ∣ T) *) * -> N * -> N *
  nullable₀ ε ns = ns
  nullable₀ ((X , α) ∷ rs)       ns with elem decidₙ X ns
  nullable₀ ((X , α) ∷ rs)       ns | yes x = nullable₀ rs ns
  nullable₀ ((X , ε) ∷ rs)       ns | no x = nullable₀ rs (X ∷ ns)
  nullable₀ ((X , r a ∷ α) ∷ rs) ns | no x = nullable₀ rs ns
  nullable₀ ((X , l Y ∷ α) ∷ rs) ns | no x with elem decidₙ Y ns
  nullable₀ ((X , l Y ∷ α) ∷ rs) ns | no x | yes x₁ = nullable₀ ((X , α) ∷ rs) ns
  nullable₀ ((X , l Y ∷ α) ∷ rs) ns | no x | no x₁ = nullable₀ rs ns

  nullable₁ :
    (rs : (N × (N ∣ T) *) *) ->
    (ns : N *) ->
    (m : ℕ) ->
    N *
  nullable₁ rs ns zero = ns
  nullable₁ rs ns (suc m) = nullable₁ rs (nullable₀ rs ns) m

  nullable : CFG -> N *
  nullable G = nullable₁ (CFG.rules G) ε (length (CFG.rules G))

  nullable₀-sound : ∀ {G X u} rs ns ->
    (∀ {X α} -> (X , α) ∈ rs -> (X , α) ∈ CFG.rules G) ->
    (∀ {Y u} -> Y ∈ ns -> G ⊢ u ∥ u ∈ l Y ∷ ε) ->
    X ∈ nullable₀ rs ns -> G ⊢ u ∥ u ∈ l X ∷ ε

  nullable₀-sound ε ns f g p = g p
  nullable₀-sound ((X , α) ∷ rs) ns f g p       with elem decidₙ X ns
  nullable₀-sound ((X , α) ∷ rs) ns f g p       | yes x = nullable₀-sound rs ns (f ∘ in-tail) g p
  nullable₀-sound ((X , ε) ∷ rs) ns f g p       | no x =
    nullable₀-sound rs ns (f ∘ in-tail) g {!p!}

  nullable₀-sound ((X , r a ∷ α) ∷ rs) ns f g p | no x = nullable₀-sound rs ns (f ∘ in-tail) g p
  nullable₀-sound ((X , l Y ∷ α) ∷ rs) ns f g p | no x with elem decidₙ Y ns
  nullable₀-sound ((X , l Y ∷ α) ∷ rs) ns f g p | no x | yes x₁ = {!!}
  nullable₀-sound ((X , l Y ∷ α) ∷ rs) ns f g p | no x | no x₁ = nullable₀-sound rs ns (f ∘ in-tail) g p

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
