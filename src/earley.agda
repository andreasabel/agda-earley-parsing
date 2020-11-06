{-# OPTIONS --irrelevant-projections #-}

open import base

module earley (N T : Set) (eqₙ : Dec N) (eqₜ : Dec T) where

open import grammar N T

module parser (G : CFG) where

  open import count N T eqₙ eqₜ

  v-step : ∀ {Y α x β} -> CFG.rules G ∋ (Y , α ++ (x ∷ β)) -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β)
  v-step {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (in₀ x α β) v

  v-unstep : ∀ {Y α x β} -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β) -> CFG.rules G ∋ (Y , α ++ (x ∷ β))
  v-unstep {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (sym (in₀ x α β)) v

  -- Earley items:
  --   Y ∘ u ↦ α ∘ β : Item w v
  -- means
  -- * we are parsing input w
  -- * it remains to parse v (v is the leftover)
  -- * Y ↦ αβ is a rule of the grammar
  -- * the item was predicted when the leftover was u

  record Item (w : T *) (v : T *) : Set where
    constructor _∘_↦_∘_
    field
      Y : N
      u : T *
      α β : (N ∣ T) *
      .{χ} : CFG.rules G ∋ (Y , α ++ β)
      .{ψ} : (Σ λ t -> t ++ u ≡ w)        -- u is a suffix of w

  infixl 3 _∘_↦_∘_
  pattern _∘_↦_∘_[_∘_] Y u α β χ ψ = (Y ∘ u ↦ α ∘ β) {χ} {ψ}
  infixl 3 _∘_↦_∘_[_∘_]

  eq-α :
    (a b : (N ∣ T)*) ->
    a ≡ b ??
  eq-α = eq-* (eq-∣ eqₙ eqₜ)

  eq-T* : (a b : T *) -> a ≡ b ??
  eq-T* = eq-* eqₜ

  eq-rule : (a b : N × (N ∣ T) *) -> a ≡ b ??
  eq-rule = eq-× eqₙ eq-α

  eq-item : ∀ {w v} -> (a b : Item w v) -> a ≡ b ??
  eq-item (X ∘ i ↦ α ∘ β) (Y ∘ j ↦ γ ∘ δ) with eq-×₄ eqₙ eq-T* eq-α eq-α (X , i , α , β) (Y , j , γ , δ)
  eq-item (X ∘ i ↦ α ∘ β) (X ∘ i ↦ α ∘ β) | yes refl = yes refl
  eq-item (X ∘ i ↦ α ∘ β) (Y ∘ j ↦ γ ∘ δ) | no x = no λ {refl → x refl}

  all-items₀ : ∀ {v w X u α β} -> ∀ χ ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ->
    Σ {Item w v *} λ as ->
      ∀ {γ δ} -> ∀ χ .ψ -> (i : Item w v) -> i ≡ (X ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) -> (Σ λ t ->
        (t ++ δ ≡ β) × (α ++ t ≡ γ)) ->
      i ∈ as
  all-items₀ χ ψ i@(X ∘ u ↦ α ∘ ε) refl = σ (i ∷ ε) λ
    { χ ψ (X ∘ u ↦ γ ∘ .ε) refl (σ ε (refl , y)) → case trans (sym (++-ε α)) (sym y) of λ {refl → in-head}
    ; χ ψ (X ∘ u ↦ γ ∘ δ) refl (σ (x₁ ∷ t) (() , y))
    }
  all-items₀ χ ψ i@(X ∘ u ↦ α ∘ x ∷ β) refl with all-items₀ (in₄ χ) ψ (X ∘ u ↦ α ←∷ x ∘ β [ in₄ χ ∘ ψ ]) refl
  all-items₀ χ ψ i@(X ∘ u ↦ α ∘ x ∷ β) refl | σ p₁ p₀ = σ (i ∷ p₁) λ
    { χ ψ (X ∘ u ↦ γ ∘ .(x ∷ β)) refl (σ ε (refl , y)) → case trans (sym (++-ε α)) (sym y) of λ {refl → in-head}
    ; χ ψ i@(X ∘ u ↦ γ ∘ δ) refl (σ (x₁ ∷ t) (refl , y)) → in-tail (p₀ χ ψ i refl (σ t (refl , (trans (sym (in₀ _ _ _)) (sym y)))))
    }

  all-items₁ : ∀ {w v X u β} -> ∀ χ ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ ε ∘ β [ χ ∘ ψ ]) ->
    Σ {Item w v *} λ as ->
      ∀ {u₀ γ δ} -> ∀ χ ψ -> (i : Item w v) -> i ≡ (X ∘ u₀ ↦ γ ∘ δ [ χ ∘ ψ ]) ->
        γ ++ δ ≡ β -> (Σ λ t → t ++ u₀ ≡ u) ->
        i ∈ as
  all-items₁ χ ψ i@(X ∘ ε ↦ ε ∘ β) refl with all-items₀ χ ψ i refl
  all-items₁ χ ψ (X ∘ ε ↦ ε ∘ β) refl | σ p₁ p₀ = σ p₁ λ
    { χ₁ ψ₁ (.X ∘ .ε ↦ γ ∘ δ) refl x₁ (σ ε refl) → p₀ χ₁ ψ₁ _ refl (σ γ (x₁ , refl))
    ; χ₁ ψ₁ (.X ∘ u₀ ↦ γ ∘ δ) refl x₁ (σ (x ∷ t) ())
    }
  all-items₁ {w} {v} χ ψ@(σ q₀ q₁) i@(X ∘ x ∷ u ↦ ε ∘ β) refl with all-items₀ χ ψ i refl | all-items₁ {w} {v} χ (σ (q₀ ←∷ x) (trans (sym (in₀ _ _ _)) (sym q₁))) (X ∘ u ↦ ε ∘ β) refl
  all-items₁ {w} {v} χ ψ (X ∘ x ∷ u ↦ ε ∘ β) refl | σ p₁ p₀ | σ p₂ p₃ = σ (p₁ ++ p₂) λ
    { χ₁ ψ₁ (.X ∘ .(x ∷ u) ↦ γ ∘ δ) refl x₂ (σ ε refl) → in-l (p₀ χ₁ ψ₁ _ refl (σ γ (x₂ , refl)))
    ; χ₁ ψ₁ (.X ∘ u₀ ↦ γ ∘ δ) refl x₂ (σ (x₁ ∷ p₄) refl) → in-r (p₃ χ₁ ψ₁ _ refl x₂ (σ p₄ refl))
    }

  all-items₂ : ∀ {w v} ->
    (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) ->
    Σ {Item w v *} λ as ->
      ∀ {X u γ δ} -> ∀ χ ψ -> (i : Item w v) -> i ≡ (X ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) -> (X , γ ++ δ) ∈ rs -> i ∈ as
  all-items₂ ε f = σ ε λ {χ₁ ψ₁ i x ()}
  all-items₂ {w} ((Y , α) ∷ rs) f with all-items₁ (f in-head) (σ ε refl) (Y ∘ w ↦ ε ∘ α) refl
  all-items₂ {w} ((Y , α) ∷ rs) f | σ p₁ p₀ with all-items₂ rs (f ∘ in-tail)
  all-items₂ {w} ((Y , α) ∷ rs) f | σ p₁ p₀ | σ p₂ p₃ = σ (p₁ ++ p₂) λ
    { χ ψ (.Y ∘ u ↦ γ ∘ δ) refl in-head → in-l (p₀ χ ψ _ refl refl ψ)
    ; χ ψ (X ∘ u ↦ γ ∘ δ) refl (in-tail x₁) → in-r (p₃ χ ψ _ refl x₁)
    }

  relevant-χ : ∀ {w v} -> (i : Item w v) -> CFG.rules G ∋ (Item.Y i , Item.α i ++ Item.β i)
  relevant-χ ((Y ∘ j ↦ α ∘ β) {χ}) = elem' eq-rule (Y , α ++ β) (CFG.rules G) χ

  open ε eqₜ

  relevant-ψ : ∀ {w v} -> (i : Item w v) -> Σ λ t -> t ++ Item.u i ≡ w
  relevant-ψ {ε} ((Y ∘ ε ↦ α ∘ β) {χ} {ψ}) = σ ε refl
  relevant-ψ {ε} ((Y ∘ x ∷ u ↦ α ∘ β) {χ} {p}) = void (ε₁ (Σ.proj₀ p))
  relevant-ψ {x ∷ w} {v} (Y ∘ ε ↦ α ∘ β [ χ ∘ p ]) = σ (x ∷ w) (++-ε (x ∷ w))
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) with eqₜ x y | eq-T* w u
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ w ↦ α ∘ β [ χ ∘ p ]) | yes refl | yes refl = σ ε refl
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ p ]) | yes refl | no x₁ with relevant-ψ {w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ ε₅ (Σ.proj₀ p) x₁ ])
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ p ]) | yes refl | no x₁ | σ q₁ q₀ = σ (x ∷ q₁) (app (x ∷_) q₀)
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ w ↦ α ∘ β [ χ ∘ p ]) | no x₂    | yes refl = void (ε₃ x₂ (Σ.proj₀ p))
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) | no x₂    | no x₁ with relevant-ψ {w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ ε₄ (Σ.proj₀ p) x₂ ])
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) | no x₂    | no x₁ | σ q₁ q₀ = σ (x ∷ q₁) (app (x ∷_) q₀)

  all-items : ∀ {w} {v} -> Σ λ as -> {i : Item w v} -> i ∈ as
  all-items with all-items₂ (CFG.rules G) id
  all-items | σ p₁ p₀ = σ p₁ λ {i} -> p₀ (relevant-χ i) (relevant-ψ i) i refl (relevant-χ i)

  open Unique Item eq-item

  -- Working set.
  -- State sets the Earley parser constructs.
  -- start rs₀ `step` rs₁ `step` rs₂ ...

  data EState : T * -> T * -> Set where
    start : {v : T *} ->
      (rs : Item v v * ) ->
      EState v v

    step : {a : T} {w v : T *} ->
      (ω : EState w (a ∷ v)) ->
      (rs : Item w v * ) ->
      EState w v

  -- Invariant: v is suffix of w.

  V : {w v : T *} ->
    EState w v ->
    Σ λ t -> t ++ v ≡ w
  V {w} {w} (start rs) = σ ε refl
  V {w} {v} (step ω rs) with V ω
  V {w} {v} (step {a} ω rs) | σ p₁ p₀ = σ (p₁ ←∷ a) (trans (sym (in₀ a p₁ v)) (sym p₀))

  -- Get the latest state.

  Sₙ : {w v : T *} ->
    EState w v ->
    Item w v *
  Sₙ (start rs) = rs
  Sₙ (step w rs) = rs

  -- Replace the latest state.

  Wₙ : {w v : T *} ->
    (ω : EState w v) ->
    (rs : Item w v *) ->
    EState w v
  Wₙ (start rs) rs₁ = start rs₁
  Wₙ (step w rs) rs₁ = step w rs₁

  -- Scanning step.

  scanr₀ : ∀ {w v} ->
    (a : T) ->
    Item w (a ∷ v)* ->
    Item w v *
  scanr₀ a ε = ε
  scanr₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs) = scanr₀ a rs
  scanr₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) = scanr₀ a rs
  scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β [ χ ∘ ψ ]) ∷ rs) with eqₜ a b
  ... | yes refl = (X ∘ u ↦ α ←∷ r a ∘ β [ v-step χ ∘ ψ ]) ∷ (scanr₀ a rs)
  ... | no x = scanr₀ a rs

  scanr : {w v : T *} ->
    (a : T) ->
    EState w (a ∷ v) ->
    EState w v
  scanr a ω = step ω (scanr₀ a (Sₙ ω))

  compl₀ : ∀ {u v w} ->
    (ω : EState w v) ->
    Item w u *
  compl₀ {u} {v} w           with eq-T* u v
  compl₀ {u} {u} w           | yes refl = Sₙ w
  compl₀ {u} {v} (start rs)  | no x = ε
  compl₀ {u} {v} (step w rs) | no x = compl₀ w

  compl₁ : ∀ {u v w} ->
    (i : Item w v) -> Item.β i ≡ ε ->
    Item w u * -> Item w v *
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ε = ε
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) = compl₁ i refl rs
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) = compl₁ i refl rs
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) with eqₙ X Z
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) | no x = compl₁ i refl rs
  compl₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β [ χ₁ ∘ ψ₁ ]) ∷ rs) | yes refl =
    (Y ∘ u₁ ↦ α₁ ←∷ l X ∘ β [ v-step χ₁ ∘ ψ₁ ]) ∷ compl₁ i refl rs

  -- For a completed item X ↦ α.ε, get the set of possible ancestors (callers).

  compl : ∀ {v w} ->
    (i : Item w v) -> Item.β i ≡ ε ->
    EState w v ->
    Item w v *
  compl i p ω = compl₁ {u = Item.u i} i p (compl₀ ω)

  predict₀ : ∀ {v w Y β} ->
    (Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) -> Item.β i ≡ l Y ∷ β ->
    (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) * ->
    Item w v *
  predict₀ ψ₁ i p ε = ε
  predict₀ {v} ψ₁ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ ps) =
    (Y ∘ v ↦ ε ∘ γ [ p ∘ ψ₁ ]) ∷ predict₀ ψ₁ i refl ps

  predic : ∀ {v w Y β} ->
    (i : Item w v) -> Item.β i ≡ l Y ∷ β ->
    EState w v ->
    Item w v *
  predic i@(X ∘ u ↦ α ∘ l Y ∷ β) refl ω =
    predict₀ (V ω) i refl (lookup Y (CFG.rules G))

  deduplicate : ∀ {w v} -> Item w v * -> Σ λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with elem eq-item x (Σ.proj₁ (deduplicate as))
  deduplicate (x ∷ as) | yes x₁ = deduplicate as
  deduplicate (x ∷ as) | no x₁ = σ (x ∷ (Σ.proj₁ (deduplicate as))) (u-∷ (Σ.proj₀ (deduplicate as)) x₁)

  pred-comp₀ : ∀ {v w β} ->
    (i : Item w v) ->
    (β ≡ Item.β i) ->
    (ω : EState w v) ->
    Item w v *
  pred-comp₀ i@(X ∘ u ↦ α ∘ ε) refl ω = compl i refl ω
  pred-comp₀ i@(X ∘ u ↦ α ∘ r a ∷ β) refl ω = ε
  pred-comp₀ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl ω with elem eqₙ Y (nullable G)
  pred-comp₀ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl ω | no x = predic i refl ω
  pred-comp₀ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl ω | yes x =
    let i₁ = X ∘ u ↦ α ←∷ l Y ∘ β [ v-step (Item.χ i) ∘ Item.ψ i ] in
    let x₁ = pred-comp₀ i₁ refl ω in
    let x₂ = predic i refl ω in
    i₁ ∷ (x₁ ++ x₂)

  pred-comp₁ : {w n : T *} ->
    (ω : EState w n) ->
    (ss : Item w n *) ->
    (rs : Item w n *) ->
    Item w n *
  pred-comp₁ ω ss ε = ε
  pred-comp₁ ω ss (r₁ ∷ rs) =
    let x₁ = pred-comp₀ r₁ refl (Wₙ ω ss) in
    x₁ ++ pred-comp₁ ω ss rs

  pred-comp₂ : {w n : T *} ->
    (ω : EState w n) ->
    (ss : Item w n *) ->
    (rs : Item w n *) ->
    (m : ℕ) ->
    (p : suc (length (Σ.proj₁ (all-items {w} {n}) \\ ss)) ≤ m) ->
    Unique (rs ++ ss) ->
    EState w n
  pred-comp₂ {n} ω ss rs zero () q
  pred-comp₂ {n} ω ss ε (suc m) p q = Wₙ ω ss
  pred-comp₂ {n} ω ss rs@(r₁ ∷ _) (suc m) p q =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let p₂ = wf-pcw₂ x₁ (rs ++ ss) q in
    pred-comp₂ ω (rs ++ ss) x₂ m p₁ p₂

  pred-comp : ∀ {w v} ->
    EState w v ->
    EState w v
  pred-comp {v} w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-items {v}) \\ ε)) in
    pred-comp₂ w ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂

  step₀ : ∀ {w a v} ->
    EState w (a ∷ v) ->
    EState w v
  step₀ {w} {a} {v} ω = scanr a (pred-comp ω)

  parse₀ : ∀ {w v} ->
     EState w v ->
     EState w ε
  parse₀ {v = ε} w = pred-comp w
  parse₀ {v = x ∷ v} w = parse₀ (step₀ w)

  itemize : ∀ w ->
    Σ (λ t -> (t ∈ CFG.rules G) × (fst t ≡ CFG.start G)) * ->
    Item w w *
  itemize w ε = ε
  itemize w (σ (X , β) p₀ ∷ rs) = (X ∘ w ↦ ε ∘ β [ fst p₀ ∘ σ ε refl ]) ∷ itemize w rs

  parse : ∀ w -> EState w ε
  parse w =
    let x₁ = lookup (CFG.start G) (CFG.rules G) in
    parse₀ (start (itemize w x₁))
