open import base

module earley (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T

module parser (G : CFG) where

  open import count N T decidₙ decidₜ

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
  eq-α ε ε = yes refl
  eq-α        ε  (x   ∷ β) = no (λ ())
  eq-α (x   ∷ α)        ε  = no (λ ())
  eq-α (r a ∷ α) (r b ∷ β) with decidₜ a b
  eq-α (r a ∷ α) (r a ∷ β) | yes refl with eq-α α β
  eq-α (r a ∷ α) (r a ∷ α) | yes refl | yes refl = yes refl
  eq-α (r a ∷ α) (r a ∷ β) | yes refl | no x = no (λ {refl → x refl})
  eq-α (r a ∷ α) (r b ∷ β) | no x = no (λ {refl → x refl})
  eq-α (r a ∷ α) (l B ∷ β) = no (λ ())
  eq-α (l A ∷ α) (r b ∷ β) = no (λ ())
  eq-α (l A ∷ α) (l B ∷ β) with decidₙ A B
  eq-α (l A ∷ α) (l A ∷ β) | yes refl with eq-α α β
  eq-α (l A ∷ α) (l A ∷ α) | yes refl | yes refl = yes refl
  eq-α (l A ∷ α) (l A ∷ β) | yes refl | no x = no (λ {refl → x refl})
  eq-α (l A ∷ α) (l B ∷ β) | no x = no (λ {refl → x refl})

  eq-T* : (a b : T *) -> a ≡ b ??
  eq-T* ε ε = yes refl
  eq-T* ε (b ∷ bs) = no (λ ())
  eq-T* (a ∷ as) ε = no (λ ())
  eq-T* (a ∷ as) (b ∷ bs) with decidₜ a b
  eq-T* (a ∷ as) (a ∷ bs) | yes refl with eq-T* as bs
  eq-T* (a ∷ as) (a ∷ bs) | yes refl | yes x = yes (app (a ∷_) x)
  eq-T* (a ∷ as) (a ∷ bs) | yes refl | no x = no λ {refl → x refl}
  eq-T* (a ∷ as) (b ∷ bs) | no x = no λ {refl → x refl}

  eq-rule : (a b : N × (N ∣ T) *) -> a ≡ b ??
  eq-rule (X , α) (Y , β) with decidₙ X Y , eq-α α β
  eq-rule (X , α) (X , α) | yes refl , yes refl = yes refl
  eq-rule (X , α) (Y , β) | yes x , no x₁ = no λ {refl → x₁ refl}
  eq-rule (X , α) (Y , β) | no x , x₁ = no λ {refl → x refl}

  eq-item : ∀ {w v} -> (a b : Item w v) -> a ≡ b ??
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) with decidₙ X Y , eq-T* j k , eq-α α₁ α₂ , eq-α β₁ β₂
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (X ∘ j ↦ α₁ ∘ β₁) | yes refl , yes refl , yes refl , yes refl = yes refl
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | no x₁ , x₂ , x₃ , x₄ = no (λ {refl → x₁ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , no x₂ , x₃ , x₄ = no (λ {refl → x₂ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , no x₃ , x₄ = no (λ {refl → x₃ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , x₃ , no x₄ = no (λ {refl → x₄ refl})

  in₄ : ∀ {rs} {X : N} {α β : _} {x : N ∣ T} -> (X , (α ++ (x ∷ β))) ∈ rs -> (X , ((α ←∷ x) ++ β)) ∈ rs
  in₄ {rs} {X} χ = in₂ (λ q → (X , q) ∈ rs) (in₀ _ _ _) χ

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} -> A -> (A -> B) -> B
  case x of f = f x

  all-rules₀ : ∀ {v w X u α β} -> ∀ χ ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ->
    Σ {Item w v *} λ as ->
      ∀ {γ δ} -> ∀ χ .ψ -> (i : Item w v) -> i ≡ (X ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) -> (Σ λ t ->
        (t ++ δ ≡ β) × (α ++ t ≡ γ)) ->
      i ∈ as
  all-rules₀ χ ψ i@(X ∘ u ↦ α ∘ ε) refl = σ (i ∷ ε) λ
    { χ ψ (X ∘ u ↦ γ ∘ .ε) refl (σ ε (refl , y)) → case trans (sym (++-ε α)) (sym y) of λ {refl → in-head}
    ; χ ψ (X ∘ u ↦ γ ∘ δ) refl (σ (x₁ ∷ t) (() , y))
    }
  all-rules₀ χ ψ i@(X ∘ u ↦ α ∘ x ∷ β) refl with all-rules₀ (in₄ χ) ψ (X ∘ u ↦ α ←∷ x ∘ β [ in₄ χ ∘ ψ ]) refl
  all-rules₀ χ ψ i@(X ∘ u ↦ α ∘ x ∷ β) refl | σ p₁ p₀ = σ (i ∷ p₁) λ
    { χ ψ (X ∘ u ↦ γ ∘ .(x ∷ β)) refl (σ ε (refl , y)) → case trans (sym (++-ε α)) (sym y) of λ {refl → in-head}
    ; χ ψ i@(X ∘ u ↦ γ ∘ δ) refl (σ (x₁ ∷ t) (refl , y)) → in-tail (p₀ χ ψ i refl (σ t (refl , (trans (sym (in₀ _ _ _)) (sym y)))))
    }

  all-rules₁ : ∀ {w v X u β} -> ∀ χ ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ ε ∘ β [ χ ∘ ψ ]) ->
    Σ {Item w v *} λ as ->
      ∀ {u₀ γ δ} -> ∀ χ ψ -> (i : Item w v) -> i ≡ (X ∘ u₀ ↦ γ ∘ δ [ χ ∘ ψ ]) ->
        γ ++ δ ≡ β -> (Σ λ t → t ++ u₀ ≡ u) ->
        i ∈ as
  all-rules₁ χ ψ i@(X ∘ ε ↦ ε ∘ β) refl with all-rules₀ χ ψ i refl
  all-rules₁ χ ψ (X ∘ ε ↦ ε ∘ β) refl | σ p₁ p₀ = σ p₁ λ
    { χ₁ ψ₁ (.X ∘ .ε ↦ γ ∘ δ) refl x₁ (σ ε refl) → p₀ χ₁ ψ₁ _ refl (σ γ (x₁ , refl))
    ; χ₁ ψ₁ (.X ∘ u₀ ↦ γ ∘ δ) refl x₁ (σ (x ∷ t) ())
    }
  all-rules₁ {w} {v} χ ψ@(σ q₀ q₁) i@(X ∘ x ∷ u ↦ ε ∘ β) refl with all-rules₀ χ ψ i refl | all-rules₁ {w} {v} χ (σ (q₀ ←∷ x) (trans (sym (in₀ _ _ _)) (sym q₁))) (X ∘ u ↦ ε ∘ β) refl
  all-rules₁ {w} {v} χ ψ (X ∘ x ∷ u ↦ ε ∘ β) refl | σ p₁ p₀ | σ p₂ p₃ = σ (p₁ ++ p₂) λ
    { χ₁ ψ₁ (.X ∘ .(x ∷ u) ↦ γ ∘ δ) refl x₂ (σ ε refl) → in-l (p₀ χ₁ ψ₁ _ refl (σ γ (x₂ , refl)))
    ; χ₁ ψ₁ (.X ∘ u₀ ↦ γ ∘ δ) refl x₂ (σ (x₁ ∷ p₄) refl) → in-r (p₃ χ₁ ψ₁ _ refl x₂ (σ p₄ refl))
    }

  all-rules₂ : ∀ {w v} ->
    (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) ->
    Σ {Item w v *} λ as ->
      ∀ {X u γ δ} -> ∀ χ ψ -> (i : Item w v) -> i ≡ (X ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) -> (X , γ ++ δ) ∈ rs -> i ∈ as
  all-rules₂ ε f = σ ε λ {χ₁ ψ₁ i x ()}
  all-rules₂ {w} ((Y , α) ∷ rs) f with all-rules₁ (f in-head) (σ ε refl) (Y ∘ w ↦ ε ∘ α) refl
  all-rules₂ {w} ((Y , α) ∷ rs) f | σ p₁ p₀ with all-rules₂ rs (f ∘ in-tail)
  all-rules₂ {w} ((Y , α) ∷ rs) f | σ p₁ p₀ | σ p₂ p₃ = σ (p₁ ++ p₂) λ
    { χ ψ (.Y ∘ u ↦ γ ∘ δ) refl in-head → in-l (p₀ χ ψ _ refl refl ψ)
    ; χ ψ (X ∘ u ↦ γ ∘ δ) refl (in-tail x₁) → in-r (p₃ χ ψ _ refl x₁)
    }

  relevant-χ : ∀ {w v} -> (i : Item w v) -> CFG.rules G ∋ (Item.Y i , Item.α i ++ Item.β i)
  relevant-χ ((Y ∘ j ↦ α ∘ β) {χ}) = elem' eq-rule (Y , α ++ β) (CFG.rules G) χ

  open ε decidₜ

  relevant-ψ : ∀ {w v} -> (i : Item w v) -> Σ λ t -> t ++ Item.u i ≡ w
  relevant-ψ {ε} ((Y ∘ ε ↦ α ∘ β) {χ} {ψ}) = σ ε refl
  relevant-ψ {ε} ((Y ∘ x ∷ u ↦ α ∘ β) {χ} {p}) = void (ε₁ (Σ.proj₀ p))
  relevant-ψ {x ∷ w} {v} (Y ∘ ε ↦ α ∘ β [ χ ∘ p ]) = σ (x ∷ w) (++-ε (x ∷ w))
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) with decidₜ x y | eq-T* w u
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ w ↦ α ∘ β [ χ ∘ p ]) | yes refl | yes refl = σ ε refl
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ p ]) | yes refl | no x₁ with relevant-ψ {w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ ε₅ (Σ.proj₀ p) x₁ ])
  relevant-ψ {x ∷ w} {v} (Y ∘ x ∷ u ↦ α ∘ β [ χ ∘ p ]) | yes refl | no x₁ | σ q₁ q₀ = σ (x ∷ q₁) (app (x ∷_) q₀)
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ w ↦ α ∘ β [ χ ∘ p ]) | no x₂    | yes refl = void (ε₃ x₂ (Σ.proj₀ p))
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) | no x₂    | no x₁ with relevant-ψ {w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ ε₄ (Σ.proj₀ p) x₂ ])
  relevant-ψ {x ∷ w} {v} (Y ∘ y ∷ u ↦ α ∘ β [ χ ∘ p ]) | no x₂    | no x₁ | σ q₁ q₀ = σ (x ∷ q₁) (app (x ∷_) q₀)

  all-rules : ∀ {w} {v} -> Σ λ as -> {i : Item w v} -> i ∈ as
  all-rules with all-rules₂ (CFG.rules G) id
  all-rules | σ p₁ p₀ = σ p₁ λ {i} -> p₀ (relevant-χ i) (relevant-ψ i) i refl (relevant-χ i)

  open Unique Item eq-item

  -- Working set.
  -- State sets the Earley parser constructs.
  -- start rs₀ `step` rs₁ `step` rs₂ ...

  data WSet : T * -> T * -> Set where
    start : {v : T *} ->
      (rs : Item v v * ) ->
      WSet v v

    step : {a : T} {w v : T *} ->
      (ω : WSet w (a ∷ v)) ->
      (rs : Item w v * ) ->
      WSet w v

  -- Invariant: v is suffix of w.

  V : {w v : T *} ->
    WSet w v ->
    Σ λ t -> t ++ v ≡ w
  V {w} {w} (start rs) = σ ε refl
  V {w} {v} (step ω rs) with V ω
  V {w} {v} (step {a} ω rs) | σ p₁ p₀ = σ (p₁ ←∷ a) (trans (sym (in₀ a p₁ v)) (sym p₀))

  -- Get the latest state.

  Sₙ : {w v : T *} ->
    WSet w v ->
    Item w v *
  Sₙ (start rs) = rs
  Sₙ (step w rs) = rs

  -- Replace the latest state.

  Wₙ : {w v : T *} ->
    (ω : WSet w v) ->
    (rs : Item w v *) ->
    WSet w v
  Wₙ (start rs) rs₁ = start rs₁
  Wₙ (step w rs) rs₁ = step w rs₁

  -- Scanning step.

  scanner-w₀ : ∀ {w v} ->
    (a : T) ->
    Item w (a ∷ v)* ->
    Item w v *
  scanner-w₀ a ε = ε
  scanner-w₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β [ χ ∘ ψ ]) ∷ rs) with decidₜ a b
  ... | yes refl = (X ∘ u ↦ α ←∷ r a ∘ β [ v-step χ ∘ ψ ]) ∷ (scanner-w₀ a rs)
  ... | no x = scanner-w₀ a rs

  scanner-w : {w v : T *} ->
    (a : T) ->
    WSet w (a ∷ v) ->
    WSet w v
  scanner-w a ω = step ω (scanner-w₀ a (Sₙ ω))

  complete-w₀ : ∀ {u v w} ->
    (ω : WSet w v) ->
    Item w u *
  complete-w₀ {u} {v} w           with eq-T* u v
  complete-w₀ {u} {u} w           | yes refl = Sₙ w
  complete-w₀ {u} {v} (start rs)  | no x = ε
  complete-w₀ {u} {v} (step w rs) | no x = complete-w₀ w

  complete-w₁ : ∀ {u v w} ->
    (i : Item w v) -> Item.β i ≡ ε ->
    Item w u * -> Item w v *
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ε = ε
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) = complete-w₁ i refl rs
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) = complete-w₁ i refl rs
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) with decidₙ X Z
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) | no x = complete-w₁ i refl rs
  complete-w₁ i@(X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β [ χ₁ ∘ ψ₁ ]) ∷ rs) | yes refl =
    (Y ∘ u₁ ↦ α₁ ←∷ l X ∘ β [ v-step χ₁ ∘ ψ₁ ]) ∷ complete-w₁ i refl rs

  -- For a completed item X ↦ α.ε, get the set of possible ancestors (callers).

  complete-w₂ : ∀ {v w} ->
    (i : Item w v) -> Item.β i ≡ ε ->
    WSet w v ->
    Item w v *
  complete-w₂ {_} {w} i p ω = complete-w₁ {u = Item.u i} i p (complete-w₀ ω)

  predict-w₀ : ∀ {v w Y β} ->
    (Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) -> Item.β i ≡ l Y ∷ β ->
    (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) * ->
    Item w v *
  predict-w₀ ψ₁ i p ε = ε
  predict-w₀ {v} ψ₁ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ ps) =
    (Y ∘ v ↦ ε ∘ γ [ p ∘ ψ₁ ]) ∷ predict-w₀ ψ₁ i refl ps

  predict-w₁ : ∀ {v w Y β} ->
    (i : Item w v) -> Item.β i ≡ l Y ∷ β ->
    WSet w v ->
    Item w v *
  predict-w₁ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl ω =
    predict-w₀ (V ω) i refl (lookup Y (CFG.rules G))

  deduplicate : ∀ {w v} -> Item w v * -> Σ λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with elem eq-item x (Σ.proj₁ (deduplicate as))
  deduplicate (x ∷ as) | yes x₁ = deduplicate as
  deduplicate (x ∷ as) | no x₁ = σ (x ∷ (Σ.proj₁ (deduplicate as))) (u-∷ (Σ.proj₀ (deduplicate as)) x₁)

  pred-comp-w₀ : ∀ {v w} ->
    (i : Item w v) ->
    (ω : WSet w v) ->
    Σ {Item w v *} λ as -> Unique as
  pred-comp-w₀ i@(X ∘ u ↦ α ∘ ε) w = deduplicate (complete-w₂ i refl w)
  pred-comp-w₀ i@(X ∘ u ↦ α ∘ r a ∷ β) w = σ ε u-ε
  pred-comp-w₀ i@(X ∘ u ↦ α ∘ l Y ∷ β) w = deduplicate (predict-w₁ i refl w)

  pred-comp-w₁ : {w n : T *} ->
    (ω : WSet w n) ->
    (ss : Item w n *) ->
    (rs : Item w n *) ->
    Item w n *
  pred-comp-w₁ ω ss ε = ε
  pred-comp-w₁ ω ss (r₁ ∷ rs) =
    let x₁ = pred-comp-w₀ r₁ (Wₙ ω ss) in
    Σ.proj₁ x₁ ++ pred-comp-w₁ ω ss rs

  pred-comp-w₂ : {w n : T *} ->
    (ω : WSet w n) ->
    (ss : Item w n *) ->
    (rs : Item w n *) ->
    (m : ℕ) ->
    (p : suc (length (Σ.proj₁ (all-rules {w} {n}) \\ ss)) ≤ m) ->
    Unique (rs ++ ss) ->
    WSet w n
  pred-comp-w₂ {n} ω ss rs zero () q
  pred-comp-w₂ {n} ω ss ε (suc m) p q = Wₙ ω ss
  pred-comp-w₂ {n} ω ss rs@(r₁ ∷ _) (suc m) p q =
    let x₁ = pred-comp-w₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let p₂ = wf-pcw₂ x₁ (rs ++ ss) q in
    pred-comp-w₂ ω (rs ++ ss) x₂ m p₁ p₂

  pred-comp-w : ∀ {w v} ->
    WSet w v ->
    WSet w v
  pred-comp-w {v} w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-rules {v}) \\ ε)) in
    pred-comp-w₂ w ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂

  -- om alla scannade items finns i ω, sȧ Complete (pred-comp-w ω)
--  complete-pred-comp-w : ∀ {t u v a X α β} -> ∀ .χ .ψ ->
--    (ω : WSet t v) ->
--    G ⊢ u / a ∷ v ⟶* X / r a ∷ β ->
--    (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ Sₙ ω ->
--    Complete (pred-comp-w ω)
--  complete-pred-comp-w χ ψ ω g p = {!!}

  step-w : ∀ {w a v} ->
    WSet w (a ∷ v) ->
    WSet w v
  step-w {w} {a} {v} ω = scanner-w a (pred-comp-w ω)

  parse : ∀ {w v} ->
     WSet w v ->
     WSet w ε
  parse {v = ε} w = pred-comp-w w
  parse {v = x ∷ v} w = parse (step-w w)
