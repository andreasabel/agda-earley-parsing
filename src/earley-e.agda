open import base
open import accessible

module earley-e (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T

module parser (G : CFG) where

  open import count N T decidₙ decidₜ

  v-step : ∀ {Y α x β} -> CFG.rules G ∋ (Y , α ++ (x ∷ β)) -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β)
  v-step {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (in₀ x α β) v

  v-unstep : ∀ {Y α x β} -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β) -> CFG.rules G ∋ (Y , α ++ (x ∷ β))
  v-unstep {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (sym (in₀ x α β)) v

  record Item (w : T *) (v : T *) : Set where
    constructor _∘_↦_∘_
    field
      Y : N
      u : T *
      α β : (N ∣ T) *
      .{χ} : CFG.rules G ∋ (Y , α ++ β)
      .{ψ} : (Σ λ t -> t ++ u ≡ w)

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

  eq-N : (a b : N) -> a ≡ b ??
  eq-N X Y = decidₙ X Y

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
  eq-rule (X , α) (Y , β) with eq-N X Y , eq-α α β
  eq-rule (X , α) (X , α) | yes refl , yes refl = yes refl
  eq-rule (X , α) (Y , β) | yes x , no x₁ = no λ {refl → x₁ refl}
  eq-rule (X , α) (Y , β) | no x , x₁ = no λ {refl → x refl}

  eq-item : ∀ {w v} -> (a b : Item w v) -> a ≡ b ??
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) with eq-N X Y , eq-T* j k , eq-α α₁ α₂ , eq-α β₁ β₂
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

  data WSet : T * -> T * -> Set where
    start : {v : T *} ->
      (rs : Item v v * ) ->
      WSet v v

    step : {a : T} {w v : T *} ->
      (ω : WSet w (a ∷ v)) ->
      (rs : Item w v * ) ->
      WSet w v

  V : {w v : T *} ->
    WSet w v ->
    Σ λ t -> t ++ v ≡ w
  V {w} {w} (start rs) = σ ε refl
  V {w} {v} (step ω rs) with V ω
  V {w} {v} (step {a} ω rs) | σ p₁ p₀ = σ (p₁ ←∷ a) (trans (sym (in₀ a p₁ v)) (sym p₀))

  Sₙ : {w v : T *} ->
    WSet w v ->
    Item w v *
  Sₙ (start rs) = rs
  Sₙ (step w rs) = rs

  Wₙ : {w v : T *} ->
    (ω : WSet w v) ->
    (rs : Item w v *) ->
    WSet w v
  Wₙ (start rs) rs₁ = start rs₁
  Wₙ (step w rs) rs₁ = step w rs₁

  Valid : ∀ {w v} -> Item w v -> Set
  Valid {w} {v} i = G ⊢ Item.u i / v ⟶* Item.Y i / Item.β i

  Sound : ∀ {w v} -> WSet w v -> Set
  Sound (start rs) = ∀ {i} -> i ∈ rs -> Valid i
  Sound (step ω rs) = Sound ω × (∀ {i} -> i ∈ rs -> Valid i)

  Complete : ∀ {v w} -> WSet w v -> Set
  Complete {v} ω =
    ∀ {Y u β} ->
    G ⊢ u / v ⟶* Y / β -> ∀ α .χ .ψ ->
    Σ λ i -> (i ∈ Sₙ ω) × (i ≡ (Y ∘ u ↦ α ∘ β [ χ ∘ ψ ]))

  H : ∀ {v w} {ω : WSet w v} -> Sound ω -> (∀ {i} -> i ∈ Sₙ ω -> Valid i)
  H {ω = start rs} s = s
  H {ω = step ω rs} s = snd s

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

  sound-scanner-w₀ : ∀ {a v w} -> ∀ rs ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    (∀ {i} -> i ∈ scanner-w₀ {w} {v} a rs -> Valid i)
  sound-scanner-w₀ ε f ()
  sound-scanner-w₀ ((X ∘ u ↦ α ∘ ε) ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p with decidₜ a b
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p | no x = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) f in-head | yes refl = scanner (f in-head)
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) f (in-tail p) | yes refl
    = sound-scanner-w₀ rs (f ∘ in-tail) p

  complete-scanner-w₀ : ∀ {a v w X u α β} -> ∀ .χ .ψ rs ->
    ∀ i -> i ∈ rs -> i ≡ (X ∘ u ↦ α ∘ r a ∷ β [ χ ∘ ψ ]) ->
    (X ∘ u ↦ α ←∷ r a ∘ β [ v-step χ ∘ ψ ]) ∈ scanner-w₀ {w} {v} a rs
  complete-scanner-w₀ χ ψ ε i () q
  complete-scanner-w₀ χ ψ ((Y ∘ t ↦ γ ∘ ε) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) (in-tail p) refl = complete-scanner-w₀ χ ψ rs _ p refl
  complete-scanner-w₀ χ ψ ((Y ∘ t ↦ γ ∘ l Z ∷ δ) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) (in-tail p) refl = complete-scanner-w₀ χ ψ rs _ p refl
  complete-scanner-w₀ χ ψ ((Y ∘ t ↦ γ ∘ r d ∷ δ) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) p refl           with decidₜ a d
  complete-scanner-w₀ χ ψ ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) in-head refl     | yes refl = in-head
  complete-scanner-w₀ χ ψ ((Y ∘ t ↦ γ ∘ r a ∷ δ) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) (in-tail p) refl | yes refl = in-tail (complete-scanner-w₀ χ ψ rs _ p refl)
  complete-scanner-w₀ χ ψ ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) in-head refl     | no x = void (x refl)
  complete-scanner-w₀ χ ψ ((Y ∘ t ↦ γ ∘ r d ∷ δ) ∷ rs) (X ∘ u ↦ α ∘ r a ∷ β) (in-tail p) refl | no x = complete-scanner-w₀ χ ψ rs _ p refl

  scanner-w : {w v : T *} ->
    (a : T) ->
    WSet w (a ∷ v) ->
    WSet w v
  scanner-w a ω = step ω (scanner-w₀ a (Sₙ ω))

  sound-scanner-w : ∀ {a w v} -> (ω : WSet w (a ∷ v)) ->
    Sound ω -> Sound (scanner-w a ω)
  sound-scanner-w (start rs) s = s , sound-scanner-w₀ rs s
  sound-scanner-w (step w rs) (s , s₁) = s , s₁ , sound-scanner-w₀ rs s₁

  complete-scanner-w : ∀ {a v w X u α β} (ω : WSet w (a ∷ v)) -> ∀ .χ .ψ ->
    Complete ω ->
    G ⊢ u / a ∷ v ⟶* X / r a ∷ β ->
      ∀ i -> i ≡ (X ∘ u ↦ α ←∷ r a ∘ β [ χ ∘ ψ ]) -> i ∈ Sₙ (scanner-w a ω)
  complete-scanner-w {a} {α = α} ω χ ψ c g (X ∘ u ↦ .(α ←∷ r a) ∘ β) refl with c g α (v-unstep χ) ψ
  complete-scanner-w {a} {α = α} ω χ ψ c g (X ∘ u ↦ .(α ←∷ r a) ∘ β) refl | σ .(X ∘ u ↦ α ∘ r a ∷ β) (x , refl) =
    complete-scanner-w₀ (v-unstep χ) ψ (Sₙ ω) _ x refl

  complete-w₀ : ∀ {u v w} ->
    (ω : WSet w v) ->
    Item w u *
  complete-w₀ {u} {v} w           with eq-T* u v
  complete-w₀ {u} {u} w           | yes refl = Sₙ w
  complete-w₀ {u} {v} (start rs)  | no x = ε
  complete-w₀ {u} {v} (step w rs) | no x = complete-w₀ w

  sound-complete-w₀ : ∀ {u v w} (w : WSet w v) ->
    Sound w -> (∀ {i} -> i ∈ complete-w₀ {u} {v} w -> Valid i)
  sound-complete-w₀ {u} {v} w s p           with eq-T* u v
  sound-complete-w₀ {v} {v} w s p           | yes refl = H s p
  sound-complete-w₀ {u} {v} (start rs) s () | no x
  sound-complete-w₀ {u} {v} (step w rs) s p | no x = sound-complete-w₀ w (fst s) p

  complete-complete-w₀ : ∀ {u v w X Y α β} {ω : WSet u w} -> ∀ .χ .ψ ->
    Sound ω ->
    G ⊢ u / v ⟶* X / l Y ∷ β ->
    G ⊢ v / w ⟶* Y / ε ->
    Σ λ (i : Item u v) -> (i ≡ (X ∘ w ↦ α ←∷ l Y ∘ β [ χ ∘ ψ ])) × (i ∈ complete-w₀ ω)
  complete-complete-w₀ χ ψ s g h = {!!}

  complete-w₁ : ∀ {X u v w α} -> ∀ .χ .ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])->
    Item w u * -> Item w v *
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ε = ε
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) with decidₙ X Z
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) | no x = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β [ χ₁ ∘ ψ₁ ]) ∷ rs) | yes refl =
    (Y ∘ u₁ ↦ α₁ ←∷ l X ∘ β [ v-step χ₁ ∘ ψ₁ ]) ∷ complete-w₁ χ ψ _ refl rs

  sound-complete-w₁ : ∀ {X u v w α} -> ∀ .χ .ψ ->
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])) ->
    (rs : Item w u *) ->
    Valid i -> (∀ {j} -> j ∈ rs -> Valid j) ->
    (∀ {j} -> j ∈ complete-w₁ χ ψ i p rs -> Valid j)
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ε v f ()
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) v f q =
    sound-complete-w₁ χ ψ _ refl rs v (f ∘ in-tail) q
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) v f q =
    sound-complete-w₁ χ ψ _ refl rs v (f ∘ in-tail) q
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q       with decidₙ X Z
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q       | no x =
    sound-complete-w₁ χ ψ _ refl rs v (f ∘ in-tail) q
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f in-head | yes refl =
    complet (f in-head) v
  sound-complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f (in-tail q) | yes refl =
    sound-complete-w₁ χ ψ _ refl rs v (f ∘ in-tail) q

  complete-w₂ : ∀ {u X v w α} -> ∀ .χ .ψ ->
    (i : Item w v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ]) ->
    WSet w v ->
    Item w v *
  complete-w₂ χ ψ i p w = complete-w₁ χ ψ i p (complete-w₀ w)

  sound-complete-w₂ : ∀ {u X v w α} -> ∀ .χ .ψ ->
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])) ->
    Valid i -> (w : WSet w v) -> Sound w ->
    (∀ {j} -> j ∈ complete-w₂ χ ψ i p w -> Valid j)
  sound-complete-w₂ χ ψ i p v w s q =
    sound-complete-w₁ χ ψ i p (complete-w₀ w) v (sound-complete-w₀ w s) q

  predict-w₀ : ∀ {u v w X α Y β} -> ∀ .χ .ψ ->
    (Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) * ->
    Item w v *
  predict-w₀ χ ψ ψ₁ i p ε = ε
  predict-w₀ {u} {v} χ ψ ψ₁  (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ ps) =
    (Y ∘ v ↦ ε ∘ γ [ p ∘ ψ₁ ]) ∷ (predict-w₀ {u} χ ψ ψ₁ _ refl ps)

  sound-predict-w₀ : ∀ {u v w X α Y β} -> ∀ .χ .ψ ->
    (ψ₁ : Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ])) ->
    (f : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    Valid i ->
    (∀ {j} -> j ∈ predict-w₀ χ ψ ψ₁ i p f -> Valid j)
  sound-predict-w₀ χ ψ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl ε v ()
  sound-predict-w₀ χ ψ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v in-head = predict p v
  sound-predict-w₀ χ ψ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v (in-tail q) =
    sound-predict-w₀ χ ψ ψ₁ _ refl f v q

  predict-w₁ : ∀ {u X v w α Y β} -> ∀ .χ .ψ ->
    (i : Item w v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    WSet w v ->
    Item w v *
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω with lookup Y (CFG.rules G)
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω | ps = predict-w₀ {u} χ ψ (V ω) _ refl ps

  sound-predict-w₁ : ∀ {v X u w α Y β} -> ∀ .χ .ψ ->
    (i : Item w v) ->  (p : i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ])) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ predict-w₁ χ ψ i p w -> Valid j)
  sound-predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω v s q with lookup Y (CFG.rules G)
  sound-predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω v s q | ps = sound-predict-w₀ χ ψ (V ω) _ refl ps v q

  deduplicate : ∀ {w v} -> Item w v * -> Σ λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with elem eq-item x (Σ.proj₁ (deduplicate as))
  deduplicate (x ∷ as) | yes x₁ = deduplicate as
  deduplicate (x ∷ as) | no x₁ = σ (x ∷ (Σ.proj₁ (deduplicate as))) (u-∷ (Σ.proj₀ (deduplicate as)) x₁)

  sound-deduplicate : ∀ {w v} -> (as : Item w v *) ->
    (∀ {i} -> i ∈ as -> Valid i) ->
    (∀ {i} -> i ∈ Σ.proj₁ (deduplicate as) -> Valid i)
  sound-deduplicate ε f ()
  sound-deduplicate (x ∷ as) f p           with elem eq-item x (Σ.proj₁ (deduplicate as))
  sound-deduplicate (x ∷ as) f p           | yes x₁ = sound-deduplicate as (f ∘ in-tail) p
  sound-deduplicate (x ∷ as) f in-head     | no x₁ = f in-head
  sound-deduplicate (x ∷ as) f (in-tail p) | no x₁ = sound-deduplicate as (f ∘ in-tail) p

  pred-comp-w₀ : ∀ {u v w X α β} -> ∀ .χ .ψ
    (i : Item w v) -> i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ->
    (ω : WSet w v) ->
    Σ {Item w v *} λ as -> Unique as
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ ε) refl w = deduplicate (complete-w₂ {u} χ ψ _ refl w)
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ r a ∷ β) refl w = σ ε u-ε
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w = deduplicate (predict-w₁ {u} χ ψ _ refl w)

  sound-pred-comp-w₀ : ∀ {u v w X α β} -> ∀ .χ .ψ
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ])) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ Σ.proj₁ (pred-comp-w₀ χ ψ i p w) -> Valid j)
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ ε) refl w v s q =
    sound-deduplicate (complete-w₂ {u} χ ψ _ refl w) (sound-complete-w₂ χ ψ _ refl v w s) q
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ r a ∷ β) refl w v s ()
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q =
    sound-deduplicate (predict-w₁ {u} χ ψ _ refl w) (sound-predict-w₁ χ ψ _ refl w v s) q

  pred-comp-w₂ : {w n : T *} ->
    (ω : WSet w n) ->
    (ss : Item w n *) ->
    (rs : Item w n *) ->
    (m : ℕ) ->
    (p : m ≡ suc (length (Σ.proj₁ (all-rules {w} {n}) \\ ss))) ->
    Unique (rs ++ ss) ->
    WSet w n
  pred-comp-w₂ w ss rs zero () q
  pred-comp-w₂ w ss ε (suc m) p q = Wₙ w ss
  pred-comp-w₂ {n} w ss (r₁ ∷ rs) (suc m) p q =
    let x₁ = pred-comp-w₀ _ _ r₁ refl (Wₙ w ss) in
    let x₂ = Σ.proj₁ x₁ \\ (r₁ ∷ (ss ++ rs)) in
    let p₁ = wf-pcw₀ (Σ.proj₀ all-rules) p q  in
    let p₂ = wf-pcw₁ r₁ (Σ.proj₁ x₁) rs ss (Σ.proj₀ x₁) q in
    pred-comp-w₂ w (r₁ ∷ ss) (rs ++ x₂) m p₁ p₂

  sound-Wₙ : ∀ {w v ss} (ω : WSet w v) ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    Sound ω -> Sound (Wₙ ω ss)
  sound-Wₙ (start rs) f s = f
  sound-Wₙ (step ω rs) f s = fst s , f

  sound-pred-comp-w₂ : ∀ {w v} (ω : WSet w v) -> ∀ ss rs m p q ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> Sound (pred-comp-w₂ ω ss rs m p q)
  sound-pred-comp-w₂ ω ss rs zero () q f g s
  sound-pred-comp-w₂ ω ss ε (suc m) p q f g s = sound-Wₙ ω f s
  sound-pred-comp-w₂ ω ss (r₁ ∷ rs) (suc m) p q f g s =
    let x₁ = pred-comp-w₀ _ _ r₁ refl (Wₙ ω ss) in
    let x₂ = Σ.proj₁ x₁ \\ (r₁ ∷ (ss ++ rs)) in
    let p₁ = wf-pcw₀ (Σ.proj₀ all-rules) p q  in
    let p₂ = wf-pcw₁ r₁ (Σ.proj₁ x₁) rs ss (Σ.proj₀ x₁) q in
    sound-pred-comp-w₂ ω (r₁ ∷ ss) (rs ++ x₂) m p₁ p₂
      (λ {in-head → g in-head ; (in-tail x) → f x})
      (s-pcw Valid (g ∘ in-tail) (sound-pred-comp-w₀ _ _ r₁ refl (Wₙ ω ss) (g in-head) (sound-Wₙ ω f s)))
      s

  pred-comp-w : ∀ {w v} ->
    WSet w v ->
    WSet w v
  pred-comp-w {v} w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-rules {v}) \\ ε)) in
    pred-comp-w₂ w ε (Σ.proj₁ x₁) m (app suc refl) x₂

  sound-pred-comp-w : ∀ {w v} {ω : WSet w v} ->
    Sound ω -> Sound (pred-comp-w ω)
  sound-pred-comp-w {w} {v} {ω} s =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-rules {w}) \\ ε)) in
    sound-pred-comp-w₂ ω ε (Σ.proj₁ x₁) m (app suc refl) x₂ (λ ())
      (sound-deduplicate (Sₙ ω) (H s))
      s

  step-w : ∀ {w a v} ->
    WSet w (a ∷ v) ->
    WSet w v
  step-w {w} {a} {v} ω = scanner-w a (pred-comp-w ω)

  sound-step-w : ∀ {w a v} {ω : WSet w (a ∷ v)} ->
    Sound ω -> Sound (step-w ω)
  sound-step-w {ω = ω} s = sound-scanner-w (pred-comp-w ω) (sound-pred-comp-w s)

  parse : ∀ {w v} ->
     WSet w v ->
     WSet w ε
  parse {v = ε} w = pred-comp-w w
  parse {v = x ∷ v} w = parse (step-w w)

  sound-parse : ∀ {w v} -> {ω : WSet w v} ->
    Sound ω -> Sound (parse ω)
  sound-parse {v = ε} s = sound-pred-comp-w s
  sound-parse {v = x ∷ v} s = sound-parse (sound-step-w s)
