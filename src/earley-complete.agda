open import base

module earley-complete (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T
open import earley N T decidₙ decidₜ

module parser-sound (G : CFG) where

  open parser G
  open import count N T decidₙ decidₜ
  open Unique Item eq-item
  
  -- Complete state sets (contain all derivable items).

  Complete₀ : ∀ {v w} -> WSet w v -> Set
  Complete₀ {v} ω =
    ∀ {Y u β} ->
    G ⊢ u / v ⟶* Y / β -> ∀ α .χ .ψ ->
    Σ λ i -> (i ∈ Sₙ ω) × (i ≡ (Y ∘ u ↦ α ∘ β [ χ ∘ ψ ]))

  Complete* : ∀ {v w} -> Item w v * -> Set
  Complete* {v} rs =
    ∀ {Y u β} ->
    G ⊢ u / v ⟶* Y / β -> ∀ α .χ .ψ ->
    Σ λ i -> (i ∈ rs) × (i ≡ (Y ∘ u ↦ α ∘ β [ χ ∘ ψ ]))

  Complete : ∀ {v w} -> WSet w v -> Set
  Complete (start rs) = Complete₀ (start rs)
  Complete (step ω rs) = Complete ω × Complete₀ (step ω rs)

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

  complete-scanner-w : ∀ {a v w X u α β} (ω : WSet w (a ∷ v)) -> ∀ .χ .ψ ->
    Complete₀ ω ->
    G ⊢ u / a ∷ v ⟶* X / r a ∷ β ->
      ∀ i -> i ≡ (X ∘ u ↦ α ←∷ r a ∘ β [ χ ∘ ψ ]) -> i ∈ Sₙ (scanner-w a ω)
  complete-scanner-w {a} {α = α} ω χ ψ c g (X ∘ u ↦ .(α ←∷ r a) ∘ β) refl with c g α (v-unstep χ) ψ
  complete-scanner-w {a} {α = α} ω χ ψ c g (X ∘ u ↦ .(α ←∷ r a) ∘ β) refl | σ .(X ∘ u ↦ α ∘ r a ∷ β) (x , refl) =
    complete-scanner-w₀ (v-unstep χ) ψ (Sₙ ω) _ x refl

  Contains : ∀ {v w} -> ∀ X u α β .χ .ψ -> WSet w v -> Set
  Contains X u α β χ ψ (start rs) = (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs
  Contains X u α β χ ψ (step ω rs) = Contains X u α β χ ψ ω ∣ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs

--  complete-complete-w₀ : ∀ {u v w X t α β} (ω : WSet w v) -> ∀ .χ .ψ ->
--    Contains X t α β χ ψ ω ->
--    (X ∘ t ↦ α ∘ β [ χ ∘ ψ ]) ∈ complete-w₀ {u} ω
--  complete-complete-w₀ {u} {v} ω χ ψ g                with eq-T* u v
--  complete-complete-w₀ {u} {u} ω χ ψ g                | yes refl = {!!}
--  complete-complete-w₀ {u} {v} (start rs) χ ψ g       | no x = {!!}
--  complete-complete-w₀ {u} {v} (step ω rs) χ ψ (r x₁) | no x = {!!}
--  complete-complete-w₀ {u} {v} (step ω rs) χ ψ (l x₁) | no x = {!!}

  _≋_ : ∀ {t u v X α β} -> (i : Item t v) -> G ∙ t ⊢ u / v ⟶* X / α ∙ β -> Set
  _≋_ {t} {u} {v} {X} {α} {β} i g = (Item.Y i , Item.u i , Item.α i , Item.β i) ≡ (X , u , α , β)

  ≋-β : ∀ {t u v X α β} -> ∀ i -> (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) -> i ≋ g -> Item.β i ≡ β
  ≋-β i g refl = refl

  eq-prop : {a b : T *} (P : Item a b -> Set) (i : Item b b) -> a ≡ b -> Set
  eq-prop P i refl = P i

  test : ∀ {t v} ->
    {P : Item t v -> Set} ->

    (∀ {u a X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      P i
    ) ->

    (∀ {β} ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> Σ λ t -> eq-prop P i t
    ) ->

    (∀ {u X Y α β δ} (x : (Y , δ) ∈ CFG.rules G) ->
      (i j : Item t v) ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
      (i ≋ g) -> P i ->
      (j ≋ predict x g) -> P j
    ) ->

    (∀ {u w X Y α β γ} ->
      (j k : Item t v) ->
      (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
      (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
      (j ≋ h) -> P j ->
      (k ≋ complet g h) -> P k
    ) ->

    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
      (i : Item t v) ->
      i ≋ g ->
      P i
    )
  test f ini h c (initial x) i refl with ini x i refl
  ... | σ refl proj₀ = proj₀
  test f ini h c (scanner g) i refl = f g i refl
  test f ini h c (predict x g) i@(X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) refl =
    h x (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i g refl (test f ini h c g _ refl) refl
  test f ini h c (complet g g₁) i p =
    c (_ ∘ _ ↦ _ ∘ _ [ in-g g₁ ∘ suff-g₂ g ]) i g g₁ refl (test f ini h c g₁ _ refl) p

--  complete-complete-w₂ : ∀ {t u v w X Y β γ} -> ∀ α .χ .ψ .χ₁ .ψ₁ ->
--    (ω : WSet t w) ->
--    (i : Item t w) ->
--    (p : i ≡ (Y ∘ v ↦ γ ∘ ε)) ->
--    G ⊢ u / v ⟶* X / l Y ∷ β ->
--    G ⊢ v / w ⟶* Y / ε ->
--    (X ∘ u ↦ α ←∷ l Y ∘ β [ χ₁ ∘ ψ₁ ]) ∈ complete-w₂ χ ψ i p ω
--  complete-complete-w₂ α χ ψ χ₁ ψ₁ ω i p g h =
--    let c₁ = complete-complete-w₀ ω (in₁ (app (_ ,_) (sym (in₀ _ _ _))) χ₁) ψ₁ {!!} in
--    complete-complete-w₁ α χ ψ χ₁ ψ₁ (complete-w₀ ω) i p c₁ g h

  complete-predict-w₀ : ∀ {t u v X Y α β δ} ->
    (ψ₀ : Σ λ s -> s ++ v ≡ t) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / ε ∙ δ) ->
    (p : i ≋ g) ->
    (q : j ≋ h) ->
    (rs : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    (Σ λ e -> σ (Y , δ) e ∈ rs) ->
    j ∈ predict-w₀ ψ₀ i (≋-β i g p) rs
  complete-predict-w₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl ε (σ p₁ ())
  complete-predict-w₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , γ) (p , refl) ∷ rs) q with eq-α γ δ
  complete-predict-w₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , δ) (p , refl) ∷ rs) q | yes refl = in-head
  complete-predict-w₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , δ) (p , refl) ∷ rs) (σ (q , refl) in-head) | no x = void (x refl)
  complete-predict-w₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , γ) (p , refl) ∷ rs) (σ q₁ (in-tail q₀)) | no x =
    in-tail (complete-predict-w₀ ψ₀ _ _ g h refl refl rs (σ q₁ q₀))

  complete-predict-w₁ : ∀ {t u v X Y α β δ} ->
    (ω : WSet t v) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (x : CFG.rules G ∋ (Y , δ)) ->
    (p : i ≋ g) ->
    j ≋ predict x g ->
    j ∈ predict-w₁ i (≋-β i g p) ω
  complete-predict-w₁ ω i@(X ∘ u ↦ α ∘ l Y ∷ β) j g x refl q =
    complete-predict-w₀ _ i j g (predict x g) refl q (lookup Y (CFG.rules G)) (lookup-sound x)

  complete-deduplicate : ∀ {w v i} -> (as : Item w v *) -> i ∈ as -> i ∈ Σ.proj₁ (deduplicate as)
  complete-deduplicate ε ()
  complete-deduplicate (x ∷ as) p with elem eq-item x (Σ.proj₁ (deduplicate as))
  complete-deduplicate (x ∷ as) in-head     | yes x₁ = x₁
  complete-deduplicate (x ∷ as) (in-tail p) | yes x₁ = complete-deduplicate as p
  complete-deduplicate (x ∷ as) in-head     | no x₁ = in-head
  complete-deduplicate (x ∷ as) (in-tail p) | no x₁ = in-tail (complete-deduplicate as p)

  complete₁-pred-comp-w₀ : ∀ {t u v X Y α β δ} ->
    (ω : WSet t v) ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    j ≋ predict x g ->
      j ∈ Σ.proj₁ (pred-comp-w₀ i ω)
  complete₁-pred-comp-w₀ ω x i@(Y ∘ u ↦ α ∘ l Z ∷ β) j@(Z ∘ u₁ ↦ ε ∘ β₁ [ χ₁ ∘ ψ₁ ]) g refl refl =
    let x₁ = complete-predict-w₁ ω i j g x refl refl in
    complete-deduplicate (predict-w₁ i refl ω) x₁

  complete₂-pred-comp-w₀ : ∀ {t u v w X Y α β γ} ->
    (ω : WSet t w) ->
    (i j : Item t w) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    i ≋ h -> 
    j ≋ complet g h ->
      j ∈ Σ.proj₁ (pred-comp-w₀ i ω)
  complete₂-pred-comp-w₀ ω i j g h refl refl =
    complete-deduplicate (complete-w₂ i refl ω) {!!}

  complete₂-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    ∀ {u X Y α β δ} ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q) ->
    j ≋ predict x g -> j ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₂-pred-comp-w₂ ω x i j g p p' q = {!!}

  complete₃-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    ∀ {u w X Y α β γ} ->
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ Sₙ (pred-comp-w₂ ω ss rs m p q) ->
    k ≋ complet g h -> k ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₃-pred-comp-w₂ ω j k g h p p' q = {!!}

  complete-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    (∀ {u a X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
    ) ->
    (∀ {β} ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> Σ λ z -> eq-prop (λ i -> i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)) i z
    ) ->
    ∀ {u X α β} ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
    (i : Item t v) ->
    i ≋ g -> i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete-pred-comp-w₂ {t} {v} {ss} {rs} {m} {p} {q} ω s u g i e =
    test {P = λ i -> i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)}
      s
      u
      (complete₂-pred-comp-w₂ {ss = ss} {rs} {m} {p} {q} ω)
      (complete₃-pred-comp-w₂ {ss = ss} {rs} {m} {p} {q} ω)
      g i e

