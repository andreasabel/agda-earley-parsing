open import base

module earley-sound (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T
open import earley N T decidₙ decidₜ

module parser-sound (G : CFG) where

  open parser G
  open import count N T decidₙ decidₜ
  open Unique Item eq-item

    -- Valid items, those that are Earley-derivable.

  Valid : ∀ {w v} -> Item w v -> Set
  Valid {w} {v} i = G ⊢ Item.u i / v ⟶* Item.Y i / Item.β i

  -- Sound state sets (contain only valid items).

  Sound : ∀ {w v} -> WSet w v -> Set
  Sound (start rs) = ∀ {i} -> i ∈ rs -> Valid i
  Sound (step ω rs) = Sound ω × (∀ {i} -> i ∈ rs -> Valid i)

  H : ∀ {v w} {ω : WSet w v} -> Sound ω -> (∀ {i} -> i ∈ Sₙ ω -> Valid i)
  H {ω = start rs} s = s
  H {ω = step ω rs} s = snd s

  sound-scanr₀ : ∀ {a v w} -> ∀ rs ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    (∀ {i} -> i ∈ scanr₀ {w} {v} a rs -> Valid i)
  sound-scanr₀ ε f ()
  sound-scanr₀ ((X ∘ u ↦ α ∘ ε) ∷ rs) f p = sound-scanr₀ rs (f ∘ in-tail) p
  sound-scanr₀ ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) f p = sound-scanr₀ rs (f ∘ in-tail) p
  sound-scanr₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p with decidₜ a b
  ... | no x = sound-scanr₀ rs (f ∘ in-tail) p
  ... | yes refl with p
  ... | in-head    = scanner (f in-head)
  ... | in-tail p₁ = sound-scanr₀ rs (f ∘ in-tail) p₁

  sound-scanr : ∀ {a w v} -> (ω : WSet w (a ∷ v)) ->
    Sound ω -> Sound (scanr a ω)
  sound-scanr (start rs) s = s , sound-scanr₀ rs s
  sound-scanr (step w rs) (s , s₁) = s , s₁ , sound-scanr₀ rs s₁

  sound-compl₀ : ∀ {u v w} (w : WSet w v) ->
    Sound w -> (∀ {i} -> i ∈ compl₀ {u} {v} w -> Valid i)
  sound-compl₀ {u} {v} w s p           with eq-T* u v
  sound-compl₀ {v} {v} w s p           | yes refl = H s p
  sound-compl₀ {u} {v} (start rs) s () | no x
  sound-compl₀ {u} {v} (step w rs) s p | no x = sound-compl₀ w (fst s) p

  sound-compl₁ : ∀ {u v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    (q : Item.u i ≡ u) ->
    (rs : Item w u *) ->
    Valid i -> (∀ {j} -> j ∈ rs -> Valid j) ->
    (∀ {j} -> j ∈ compl₁ i p rs -> Valid j)
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ε v f ()
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) v f q = sound-compl₁ _ refl refl rs v (f ∘ in-tail) q
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) v f q = sound-compl₁ _ refl refl rs v (f ∘ in-tail) q
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q           with decidₙ X Z
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q           | no x = sound-compl₁ _ refl refl rs v (f ∘ in-tail) q
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f in-head     | yes refl = complet (f in-head) v
  sound-compl₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f (in-tail q) | yes refl = sound-compl₁ _ refl refl rs v (f ∘ in-tail) q

  sound-compl₂ : ∀ {v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    Valid i -> (ω : WSet w v) -> Sound ω ->
    (∀ {j} -> j ∈ compl₂ i p ω -> Valid j)
  sound-compl₂ i p v ω s q =
    sound-compl₁ i p refl (compl₀ ω) v (sound-compl₀ ω s) q

  sound-predict₀ : ∀ {v w  Y β} ->
    (ψ₁ : Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) -> (p : Item.β i ≡ l Y ∷ β) ->
    (f : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    Valid i ->
    (∀ {j} -> j ∈ predict₀ ψ₁ i p f -> Valid j)
  sound-predict₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl ε v ()
  sound-predict₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v in-head = predict p v
  sound-predict₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v (in-tail q) =
    sound-predict₀ ψ₁ _ refl f v q

  sound-predict₁ : ∀ {v w Y β} ->
    (i : Item w v) ->  (p : Item.β i ≡ l Y ∷ β) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ predict₁ i p w -> Valid j)
  sound-predict₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω v s q =
    sound-predict₀ (V ω) _ refl (lookup Y (CFG.rules G)) v q

  sound-deduplicate : ∀ {w v} -> (as : Item w v *) ->
    (∀ {i} -> i ∈ as -> Valid i) ->
    (∀ {i} -> i ∈ Σ.proj₁ (deduplicate as) -> Valid i)
  sound-deduplicate ε f ()
  sound-deduplicate (x ∷ as) f p           with elem eq-item x (Σ.proj₁ (deduplicate as))
  sound-deduplicate (x ∷ as) f p           | yes x₁ = sound-deduplicate as (f ∘ in-tail) p
  sound-deduplicate (x ∷ as) f in-head     | no x₁ = f in-head
  sound-deduplicate (x ∷ as) f (in-tail p) | no x₁ = sound-deduplicate as (f ∘ in-tail) p

  sound-pred-comp₀ : ∀ {u v w X α β} -> ∀ .χ .ψ
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ])) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ Σ.proj₁ (pred-comp₀ i w) -> Valid j)
  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ ε) refl w v s q =
    sound-deduplicate (compl₂ i refl w) (sound-compl₂ i refl v w s) q
  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ r a ∷ β) refl w v s ()
  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q =
    sound-deduplicate (predict₁ i refl w) (sound-predict₁ i refl w v s) q

  soundₙ : ∀ {w v ss} (ω : WSet w v) ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    Sound ω -> Sound (Wₙ ω ss)
  soundₙ (start rs) f s = f
  soundₙ (step ω rs) f s = fst s , f

  sound-pred-comp₁ : ∀ {w v} (ω : WSet w v) -> ∀ ss rs ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> (∀ {i} -> i ∈ pred-comp₁ ω ss rs -> Valid i)
  sound-pred-comp₁ ω ss ε f g s ()
  sound-pred-comp₁ ω ss (x ∷ rs) f g s p =
    let x₁ = sound-pred-comp₀ _ _ x refl (Wₙ ω ss) (g in-head) (soundₙ ω f s) in
    let x₂ = sound-pred-comp₁ ω ss rs f (g ∘ in-tail) s in
    in-either Valid x₁ x₂ p

  sound-pred-comp₂ : ∀ {w v} (ω : WSet w v) -> ∀ ss rs m p q ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> Sound (pred-comp₂ ω ss rs m p q)
  sound-pred-comp₂ ω ss rs zero () q f g s
  sound-pred-comp₂ ω ss ε (suc m) p q f g s = soundₙ ω f s
  sound-pred-comp₂ ω ss rs@(r₁ ∷ _) (suc m) p q f g s =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q  in
    let p₂ = wf-pcw₂ x₁ (rs ++ ss) q in
    let p₃ = sound-pred-comp₁ ω ss rs f g s in
    let p₄ = s-pcw₀ Valid p₃ in
    sound-pred-comp₂ ω (rs ++ ss) x₂ m p₁ p₂ (in-either Valid g f) p₄ s

  sound-pred-comp : ∀ {w v} {ω : WSet w v} ->
    Sound ω -> Sound (pred-comp ω)
  sound-pred-comp {w} {v} {ω} s =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-rules {w}) \\ ε)) in
    sound-pred-comp₂ ω ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂ (λ ())
      (sound-deduplicate (Sₙ ω) (H s))
      s

  sound-step : ∀ {w a v} {ω : WSet w (a ∷ v)} ->
    Sound ω -> Sound (step₀ ω)
  sound-step {ω = ω} s = sound-scanr (pred-comp ω) (sound-pred-comp s)

  sound-parse₀ : ∀ {w v} -> {ω : WSet w v} ->
    Sound ω -> Sound (parse₀ ω)
  sound-parse₀ {v = ε} s = sound-pred-comp s
  sound-parse₀ {v = x ∷ v} s = sound-parse₀ (sound-step s)
