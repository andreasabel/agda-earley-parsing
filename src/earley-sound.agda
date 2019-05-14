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

  sound-scanner-w : ∀ {a w v} -> (ω : WSet w (a ∷ v)) ->
    Sound ω -> Sound (scanner-w a ω)
  sound-scanner-w (start rs) s = s , sound-scanner-w₀ rs s
  sound-scanner-w (step w rs) (s , s₁) = s , s₁ , sound-scanner-w₀ rs s₁

  sound-complete-w₀ : ∀ {u v w} (w : WSet w v) ->
    Sound w -> (∀ {i} -> i ∈ complete-w₀ {u} {v} w -> Valid i)
  sound-complete-w₀ {u} {v} w s p           with eq-T* u v
  sound-complete-w₀ {v} {v} w s p           | yes refl = H s p
  sound-complete-w₀ {u} {v} (start rs) s () | no x
  sound-complete-w₀ {u} {v} (step w rs) s p | no x = sound-complete-w₀ w (fst s) p

  sound-complete-w₁ : ∀ {u v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    (q : Item.u i ≡ u) ->
    (rs : Item w u *) ->
    Valid i -> (∀ {j} -> j ∈ rs -> Valid j) ->
    (∀ {j} -> j ∈ complete-w₁ i p rs -> Valid j)
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ε v f ()
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) v f q = sound-complete-w₁ _ refl refl rs v (f ∘ in-tail) q
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) v f q = sound-complete-w₁ _ refl refl rs v (f ∘ in-tail) q
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q           with decidₙ X Z
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) v f q           | no x = sound-complete-w₁ _ refl refl rs v (f ∘ in-tail) q
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f in-head     | yes refl = complet (f in-head) v
  sound-complete-w₁ (X ∘ u ↦ α ∘ ε) refl refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β) ∷ rs) v f (in-tail q) | yes refl = sound-complete-w₁ _ refl refl rs v (f ∘ in-tail) q

  sound-complete-w₂ : ∀ {v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    Valid i -> (ω : WSet w v) -> Sound ω ->
    (∀ {j} -> j ∈ complete-w₂ i p ω -> Valid j)
  sound-complete-w₂ i p v ω s q =
    sound-complete-w₁ i p refl (complete-w₀ ω) v (sound-complete-w₀ ω s) q

  sound-predict-w₀ : ∀ {v w  Y β} ->
    (ψ₁ : Σ λ t -> t ++ v ≡ w) ->
    (i : Item w v) -> (p : Item.β i ≡ l Y ∷ β) ->
    (f : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    Valid i ->
    (∀ {j} -> j ∈ predict-w₀ ψ₁ i p f -> Valid j)
  sound-predict-w₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl ε v ()
  sound-predict-w₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v in-head = predict p v
  sound-predict-w₀ ψ₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v (in-tail q) =
    sound-predict-w₀ ψ₁ _ refl f v q

  sound-predict-w₁ : ∀ {v w Y β} ->
    (i : Item w v) ->  (p : Item.β i ≡ l Y ∷ β) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ predict-w₁ i p w -> Valid j)
  sound-predict-w₁ (X ∘ u ↦ α ∘ l Y ∷ β) refl ω v s q =
    sound-predict-w₀ (V ω) _ refl (lookup Y (CFG.rules G)) v q

  sound-deduplicate : ∀ {w v} -> (as : Item w v *) ->
    (∀ {i} -> i ∈ as -> Valid i) ->
    (∀ {i} -> i ∈ Σ.proj₁ (deduplicate as) -> Valid i)
  sound-deduplicate ε f ()
  sound-deduplicate (x ∷ as) f p           with elem eq-item x (Σ.proj₁ (deduplicate as))
  sound-deduplicate (x ∷ as) f p           | yes x₁ = sound-deduplicate as (f ∘ in-tail) p
  sound-deduplicate (x ∷ as) f in-head     | no x₁ = f in-head
  sound-deduplicate (x ∷ as) f (in-tail p) | no x₁ = sound-deduplicate as (f ∘ in-tail) p

  sound-pred-comp-w₀ : ∀ {u v w X α β} -> ∀ .χ .ψ
    (i : Item w v) -> (p : i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ])) ->
    (w : WSet w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ Σ.proj₁ (pred-comp-w₀ i w) -> Valid j)
  sound-pred-comp-w₀ χ ψ i@(X ∘ u ↦ α ∘ ε) refl w v s q =
    sound-deduplicate (complete-w₂ i refl w) (sound-complete-w₂ i refl v w s) q
  sound-pred-comp-w₀ χ ψ i@(X ∘ u ↦ α ∘ r a ∷ β) refl w v s ()
  sound-pred-comp-w₀ χ ψ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q =
    sound-deduplicate (predict-w₁ i refl w) (sound-predict-w₁ i refl w v s) q

  sound-Wₙ : ∀ {w v ss} (ω : WSet w v) ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    Sound ω -> Sound (Wₙ ω ss)
  sound-Wₙ (start rs) f s = f
  sound-Wₙ (step ω rs) f s = fst s , f

  sound-pred-comp-w₁ : ∀ {w v} (ω : WSet w v) -> ∀ ss rs ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> (∀ {i} -> i ∈ pred-comp-w₁ ω ss rs -> Valid i)
  sound-pred-comp-w₁ ω ss ε f g s ()
  sound-pred-comp-w₁ ω ss (x ∷ rs) f g s p =
    let x₁ = sound-pred-comp-w₀ _ _ x refl (Wₙ ω ss) (g in-head) (sound-Wₙ ω f s) in
    let x₂ = sound-pred-comp-w₁ ω ss rs f (g ∘ in-tail) s in
    in-either Valid x₁ x₂ p

  sound-pred-comp-w₂ : ∀ {w v} (ω : WSet w v) -> ∀ ss rs m p q ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> Sound (pred-comp-w₂ ω ss rs m p q)
  sound-pred-comp-w₂ ω ss rs zero () q f g s
  sound-pred-comp-w₂ ω ss ε (suc m) p q f g s = sound-Wₙ ω f s
  sound-pred-comp-w₂ ω ss rs@(r₁ ∷ _) (suc m) p q f g s =
    let x₁ = pred-comp-w₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q  in
    let p₂ = wf-pcw₂ x₁ (rs ++ ss) q in
    let p₃ = sound-pred-comp-w₁ ω ss rs f g s in
    let p₄ = s-pcw₀ Valid p₃ in
    sound-pred-comp-w₂ ω (rs ++ ss) x₂ m p₁ p₂ (in-either Valid g f) p₄ s

  sound-pred-comp-w : ∀ {w v} {ω : WSet w v} ->
    Sound ω -> Sound (pred-comp-w ω)
  sound-pred-comp-w {w} {v} {ω} s =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-rules {w}) \\ ε)) in
    sound-pred-comp-w₂ ω ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂ (λ ())
      (sound-deduplicate (Sₙ ω) (H s))
      s

  sound-step-w : ∀ {w a v} {ω : WSet w (a ∷ v)} ->
    Sound ω -> Sound (step-w ω)
  sound-step-w {ω = ω} s = sound-scanner-w (pred-comp-w ω) (sound-pred-comp-w s)

  sound-parse : ∀ {w v} -> {ω : WSet w v} ->
    Sound ω -> Sound (parse ω)
  sound-parse {v = ε} s = sound-pred-comp-w s
  sound-parse {v = x ∷ v} s = sound-parse (sound-step-w s)
