open import base

module earley-sound (N T : Set) (eqₙ : Dec N) (eqₜ : Dec T) where

open import grammar N T
open import earley N T eqₙ eqₜ

module parser-sound (G : CFG) where

  open parser G
  open import count N T eqₙ eqₜ
  open Unique Item eq-item

    -- Valid items, those that are Earley-derivable.

  Valid : ∀ {w v} -> Item w v -> Set
  Valid {w} {v} i = G ∙ w ⊢ Item.u i / v ⟶* Item.Y i / Item.α i ∙ Item.β i

  -- Sound state sets (contain only valid items).

  Sound : ∀ {w v} -> EState w v -> Set
  Sound (start rs) = ∀ {i} -> i ∈ rs -> Valid i
  Sound (step ω rs) = Sound ω × (∀ {i} -> i ∈ rs -> Valid i)

  sound-scanr₀ : ∀ {a v w} -> ∀ rs ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    (∀ {i} -> i ∈ scanr₀ {w} {v} a rs -> Valid i)

  sound-scanr₀ ε f ()
  
  sound-scanr₀ ((X ∘ u ↦ α ∘ ε) ∷ rs) f p = 
    sound-scanr₀ rs (f ∘ in-tail) p

  sound-scanr₀ ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) f p = 
    sound-scanr₀ rs (f ∘ in-tail) p

  sound-scanr₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p with eqₜ a b
  ... | no x = sound-scanr₀ rs (f ∘ in-tail) p
  ... | yes refl with p
  ...            | in-head    = scanner (f in-head)
  ...            | in-tail p₁ = sound-scanr₀ rs (f ∘ in-tail) p₁

  sound-scanr : ∀ {a w v} -> (ω : EState w (a ∷ v)) ->
    Sound ω -> Sound (scanr a ω)
  sound-scanr (start rs) s = s , sound-scanr₀ rs s
  sound-scanr (step w rs) (s , s₁) = s , s₁ , sound-scanr₀ rs s₁

  sound-compl₀ : ∀ {u v w} (w : EState w v) ->
    Sound w -> (∀ {i} -> i ∈ compl₀ {u} {v} w -> Valid i)
  sound-compl₀ {u} {v} w s p           with eq-T* u v
  sound-compl₀ {v} {v} (start rs) s p  | yes refl = s p
  sound-compl₀ {v} {v} (step w rs) s p | yes refl = snd s p
  sound-compl₀ {u} {v} (start rs) s () | no x
  sound-compl₀ {u} {v} (step w rs) s p | no x = sound-compl₀ w (fst s) p

  sound-compl₁ : ∀ {u v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    (q : Item.u i ≡ u) ->
    (rs : Item w u *) ->
    Valid i -> (∀ {j} -> j ∈ rs -> Valid j) ->
    (∀ {j} -> j ∈ compl₁ i p rs -> Valid j)

  sound-compl₁ i refl refl ε v f ()

  sound-compl₁ i refl refl ((Y ∘ u ↦ α ∘ ε) ∷ rs) v f q =
    sound-compl₁ _ refl refl rs v (f ∘ in-tail) q

  sound-compl₁ i refl refl ((Y ∘ u ↦ α ∘ r a ∷ β) ∷ rs) v f q =
    sound-compl₁ _ refl refl rs v (f ∘ in-tail) q

  sound-compl₁ i refl refl ((Y ∘ u ↦ α ∘ l Z ∷ β) ∷ rs) v f with eqₙ (Item.Y i) Z
  ... | no x = sound-compl₁ _ refl refl rs v (f ∘ in-tail)
  ... | yes refl =
    λ { in-head → complet (f in-head) v
      ; (in-tail q) → sound-compl₁ _ refl refl rs v (f ∘ in-tail) q
      }

  sound-compl : ∀ {v w} ->
    (i : Item w v) ->
    (p : Item.β i ≡ ε) ->
    Valid i -> (ω : EState w v) -> Sound ω ->
    (∀ {j} -> j ∈ compl i p ω -> Valid j)
  sound-compl i p v ω s q =
    sound-compl₁ i p refl (compl₀ ω) v (sound-compl₀ ω s) q

  soundₙ : ∀ {w v ss} (ω : EState w v) ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    Sound ω -> Sound (Wₙ ω ss)
  soundₙ (start rs) f s = f
  soundₙ (step ω rs) f s = fst s , f

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

  sound-predic : ∀ {v w Y β} ->
    (i : Item w v) ->  (p : Item.β i ≡ l Y ∷ β) ->
    (w : EState w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ predic i p w -> Valid j)
  sound-predic (X ∘ u ↦ α ∘ l Y ∷ β) refl ω v s q =
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
    (w : EState w v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ pred-comp₀ i refl w -> Valid j)

  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ ε) refl w v s q =
    sound-compl i refl v w s q

  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ r a ∷ β) refl w v s ()

  sound-pred-comp₀ χ ψ i@(X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q with elem eqₙ Y (nullable G)
  ... | no x = sound-predic i refl w v s q
  ... | yes x =
    let i₁ = X ∘ u ↦ α ←∷ l Y ∘ β in
    let rs₁ = predic i refl w in
    let rs₂ = pred-comp₀ i₁ refl w in
    case in-either (i₁ ∷ rs₂) rs₁ q of
      λ { (r x₁) → sound-predic i refl w v s x₁
        ; (l in-head) →
          let x₁ = nullable-sound x in
          complet v (Σ.proj₀ x₁)
        ; (l (in-tail x₁)) →
          let y₀ = nullable-sound x in
          let y₁ = complet v (Σ.proj₀ y₀) in
          let y₂ = X ∘ u ↦ α ←∷ l Y ∘ β in
          sound-pred-comp₀ {β = β} (v-step χ) ψ y₂ refl w y₁ s x₁
        }

  sound-pred-comp₁ : ∀ {w v} (ω : EState w v) -> ∀ ss rs ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> (∀ {i} -> i ∈ pred-comp₁ ω ss rs -> Valid i)
  sound-pred-comp₁ ω ss ε f g s ()
  sound-pred-comp₁ ω ss (x ∷ rs) f g s p =
    let x₁ = sound-pred-comp₀ _ _ x refl (Wₙ ω ss) (g in-head) (soundₙ ω f s) in
    let x₂ = sound-pred-comp₁ ω ss rs f (g ∘ in-tail) s in
    in-both Valid x₁ x₂ p

  sound-pred-comp₂ : ∀ {w v} (ω : EState w v) -> ∀ ss rs m p q ->
    (∀ {i} -> i ∈ ss -> Valid i) ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    Sound ω -> Sound (pred-comp₂ ω ss rs m p q)
  sound-pred-comp₂ ω ss rs zero () q f g s
  sound-pred-comp₂ ω ss ε (suc m) p q f g s = soundₙ ω f s
  sound-pred-comp₂ ω ss rs@(r₁ ∷ _) (suc m) p q f g s =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q  in
    let p₂ = wf-pcw₂ x₁ (rs ++ ss) q in
    let p₃ = sound-pred-comp₁ ω ss rs f g s in
    let p₄ = s-pcw₀ Valid p₃ in
    sound-pred-comp₂ ω (rs ++ ss) x₂ m p₁ p₂ (in-both Valid g f) p₄ s

  sound-pred-comp : ∀ {w v} {ω : EState w v} ->
    Sound ω -> Sound (pred-comp ω)
  sound-pred-comp {w} {v} {ω@(start rs)} s =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-items {w}) \\ ε)) in
    sound-pred-comp₂ ω ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂ (λ ())
      (sound-deduplicate (Sₙ ω) s)
      s
  sound-pred-comp {w} {v} {ω@(step _ rs)} s =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (Σ.proj₁ (all-items {w}) \\ ε)) in
    sound-pred-comp₂ ω ε (Σ.proj₁ x₁) m (≤ₛ (≤-self _)) x₂ (λ ())
      (sound-deduplicate (Sₙ ω) (snd s))
      s

  sound-step₀ : ∀ {w a v} {ω : EState w (a ∷ v)} ->
    Sound ω -> Sound (step₀ ω)
  sound-step₀ {ω = ω} s = sound-scanr (pred-comp ω) (sound-pred-comp s)

  sound-parse₀ : ∀ {w v} -> {ω : EState w v} ->
    Sound ω -> Sound (parse₀ ω)
  sound-parse₀ {v = ε} s = sound-pred-comp s
  sound-parse₀ {v = x ∷ v} s = sound-parse₀ (sound-step₀ s)

  sound-itemize : ∀ {w} rs ->
    (∀ {i} -> i ∈ itemize w rs -> Valid i)
  sound-itemize ε {i} ()
  sound-itemize (σ (X , β) (x , refl) ∷ rs) in-head = initial x
  sound-itemize (σ (X , β) p₀ ∷ rs)  (in-tail p) = sound-itemize rs p

  sound-parse : ∀ w -> Sound (parse w)
  sound-parse w =
    let x₁ = lookup (CFG.start G) (CFG.rules G) in
    let x₂ = sound-itemize {w} x₁ in
    let ω = start (itemize w x₁) in
    sound-parse₀ {ω = ω} x₂
