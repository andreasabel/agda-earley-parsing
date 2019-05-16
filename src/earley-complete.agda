open import base

module earley-complete (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T
open import earley N T decidₙ decidₜ

module parser-sound (G : CFG) where

  open parser G
  open import count N T decidₙ decidₜ
  open Unique Item eq-item
  
  -- Complete state sets (contain all derivable items).

  _≋_ : ∀ {t u v X α β} -> (i : Item t v) -> G ∙ t ⊢ u / v ⟶* X / α ∙ β -> Set
  _≋_ {t} {u} {v} {X} {α} {β} i g = (Item.Y i , Item.u i , Item.α i , Item.β i) ≡ (X , u , α , β)

  ≋-β : ∀ {t u v X α β} -> ∀ i -> (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) -> i ≋ g -> Item.β i ≡ β
  ≋-β i g refl = refl

  eq-prop : {a b : T *} (P : Item a b -> Set) (i : Item b b) -> a ≡ b -> Set
  eq-prop P i refl = P i

  Complete₀ : ∀ {t v} -> WSet t v -> Set
  Complete₀ {t} {v} ω = ∀ {u Y α β} ->
    (i : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* Y / α ∙ β) ->
    i ≋ g ->
    i ∈ Sₙ ω

  mutual
    Complete : ∀ {v w} -> WSet w v -> Set
    Complete ω = Complete₀ ω × Complete* ω
  
    Complete* : ∀ {v w} -> WSet w v -> Set
    Complete* (start rs) = ⊤
    Complete* (step ω rs) = Complete ω

  complete-scanner-w₀ : ∀ {t u v X α β} -> ∀ a rs ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g -> i ∈ rs ->
    j ≋ scanner g ->
      j ∈ scanner-w₀ a rs
  complete-scanner-w₀ a ε i j g refl () refl
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs)       i j g refl (in-tail p) refl = complete-scanner-w₀ a rs i j g refl p refl
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) i j g refl (in-tail p) refl = complete-scanner-w₀ a rs i j g refl p refl
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl p           refl with decidₜ a b
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl in-head     refl | yes refl = in-head
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl (in-tail p) refl | yes refl = in-tail (complete-scanner-w₀ a rs i j g refl p refl)
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl in-head     refl | no x = void (x refl)
  complete-scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl (in-tail p) refl | no x = complete-scanner-w₀ a rs i j g refl p refl

  complete-scanner-w : ∀ {t u v X α β} -> ∀ a ->
    (ω : WSet t (a ∷ v)) ->
    Complete ω ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g ->
    j ≋ scanner g ->
      j ∈ Sₙ (scanner-w a ω)
  complete-scanner-w a ω@(start rs) c  i j g refl refl with (fst c) i g refl
  complete-scanner-w a ω@(start rs) c  i j g refl refl | d = complete-scanner-w₀ a (Sₙ ω) i j g refl d refl
  complete-scanner-w a ω@(step _ rs) c i j g refl refl with (fst c) i g refl
  complete-scanner-w a ω@(step _ rs) c i j g refl refl | d = complete-scanner-w₀ a (Sₙ ω) i j g refl d refl

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

  complete₁-pred-comp-w₁ : ∀ {t u v X Y α β δ ss} -> ∀ rs ->
    (ω : WSet t v)
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    i ∈ rs ->
    j ≋ predict x g ->
      j ∈ pred-comp-w₁ ω ss rs
  complete₁-pred-comp-w₁ {ss = ss} (i  ∷ rs) ω x i j g o in-head q =
    in-l (complete₁-pred-comp-w₀ (Wₙ ω ss) x i j g o q)
  complete₁-pred-comp-w₁ (r₁ ∷ rs) ω x i j g o (in-tail p) q =
    in-r (complete₁-pred-comp-w₁ rs ω x i j g o p q)

  in-after : ∀ {v w} ->
    (i : Item w v) ->
    (ω : WSet w v) ->
    (rs ss : Item w v *)
    (m : ℕ)
    (p : suc (length (Σ.proj₁ (all-rules {w} {v}) \\ ss)) ≤ m)
    (q : Unique (rs ++ ss)) ->
      Set
  in-after i ω rs ss zero () q
  in-after i ω ε ss (suc m) p q = ⊥
  in-after i ω rs@(_ ∷ _) ss (suc m) p q =
    let x₁ = pred-comp-w₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ x₁ (rs ++ ss) q in
    i ∈ Sₙ (pred-comp-w₂ ω (rs ++ ss) x₂ m p₁ q₁)
  
  complete₁₋₁-pred-comp-w₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    in-after i ω rs ss m p q ->
    i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₁₋₁-pred-comp-w₂ ss rs zero () q ω i a
  complete₁₋₁-pred-comp-w₂ ss ε (suc m) p q ω i ()
  complete₁₋₁-pred-comp-w₂ ss (x ∷ rs) (suc m) p q ω i a = a

  complete₁₀-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    i ∈ ss ->
    i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₁₀-pred-comp-w₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₀-pred-comp-w₂ {ss = ss} {ε} {suc m} {p} (start rs) i s = s
  complete₁₀-pred-comp-w₂ {ss = ss} {ε} {suc m} {p} (step ω rs) i s = s
  complete₁₀-pred-comp-w₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} {q} ω i s =
    complete₁₀-pred-comp-w₂ {m = m} ω i (in-r s)

  complete₁₁-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    i ∈ rs ->
    i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₁₁-pred-comp-w₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₁-pred-comp-w₂ {ss = ss} {ε} {suc m} {p} ω i ()
  complete₁₁-pred-comp-w₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} ω i s =
    complete₁₀-pred-comp-w₂ {m = m} ω i (in-l s)

  complete₁₂-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    ∀ {u X Y α β δ} ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> i ∈ rs ->
    j ≋ predict x g -> j ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₁₂-pred-comp-w₂ {ss = ss} {rs} {zero} {p = ()} ω x i j g p p' q
  complete₁₂-pred-comp-w₂ {ss = ss} {ε} {suc m} ω x i j g p () q
  complete₁₂-pred-comp-w₂ {ss = ss} {rs@(_ ∷ _)} {suc m} ω x i j g p p' q =
    let x₁ = pred-comp-w₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let y₁ = complete₁-pred-comp-w₁ rs ω x i j g p p' q in
    let y₂ = include-\\ {as = x₁} {bs = rs ++ ss} y₁ in
    case in-lr x₂ (rs ++ ss) y₂ of
      λ { (r z) → complete₁₀-pred-comp-w₂ {m = m} ω j z
        ; (l z) → complete₁₁-pred-comp-w₂ {m = m} ω j z
        }

  Nx : ∀ {t v} -> Item t v * -> Item t v * -> Set
  Nx {t} {v} ss rs =
    ∀ {u X Y α β δ} ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> i ∈ ss ->
    j ≋ predict x g ->
      j ∈ (rs ++ ss)
  
  nx' : ∀ {t v rs ss} (ω : WSet t v) ->
    Nx ss rs ->
    Nx (rs ++ ss) (pred-comp-w₁ ω ss rs \\ (rs ++ ss))
  nx' {rs = ε} {ss} ω nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  nx' {rs = rs@(r₁ ∷ rs₀)} {ss} ω nx x i j g z₁ z₂ z₃ =
    case in-lr rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx x i j g z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) →
        let y₁ = complete₁-pred-comp-w₁ rs ω x i j g z₁ x₁ z₃ in
        include-\\ y₁
      }

  complete₁-pred-comp-w₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    Nx ss rs ->
    ∀ {u X Y α β δ}
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q) ->
    j ≋ predict x g ->
      j ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₁-pred-comp-w₂ ss rs            zero    () q ω           nx x i j g z₁ z₂ z₃
  complete₁-pred-comp-w₂ ss ε             (suc m) p  q (start rs)  nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃ 
  complete₁-pred-comp-w₂ ss ε             (suc m) p  q (step ω rs) nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃
  complete₁-pred-comp-w₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           nx x i j g z₁ z₂ z₃ =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ (pred-comp-w₁ ω ss rs) (rs ++ ss) q in
    complete₁-pred-comp-w₂ (rs ++ ss) _ m p₁ q₁ ω (nx' ω nx) x i j g z₁ z₂ z₃

  Nx₂ : ∀ {t v} -> Item t v * -> Item t v * -> Set
  Nx₂ {t} {v} ss rs =
    ∀ {u w X Y α β γ} ->
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ ss ->
    k ≋ complet g h ->
      k ∈ (rs ++ ss)
  
  nx₂' : ∀ {t v rs ss} (ω : WSet t v) ->
    Complete* ω ->
    Nx₂ ss rs ->
    Nx₂ (rs ++ ss) (pred-comp-w₁ ω ss rs \\ (rs ++ ss))
  nx₂' {rs = ε} {ss} ω c nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  nx₂' {rs = rs@(r₁ ∷ rs₀)} {ss} ω c nx x i j g z₁ z₂ z₃ =
    case in-lr rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx x i j g z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) → {!!}
      }

  complete₂-pred-comp-w₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx₂ ss rs ->
    ∀ {u w X Y α β γ}
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ Sₙ (pred-comp-w₂ ω ss rs m p q) ->
    k ≋ complet g h ->
      k ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)
  complete₂-pred-comp-w₂ ss rs            zero    () q ω           c nx x i j g z₁ z₂ z₃
  complete₂-pred-comp-w₂ ss ε             (suc m) p  q (start rs)  c nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃ 
  complete₂-pred-comp-w₂ ss ε             (suc m) p  q (step ω rs) c nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃
  complete₂-pred-comp-w₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           c nx x i j g z₁ z₂ z₃ =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ (pred-comp-w₁ ω ss rs) (rs ++ ss) q in
    complete₂-pred-comp-w₂ (rs ++ ss) _ m p₁ q₁ ω c (nx₂' ω c nx) x i j g z₁ z₂ z₃

  complete-pred-comp-w₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx ss rs ->
    Nx₂ ss rs ->
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
  complete-pred-comp-w₂ {t} {v} {ss} {rs} {m} {p} {q} ω c nx nx₂ s u g i e =
    test {P = λ i -> i ∈ Sₙ (pred-comp-w₂ ω ss rs m p q)}
      s
      u
      (complete₁-pred-comp-w₂ ss rs m p q ω nx)
      (complete₂-pred-comp-w₂ ss rs m p q ω c nx₂)
      g i e

  complete₀-pred-comp-w : ∀ {t v} ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    Nx₂ ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    (∀ {u a X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ (pred-comp-w ω)
    ) ->
    (∀ {β} ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> Σ λ z -> eq-prop (_∈ Sₙ (pred-comp-w ω)) i z
    ) ->
    ∀ {u X α β} ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
    (i : Item t v) ->
    i ≋ g -> i ∈ Sₙ (pred-comp-w ω)
  complete₀-pred-comp-w {t} ω c nx nx₂ fx fx₂ g i p =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    complete-pred-comp-w₂ {p = ≤ₛ (≤-self _)} {q = x₂} ω c nx nx₂ fx fx₂ g i p

  complete₁-pred-comp-w : ∀ {t v} ->
    (ω : WSet t v) ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
      (i : Item t v) ->
      i ≋ g -> i ∈ Sₙ (pred-comp-w ω)
    ) ->
    Complete (pred-comp-w ω)
  complete₁-pred-comp-w ω f = (λ i g x → f g i x) , {!ω!}

  complete-pred-comp-w : ∀ {t v} ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    Nx₂ ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    (∀ {u a X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ (pred-comp-w ω)
    ) ->
    (∀ {β} ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> Σ λ z -> eq-prop (_∈ Sₙ (pred-comp-w ω)) i z
    ) ->
    Complete (pred-comp-w ω)
  complete-pred-comp-w {t} ω c nx nx₂ fx fx₂ =
    let x₅ = complete₀-pred-comp-w ω c nx nx₂ fx fx₂ in
    complete₁-pred-comp-w ω x₅

  complete-step-w : ∀ {a t v} ->
    (ω : WSet t (a ∷ v)) ->
    Complete ω ->
    (∀ {β} ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item (a ∷ v) (a ∷ v)) ->
      i ≋ initial x -> Σ λ z -> eq-prop (_∈ Sₙ (pred-comp-w ω)) i z
    ) ->
    ∀ {u X α β} ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g ->
    j ≋ scanner g ->
      j ∈ Sₙ (step-w ω)
  complete-step-w {a} ω c fx i j g refl refl =
    complete-scanner-w a (pred-comp-w ω) {!!} i j g refl refl
    

-- om alla scannade items finns i ω, sȧ Complete (pred-comp-w ω)
--  complete-pred-comp-w : ∀ {t u v a X α β} -> ∀ .χ .ψ ->
--    (ω : WSet t v) ->
--    G ⊢ u / a ∷ v ⟶* X / r a ∷ β ->
--    (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ Sₙ ω ->
--    Complete (pred-comp-w ω)
--  complete-pred-comp-w χ ψ ω g p = {!!}
