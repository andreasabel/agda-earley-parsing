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

  complete-scanr₀ : ∀ {t u v X α β} -> ∀ a rs ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g -> i ∈ rs ->
    j ≋ scanner g ->
      j ∈ scanr₀ a rs
  complete-scanr₀ a ε i j g refl () refl
  complete-scanr₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs)       i j g refl (in-tail p) refl = complete-scanr₀ a rs i j g refl p refl
  complete-scanr₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) i j g refl (in-tail p) refl = complete-scanr₀ a rs i j g refl p refl
  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl p           refl with decidₜ a b
  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl in-head     refl | yes refl = in-head
  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl (in-tail p) refl | yes refl = in-tail (complete-scanr₀ a rs i j g refl p refl)
  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl in-head     refl | no x = void (x refl)
  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl (in-tail p) refl | no x = complete-scanr₀ a rs i j g refl p refl

  complete-scanr : ∀ {t u v X α β} -> ∀ a ->
    (ω : WSet t (a ∷ v)) ->
    Complete ω ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g ->
    j ≋ scanner g ->
      j ∈ Sₙ (scanr a ω)
  complete-scanr a ω@(start rs) c  i j g refl refl with (fst c) i g refl
  complete-scanr a ω@(start rs) c  i j g refl refl | d = complete-scanr₀ a (Sₙ ω) i j g refl d refl
  complete-scanr a ω@(step _ rs) c i j g refl refl with (fst c) i g refl
  complete-scanr a ω@(step _ rs) c i j g refl refl | d = complete-scanr₀ a (Sₙ ω) i j g refl d refl

  Contains : ∀ {v w} -> ∀ X u α β .χ .ψ -> WSet w v -> Set
  Contains X u α β χ ψ (start rs) = (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs
  Contains X u α β χ ψ (step ω rs) = Contains X u α β χ ψ ω ∣ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs

--  complete-compl₀ : ∀ {u v w X t α β} (ω : WSet w v) -> ∀ .χ .ψ ->
--    Contains X t α β χ ψ ω ->
--    (X ∘ t ↦ α ∘ β [ χ ∘ ψ ]) ∈ compl₀ {u} ω
--  complete-compl₀ {u} {v} ω χ ψ g                with eq-T* u v
--  complete-compl₀ {u} {u} ω χ ψ g                | yes refl = {!!}
--  complete-compl₀ {u} {v} (start rs) χ ψ g       | no x = {!!}
--  complete-compl₀ {u} {v} (step ω rs) χ ψ (r x₁) | no x = {!!}
--  complete-compl₀ {u} {v} (step ω rs) χ ψ (l x₁) | no x = {!!}

  test₃ : ∀ {a t} ->
    (Σ λ s -> s ++ (a ∷ t) ≡ t) -> Void
  test₃ (σ p₁ p₀) = void (ε.ε₂ decidₜ p₀)

  test₂ : ∀ {v a} {a₀ : T} p q ->
    p ++ (a ∷ v) ≡ q ++ (a₀ ∷ v) ->
    a ≡ a₀
  test₂ ε ε refl = refl
  test₂ {v = v} ε (x ∷ q) s = void (ε.ε₆ decidₜ _ v (sym s))
  test₂ {v = v} (x ∷ p) ε s = void (ε.ε₆ decidₜ _ v s)
  test₂ (x ∷ p) (x₁ ∷ q) s = test₂ p q (uncons x x₁ s)
  
  test₁ : ∀ {a₀ v t} {a : T} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (Σ λ u -> u ++ (a₀ ∷ v) ≡ t) ->
    a ≡ a₀
  test₁ (r refl) (σ q₁ q₀) = void (ε.ε₂ decidₜ q₀)
  test₁ (l (σ ε refl)) (σ ε refl) = refl
  test₁ {v = v} (l (σ ε refl)) (σ (x ∷ q₁) q₀) = void (ε.ε₆ decidₜ _ v q₀)
  test₁ {v = v} (l (σ (x ∷ p₁) p₀)) (σ ε refl) = void (ε.ε₆ decidₜ _ v p₀)
  test₁ (l (σ (x ∷ p₁) p₀)) (σ (x₁ ∷ q₁) refl) = test₂ p₁ q₁ (uncons x x₁ p₀)

  test₀ : ∀ {t u v a a₀ X α β} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (h : G ∙ t ⊢ u / a₀ ∷ v ⟶* X / α ∙ r a₀ ∷ β) ->
    a ≡ a₀
  test₀ p g = test₁ p (suff-g₂ g)
    
  test : ∀ {a t v} ->
    {P : Item t v -> Set} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->

    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      P i
    ) ->

    (∀ {β} ->
      (z : t ≡ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> eq-prop P i z
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
  test s f ini h c (initial x) i refl = ini refl x i refl
  test {a} s f ini h c (scanner g) i p = case test₀ s g of λ {refl -> f g i p}
  test s f ini h c (predict x g) i@(X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) refl =
    h x (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i g refl (test s f ini h c g _ refl) refl
  test s f ini h c (complet g g₁) i p =
    c (_ ∘ _ ↦ _ ∘ _ [ in-g g₁ ∘ suff-g₂ g ]) i g g₁ refl (test s f ini h c g₁ _ refl) p

--  complete-compl₂ : ∀ {t u v w X Y β γ} -> ∀ α .χ .ψ .χ₁ .ψ₁ ->
--    (ω : WSet t w) ->
--    (i : Item t w) ->
--    (p : i ≡ (Y ∘ v ↦ γ ∘ ε)) ->
--    G ⊢ u / v ⟶* X / l Y ∷ β ->
--    G ⊢ v / w ⟶* Y / ε ->
--    (X ∘ u ↦ α ←∷ l Y ∘ β [ χ₁ ∘ ψ₁ ]) ∈ compl₂ χ ψ i p ω
--  complete-compl₂ α χ ψ χ₁ ψ₁ ω i p g h =
--    let c₁ = complete-compl₀ ω (in₁ (app (_ ,_) (sym (in₀ _ _ _))) χ₁) ψ₁ {!!} in
--    complete-compl₁ α χ ψ χ₁ ψ₁ (compl₀ ω) i p c₁ g h

  complete-predict₀ : ∀ {t u v X Y α β δ} ->
    (ψ₀ : Σ λ s -> s ++ v ≡ t) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / ε ∙ δ) ->
    (p : i ≋ g) ->
    (q : j ≋ h) ->
    (rs : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    (Σ λ e -> σ (Y , δ) e ∈ rs) ->
    j ∈ predict₀ ψ₀ i (≋-β i g p) rs
  complete-predict₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl ε (σ p₁ ())
  complete-predict₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , γ) (p , refl) ∷ rs) q with eq-α γ δ
  complete-predict₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , δ) (p , refl) ∷ rs) q | yes refl = in-head
  complete-predict₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , δ) (p , refl) ∷ rs) (σ (q , refl) in-head) | no x = void (x refl)
  complete-predict₀ ψ₀ (X ∘ u ↦ α ∘ l Y ∷ β) (Y ∘ u₁ ↦ ε ∘ δ) g h refl refl (σ (Y , γ) (p , refl) ∷ rs) (σ q₁ (in-tail q₀)) | no x =
    in-tail (complete-predict₀ ψ₀ _ _ g h refl refl rs (σ q₁ q₀))

  complete-predict₁ : ∀ {t u v X Y α β δ} ->
    (ω : WSet t v) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (x : CFG.rules G ∋ (Y , δ)) ->
    (p : i ≋ g) ->
    j ≋ predict x g ->
    j ∈ predict₁ i (≋-β i g p) ω
  complete-predict₁ ω i@(X ∘ u ↦ α ∘ l Y ∷ β) j g x refl q =
    complete-predict₀ _ i j g (predict x g) refl q (lookup Y (CFG.rules G)) (lookup-sound x)

  complete-deduplicate : ∀ {w v i} -> (as : Item w v *) -> i ∈ as -> i ∈ Σ.proj₁ (deduplicate as)
  complete-deduplicate ε ()
  complete-deduplicate (x ∷ as) p with elem eq-item x (Σ.proj₁ (deduplicate as))
  complete-deduplicate (x ∷ as) in-head     | yes x₁ = x₁
  complete-deduplicate (x ∷ as) (in-tail p) | yes x₁ = complete-deduplicate as p
  complete-deduplicate (x ∷ as) in-head     | no x₁ = in-head
  complete-deduplicate (x ∷ as) (in-tail p) | no x₁ = in-tail (complete-deduplicate as p)

  complete₁-pred-comp₀ : ∀ {t u v X Y α β δ} ->
    (ω : WSet t v) ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    j ≋ predict x g ->
      j ∈ Σ.proj₁ (pred-comp₀ i ω)
  complete₁-pred-comp₀ ω x i@(Y ∘ u ↦ α ∘ l Z ∷ β) j@(Z ∘ u₁ ↦ ε ∘ β₁ [ χ₁ ∘ ψ₁ ]) g refl refl =
    let x₁ = complete-predict₁ ω i j g x refl refl in
    complete-deduplicate (predict₁ i refl ω) x₁

  complete₂-pred-comp₀ : ∀ {t u v w X Y α β γ} ->
    (ω : WSet t w) ->
    (i j : Item t w) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    i ≋ h -> 
    j ≋ complet g h ->
      j ∈ Σ.proj₁ (pred-comp₀ i ω)
  complete₂-pred-comp₀ ω i j g h refl refl =
    complete-deduplicate (compl₂ i refl ω) {!!}

  complete₁-pred-comp₁ : ∀ {t u v X Y α β δ ss} -> ∀ rs ->
    (ω : WSet t v)
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    i ∈ rs ->
    j ≋ predict x g ->
      j ∈ pred-comp₁ ω ss rs
  complete₁-pred-comp₁ {ss = ss} (i  ∷ rs) ω x i j g o in-head q =
    in-l (complete₁-pred-comp₀ (Wₙ ω ss) x i j g o q)
  complete₁-pred-comp₁ (r₁ ∷ rs) ω x i j g o (in-tail p) q =
    in-r (complete₁-pred-comp₁ rs ω x i j g o p q)

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
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ x₁ (rs ++ ss) q in
    i ∈ Sₙ (pred-comp₂ ω (rs ++ ss) x₂ m p₁ q₁)
  
  complete₁₋₁-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    in-after i ω rs ss m p q ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₋₁-pred-comp₂ ss rs zero () q ω i a
  complete₁₋₁-pred-comp₂ ss ε (suc m) p q ω i ()
  complete₁₋₁-pred-comp₂ ss (x ∷ rs) (suc m) p q ω i a = a

  complete₁₀-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    i ∈ ss ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₀-pred-comp₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₀-pred-comp₂ {ss = ss} {ε} {suc m} {p} (start rs) i s = s
  complete₁₀-pred-comp₂ {ss = ss} {ε} {suc m} {p} (step ω rs) i s = s
  complete₁₀-pred-comp₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} {q} ω i s =
    complete₁₀-pred-comp₂ {m = m} ω i (in-r s)

  complete₁₁-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    (i : Item t v) ->
    i ∈ rs ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₁-pred-comp₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₁-pred-comp₂ {ss = ss} {ε} {suc m} {p} ω i ()
  complete₁₁-pred-comp₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} ω i s =
    complete₁₀-pred-comp₂ {m = m} ω i (in-l s)

  complete₁₂-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : WSet t v) ->
    ∀ {u X Y α β δ} ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> i ∈ rs ->
    j ≋ predict x g -> j ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₂-pred-comp₂ {ss = ss} {rs} {zero} {p = ()} ω x i j g p p' q
  complete₁₂-pred-comp₂ {ss = ss} {ε} {suc m} ω x i j g p () q
  complete₁₂-pred-comp₂ {ss = ss} {rs@(_ ∷ _)} {suc m} ω x i j g p p' q =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let y₁ = complete₁-pred-comp₁ rs ω x i j g p p' q in
    let y₂ = include-\\ {as = x₁} {bs = rs ++ ss} y₁ in
    case in-lr x₂ (rs ++ ss) y₂ of
      λ { (r z) → complete₁₀-pred-comp₂ {m = m} ω j z
        ; (l z) → complete₁₁-pred-comp₂ {m = m} ω j z
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
    Nx (rs ++ ss) (pred-comp₁ ω ss rs \\ (rs ++ ss))
  nx' {rs = ε} {ss} ω nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  nx' {rs = rs@(r₁ ∷ rs₀)} {ss} ω nx x i j g z₁ z₂ z₃ =
    case in-lr rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx x i j g z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) →
        let y₁ = complete₁-pred-comp₁ rs ω x i j g z₁ x₁ z₃ in
        include-\\ y₁
      }

  complete₁-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    Nx ss rs ->
    ∀ {u X Y α β δ}
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> 
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q) ->
    j ≋ predict x g ->
      j ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁-pred-comp₂ ss rs            zero    () q ω           nx x i j g z₁ z₂ z₃
  complete₁-pred-comp₂ ss ε             (suc m) p  q (start rs)  nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃ 
  complete₁-pred-comp₂ ss ε             (suc m) p  q (step ω rs) nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃
  complete₁-pred-comp₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           nx x i j g z₁ z₂ z₃ =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ (pred-comp₁ ω ss rs) (rs ++ ss) q in
    complete₁-pred-comp₂ (rs ++ ss) _ m p₁ q₁ ω (nx' ω nx) x i j g z₁ z₂ z₃

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
    Nx₂ (rs ++ ss) (pred-comp₁ ω ss rs \\ (rs ++ ss))
  nx₂' {rs = ε} {ss} ω c nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  nx₂' {rs = rs@(r₁ ∷ rs₀)} {ss} ω c nx x i j g z₁ z₂ z₃ =
    case in-lr rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx x i j g z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) → {!!}
      }

  complete₂-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx₂ ss rs ->
    ∀ {u w X Y α β γ}
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ Sₙ (pred-comp₂ ω ss rs m p q) ->
    k ≋ complet g h ->
      k ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₂-pred-comp₂ ss rs            zero    () q ω           c nx x i j g z₁ z₂ z₃
  complete₂-pred-comp₂ ss ε             (suc m) p  q (start rs)  c nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃ 
  complete₂-pred-comp₂ ss ε             (suc m) p  q (step ω rs) c nx x i j g z₁ z₂ z₃ =
    nx x i j g z₁ z₂ z₃
  complete₂-pred-comp₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           c nx x i j g z₁ z₂ z₃ =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ (pred-comp₁ ω ss rs) (rs ++ ss) q in
    complete₂-pred-comp₂ (rs ++ ss) _ m p₁ q₁ ω c (nx₂' ω c nx) x i j g z₁ z₂ z₃

  complete-pred-comp₂ : ∀ {a t v ss rs m p q} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx ss rs ->
    Nx₂ ss rs ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
    ) ->
    (∀ {β} ->
      (z : t ≡ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> eq-prop (λ i -> i ∈ Sₙ (pred-comp₂ ω ss rs m p q)) i z
    ) ->
    ∀ {u X α β} ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
    (i : Item t v) ->
    i ≋ g -> i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete-pred-comp₂ {a} {t} {v} {ss} {rs} {m} {p} {q} h ω c nx nx₂ s u g i e =
    test {P = λ i -> i ∈ Sₙ (pred-comp₂ ω ss rs m p q)}
      h
      s
      u 
      (complete₁-pred-comp₂ ss rs m p q ω nx)
      (complete₂-pred-comp₂ ss rs m p q ω c nx₂)
      g i e

  complete₀-pred-comp : ∀ {a t v} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : WSet t v) ->
    Complete* ω ->
    Nx ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    Nx₂ ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ (Σ.proj₁ (deduplicate (Sₙ ω)))
    ) ->
    (∀ {β} ->
      (z : t ≡ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> eq-prop (_∈ Σ.proj₁ (deduplicate (Sₙ ω))) i z
    ) ->
    ∀ {u X α β} ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
    (i : Item t v) ->
    i ≋ g -> i ∈ Sₙ (pred-comp ω)
  complete₀-pred-comp {a} {t} s ω c nx nx₂ fx fx₂ g i p =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    complete-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} s ω c nx nx₂
      (λ g₁ i₁ x → complete₁₁-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} ω i₁ (fx g₁ i₁ x))
      (λ {refl x i₁ x₃ → complete₁₁-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} ω i₁ (fx₂ refl x i₁ x₃)})
      g i p

  complete₃-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : WSet t v) ->
    Complete* ω ->
    Complete* (pred-comp₂ ω ss rs m p q)
  complete₃-pred-comp₂ ss rs zero () q ω c
  complete₃-pred-comp₂ ss ε (suc m) p q (start rs) c = top
  complete₃-pred-comp₂ ss ε (suc m) p q (step ω rs) c = c
  complete₃-pred-comp₂ ss rs@(_ ∷ _) (suc m) p q ω c =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-rules) p q in
    let q₁ = wf-pcw₂ x₁ (rs ++ ss) q in
    complete₃-pred-comp₂ (rs ++ ss) x₂ m p₁ q₁ ω c 

  complete₁-pred-comp : ∀ {t v} ->
    (ω : WSet t v) ->
    Complete* ω ->
    Complete* (pred-comp ω)
  complete₁-pred-comp ω =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    complete₃-pred-comp₂ ε _ _ (≤ₛ (≤-self _)) x₂ ω
    
  complete₂-pred-comp : ∀ {t v} ->
    (ω : WSet t v) ->
    Complete* ω ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
      (i : Item t v) ->
      i ≋ g -> i ∈ Sₙ (pred-comp ω)
    ) ->
    Complete (pred-comp ω)
  complete₂-pred-comp ω c f = (λ i g x → f g i x) , complete₁-pred-comp ω c

  complete-pred-comp : ∀ {a t v} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : WSet t v) ->
    Complete* ω ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ ω
    ) ->
    (∀ {β} ->
      (z : t ≡ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> eq-prop (_∈ Sₙ ω) i z
    ) ->
    Complete (pred-comp ω)
  complete-pred-comp {a} {t} s ω c fx fx₂ =
    let
      x₅ = complete₀-pred-comp s ω c (λ x i j g x₁ ()) (λ j k g h x ())
        (λ {g i x → complete-deduplicate (Sₙ ω) (fx g i x)})
        λ {refl x i x₁ → complete-deduplicate (Sₙ ω) (fx₂ refl x i x₁)}
    in
    complete₂-pred-comp ω c x₅

  complete-step : ∀ {a₀ a t v} ->
    (Σ λ u -> u ++ (a₀ ∷ a ∷ v) ≡ t) ∣ (a ∷ v) ≡ t ->
    (ω : WSet t (a ∷ v)) ->
    Complete* ω ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a₀ ∷ a ∷ v ⟶* X / α ∙ r a₀ ∷ β) ->
      (i : Item t (a ∷ v)) -> (i ≋ scanner g) ->
      i ∈ Sₙ ω
    ) ->
    (∀ {β} ->
      (z : t ≡ a ∷ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item (a ∷ v) (a ∷ v)) ->
      i ≋ initial x -> eq-prop (_∈ Sₙ ω) i z
    ) ->
    ∀ {u X α β} ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g ->
    j ≋ scanner g ->
      j ∈ Sₙ (step₀ ω)
  complete-step {a₀} {a} s ω c fx fx₂ i j g refl refl =
    let
      x₁ = complete-pred-comp s ω c fx fx₂
    in complete-scanr a (pred-comp ω) x₁ i j g refl refl

  complete*-step : ∀ {a₀ a t v} ->
    (Σ λ u -> u ++ (a₀ ∷ a ∷ v) ≡ t) ∣ (a ∷ v) ≡ t ->
    (ω : WSet t (a ∷ v)) ->
    Complete* ω ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a₀ ∷ a ∷ v ⟶* X / α ∙ r a₀ ∷ β) ->
      (i : Item t (a ∷ v)) -> (i ≋ scanner g) ->
      i ∈ Sₙ ω
    ) ->
    (∀ {β} ->
      (z : t ≡ a ∷ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item (a ∷ v) (a ∷ v)) ->
      i ≋ initial x -> eq-prop (_∈ Sₙ ω) i z
    ) ->
    Complete* (step₀ ω)
  complete*-step s ω c fx fx₂ =
    complete-pred-comp s ω c fx fx₂

  complete-parse₀ : ∀ {a t v} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : WSet t v) ->
    Complete* ω ->
    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
      (i : Item t v) -> (i ≋ scanner g) ->
      i ∈ Sₙ ω
    ) ->
    (∀ {β} ->
      (z : t ≡ v) ->
      (x : (CFG.start G , β) ∈ CFG.rules G) ->
      (i : Item v v) ->
      i ≋ initial x -> eq-prop (_∈ Sₙ ω) i z
    ) ->
    Complete (parse₀ ω)
  complete-parse₀ {a₀} {t} {v = ε} k ω c fx fx₂ = complete-pred-comp k ω c fx fx₂
  complete-parse₀ {a₀} {t} {v = a ∷ v} k ω c fx fx₂ =
    let
      x₁ = complete-pred-comp k ω c fx fx₂
      x₂ = case k of
        λ { (r refl) → l (σ ε refl)
          ; (l (σ p₁ p₀)) → l (σ (p₁ ←∷ a₀) (trans (sym (in₀ _ _ _)) (sym p₀)))
          }
    in
    complete-parse₀ {v = v} x₂ (step₀ ω) x₁
      (λ {g i refl → complete-scanr a (pred-comp ω) x₁
        (_ ∘ _ ↦ _ ∘ _ [ v-unstep (Item.χ i) ∘ Item.ψ i ]) i g refl refl})
      (λ {refl x₂ i x₃ → case k of
        λ { (r ())
          ; (l (σ p₁ p₀)) → void (ε.ε₂ decidₜ (trans (sym (in₀ _ _ _)) (sym p₀)))
          }
        })

  complete₀-itemize : ∀ w {β} ->
    (rs : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ CFG.start G)) *) ->
    (x : (CFG.start G , β) ∈ CFG.rules G) ->
    (CFG.start G , β) ∈ map Σ.proj₁ rs ->
    (i : Item w w) ->
    i ≋ initial x ->
      i ∈ itemize w rs
  complete₀-itemize w ε x () i refl
  complete₀-itemize w (σ (X , β) p₀ ∷ rs) x in-head i refl = in-head
  complete₀-itemize w (σ (X , β) p₀ ∷ rs) x (in-tail p) i refl =
    in-tail (complete₀-itemize w rs x p i refl)

  complete-itemize : ∀ w {β} ->
    (x : (CFG.start G , β) ∈ CFG.rules G) ->
    (i : Item w w) ->
    i ≋ initial x ->
      i ∈ itemize w (lookup (CFG.start G) (CFG.rules G))
  complete-itemize w x i refl =
    let x₁ = Σ.proj₀ (lookup-sound x) in
    complete₀-itemize w (lookup _ _) x (in-map Σ.proj₁ x₁) i refl

  complete-parse : ∀ a₀ w ->
    Complete (parse w)
  complete-parse a₀ ε =
    complete-parse₀ {a = a₀} (r refl) (start (itemize ε (lookup _ _))) top
      (λ {g i x → void (test₃ (suff-g₂ g))})
      (λ {refl x i x₁ → complete-itemize ε x i x₁})
  complete-parse a₀ (x ∷ w) =
    let
      x₁ = start (itemize (x ∷ w) (lookup _ _)) 
      x₂ = complete-pred-comp {a = a₀} (r refl) x₁ top
        (λ {g i x₂ → void (test₃ (suff-g₂ g))})
        (λ {refl x₂ i refl → complete-itemize (x ∷ w) x₂ i refl})
    in
    complete-parse₀ (l (σ ε refl)) (step₀ x₁) x₂
      (λ g i x₃ → complete-step {a₀ = x} (r refl) x₁ top
        (λ {g₁ i₁ x₄ → void (test₃ (suff-g₂ g₁))})
        (λ {refl x₄ i₁ x₅ → complete-itemize (x ∷ w) x₄ i₁ x₅})
        (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i g refl x₃)
      (λ ())
