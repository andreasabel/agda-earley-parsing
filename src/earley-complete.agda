open import base

module earley-complete (N T : Set) (eqₙ : Dec N) (eqₜ : Dec T) where

open import grammar N T
open import earley N T eqₙ eqₜ

module parser-complete (G : CFG) where

  open parser G
  open import count N T eqₙ eqₜ
  open Unique Item eq-item

  -- Complete state sets (contain all derivable items).

  _≋_ : ∀ {t u v X α β} -> (i : Item t v) -> G ∙ t ⊢ u / v ⟶* X / α ∙ β -> Set
  _≋_ {t} {u} {v} {X} {α} {β} i g =
    (Item.Y i , Item.u i , Item.α i , Item.β i) ≡ (X , u , α , β)

  ≋-β : ∀ {t u v X α β} -> ∀ i -> (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) -> i ≋ g -> Item.β i ≡ β
  ≋-β i g refl = refl

  eq-prop : {a b : T *} (P : Item a b -> Set) (i : Item b b) -> a ≡ b -> Set
  eq-prop P i refl = P i

  test₃ : ∀ {a t} ->
    (Σ λ s -> s ++ (a ∷ t) ≡ t) -> Void
  test₃ (σ p₁ p₀) = void (ε.ε₂ eqₜ p₀)

  test₂ : ∀ {v a} {a₀ : T} p q ->
    p ++ (a ∷ v) ≡ q ++ (a₀ ∷ v) ->
    a ≡ a₀
  test₂ ε ε refl = refl
  test₂ {v = v} ε (x ∷ q) s = void (ε.ε₆ eqₜ _ v (sym s))
  test₂ {v = v} (x ∷ p) ε s = void (ε.ε₆ eqₜ _ v s)
  test₂ (x ∷ p) (x₁ ∷ q) s = test₂ p q (uncons x x₁ s)

  test₁ : ∀ {a₀ v t} {a : T} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (Σ λ u -> u ++ (a₀ ∷ v) ≡ t) ->
    a ≡ a₀
  test₁ (r refl) (σ q₁ q₀) = void (ε.ε₂ eqₜ q₀)
  test₁ (l (σ ε refl)) (σ ε refl) = refl
  test₁ {v = v} (l (σ ε refl)) (σ (x ∷ q₁) q₀) = void (ε.ε₆ eqₜ _ v q₀)
  test₁ {v = v} (l (σ (x ∷ p₁) p₀)) (σ ε refl) = void (ε.ε₆ eqₜ _ v p₀)
  test₁ (l (σ (x ∷ p₁) p₀)) (σ (x₁ ∷ q₁) refl) = test₂ p₁ q₁ (uncons x x₁ p₀)

  test₀ : ∀ {t u v a a₀ X α β} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (h : G ∙ t ⊢ u / a₀ ∷ v ⟶* X / α ∙ r a₀ ∷ β) ->
    a ≡ a₀
  test₀ p g = test₁ p (suff-g₂ g)

  Complete₀ : ∀ {t v} -> Item t v * -> Set
  Complete₀ {t} {v} rs = ∀ {u Y α β} ->
    (i : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* Y / α ∙ β) ->
    i ≋ g ->
    i ∈ rs

  mutual
    Complete : ∀ {v w} -> EState w v -> Set
    Complete ω = Complete₀ (Sₙ ω) × Complete* ω

    Complete* : ∀ {v w} -> EState w v -> Set
    Complete* (start rs) = ⊤
    Complete* (step ω rs) = Complete ω

  complete-ind : ∀ {a t v} ->
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
      (w ≡ v -> Void) ->
      (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
      (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
      (j ≋ h) -> P j ->
      (k ≋ complet g h) -> P k
    ) ->

    (∀ {u X Y α β γ} ->
      (j k : Item t v) ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
      (h : G ∙ t ⊢ v / v ⟶* Y / γ ∙ ε) ->
      (j ≋ g) -> P j ->
      (k ≋ complet g h) -> P k
    ) ->

    (∀ {u X α β} ->
      (g : G ∙ t ⊢ u / v ⟶* X / α ∙ β) ->
      (i : Item t v) ->
      i ≋ g ->
      P i
    )
  complete-ind s f ini h c d (initial x) i refl =
    ini refl x i refl

  complete-ind {a} s f ini h c d (scanner g) i p =
    case test₀ s g of λ {refl -> f g i p}

  complete-ind s f ini h c d (predict x g) i p =
    let x₁ = complete-ind s f ini h c d g _ refl in
    h x (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i g refl x₁ p

  complete-ind s f ini h c d (complet {v = v} {w} g g₁) i p with eq-T* v w
  complete-ind s f ini h c d (complet {v = v} {w} g g₁) i p | yes refl =
    let x₁ = complete-ind s f ini h c d g _ refl in
    d (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i g g₁ refl x₁ p
  complete-ind s f ini h c d (complet {v = v} {w} g g₁) i p | no x =
    let x₁ = complete-ind s f ini h c d g₁ _ refl in
    c (_ ∘ _ ↦ _ ∘ _ [ in-g g₁ ∘ suff-g₂ g ]) i x g g₁ refl x₁ p

  complete-scanr₀ : ∀ {t u v X α β} -> ∀ a rs ->
    (i : Item t (a ∷ v)) ->
    (j : Item t v) ->
    (g : G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β) ->
    i ≋ g -> i ∈ rs ->
    j ≋ scanner g ->
      j ∈ scanr₀ a rs
  complete-scanr₀ a ε i j g refl () refl

  complete-scanr₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs)       i j g refl (in-tail p) refl =
    complete-scanr₀ a rs i j g refl p refl

  complete-scanr₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) i j g refl (in-tail p) refl =
    complete-scanr₀ a rs i j g refl p refl

  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl in-head     refl with eqₜ a b
  ... | yes refl = in-head
  ... | no x     = void (x refl)

  complete-scanr₀ a ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) i j g refl (in-tail p) refl with eqₜ a b
  ... | yes refl = in-tail (complete-scanr₀ a rs i j g refl p refl)
  ... | no x     = complete-scanr₀ a rs i j g refl p refl

  complete-scanr : ∀ {t u v X α β} -> ∀ a ->
    (ω : EState t (a ∷ v)) ->
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

  Contains : ∀ {v w} -> ∀ X u α β .χ .ψ -> EState w v -> Set
  Contains X u α β χ ψ (start rs) = (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs
  Contains X u α β χ ψ (step ω rs) = Contains X u α β χ ψ ω ∣ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ∈ rs

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

  complete-predic : ∀ {t u v X Y α β δ} ->
    (ω : EState t v) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (x : CFG.rules G ∋ (Y , δ)) ->
    (p : i ≋ g) ->
    j ≋ predict x g ->
    j ∈ predic i (≋-β i g p) ω
  complete-predic ω i@(X ∘ u ↦ α ∘ l Y ∷ β) j g x refl q =
    complete-predict₀ _ i j g (predict x g) refl q (lookup Y (CFG.rules G)) (lookup-sound x)

  complete-deduplicate : ∀ {w v i} -> (as : Item w v *) -> i ∈ as -> i ∈ Σ.proj₁ (deduplicate as)
  complete-deduplicate ε ()
  complete-deduplicate (x ∷ as) p with elem eq-item x (Σ.proj₁ (deduplicate as))
  complete-deduplicate (x ∷ as) in-head     | yes x₁ = x₁
  complete-deduplicate (x ∷ as) (in-tail p) | yes x₁ = complete-deduplicate as p
  complete-deduplicate (x ∷ as) in-head     | no x₁ = in-head
  complete-deduplicate (x ∷ as) (in-tail p) | no x₁ = in-tail (complete-deduplicate as p)

  complete₁-pred-comp₀ : ∀ {t u v X Y α β δ} ->
    (ω : EState t v) ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g ->
    j ≋ predict x g ->
      j ∈ pred-comp₀ i refl ω
  complete₁-pred-comp₀ ω x i@(X ∘ u ↦ α ∘ l Z ∷ β) j g refl refl with elem eqₙ Z (nullable G)
  complete₁-pred-comp₀ ω x i@(X ∘ u ↦ α ∘ l Z ∷ β) j g refl refl | yes d =
    let x₁ = complete-predic ω i j g x refl refl in
    in-r x₁
  complete₁-pred-comp₀ ω x i j@(Z ∘ u₁ ↦ ε ∘ β₁) g refl refl | no d =
    complete-predic ω i j g x refl refl

  complete₀-compl₀ : ∀ {t u v w X Y α β} ->
    (ω : EState t w) ->
    Complete ω ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (Σ λ s -> s ++ w ≡ v) ->
    (j : Item t v) ->
    j ≋ g ->
      j ∈ compl₀ ω
  complete₀-compl₀ {t} {u} {v} {w} ω c g p j           with eq-T* v w
  complete₀-compl₀ {t} {u} {v} {v} ω c g p j           | yes refl = fst c j g
  complete₀-compl₀ {w} {u} {v} {w} (start rs) c g p j  | no x =
    void (x (sym (constrained-eq p (suff-g₂ g))))
  complete₀-compl₀ {t} {u} {v} {w} (step ω rs) c g p j | no x =
    complete₀-compl₀ ω (snd c) g (suffix-with-ω (V ω) p (suff-g₂ g)) j

  complete-compl₀ : ∀ {t u v w X Y α β} ->
    (ω : EState t w) ->
    Complete* ω ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (Σ λ s -> s ++ w ≡ v) ->
    (v ≡ w -> Void) ->
    (j : Item t v) ->
    j ≋ g ->
      j ∈ compl₀ ω
  complete-compl₀ {w} {u} {v} {w} (start rs) c g p q j s =
    void (q (sym (constrained-eq p (suff-g₂ g))))
  complete-compl₀ {t} {u} {v} {w} (step ω rs) c g p q j s with eq-T* v w
  complete-compl₀ {t} {u} {v} {w} (step ω rs) c g p q j s | yes x = void (q x)
  complete-compl₀ {t} {u} {v} {w} (step ω rs) c g p q j s | no x =
    complete₀-compl₀ ω c g (suffix-with-ω (V ω) p (suff-g₂ g)) j s

  complete-compl₁ : ∀ {t u v w X Y α β γ} -> ∀ rs ->
    (i : Item t v) ->
    (j k : Item t w) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    i ≋ g ->
    (p : j ≋ h) ->
    i ∈ rs ->
    k ≋ complet g h ->
      k ∈ compl₁ j (≋-β j h p) rs
  complete-compl₁ ε i j k g h o p () s
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs)       i j k g h refl refl (in-tail q) s =
    complete-compl₁ rs i j k g h refl refl q s
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) i j k g h refl refl (in-tail q) s =
    complete-compl₁ rs i j k g h refl refl q s
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) i j k g h refl refl q s           with eqₙ (Item.Y j) Z
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) i j k g h refl refl in-head     s | no x = void (x refl)
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) i j k g h refl refl (in-tail q) s | no x =
    complete-compl₁ rs i j k g h refl refl q s
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) i j k g h refl refl in-head  refl | yes refl = in-head
  complete-compl₁ ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) i j k g h refl refl (in-tail q) s | yes refl =
    in-tail (complete-compl₁ rs i j k g h refl refl q s)

  complete-compl : ∀ {t u v w X Y α β γ} ->
    (ω : EState t w) ->
    Complete* ω ->
    (i j : Item t w) ->
    (v ≡ w -> Void) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    (p : i ≋ h) ->
    j ≋ complet g h ->
      j ∈ compl i (≋-β i h p) ω
  complete-compl ω c i j p g h refl s =
    let x₁ = compl₀ ω in
    let x₂ = complete-compl₀ ω c g (suff-g₃ h) p _ refl in
    complete-compl₁ x₁ (_ ∘ _ ↦ _ ∘ _ [ in-g g ∘ suff-g₁ g ]) i j g h refl refl x₂ s

  complete₂-pred-comp₀ : ∀ {t u v w X Y α β γ} ->
    (ω : EState t w) ->
    Complete* ω ->
    (i j : Item t w) ->
    (v ≡ w -> Void) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    i ≋ h ->
    j ≋ complet g h ->
      j ∈ pred-comp₀ i refl ω
  complete₂-pred-comp₀ ω c i j n g h refl = complete-compl ω c _ _ n g h refl

  complete₃-pred-comp₀ : ∀ {t u v X Y α β γ} ->
    (ω : EState t v) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / γ ∙ ε) ->
    i ≋ g ->
    j ≋ complet g h ->
      j ∈ pred-comp₀ i refl ω
  complete₃-pred-comp₀ {Y = Y} ω i j g h refl refl
      with elem eqₙ Y (nullable G)
  ... | yes x = in-head
  ... | no x = void (x (nullable-complete h))

  complete₁-pred-comp₁ : ∀ {t u v X Y α β δ ss} -> ∀ rs ->
    (ω : EState t v)
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g ->
    i ∈ rs ->
    j ≋ predict x g ->
      j ∈ pred-comp₁ ω ss rs
  complete₁-pred-comp₁ {ss = ss} (i  ∷ rs) ω x i j g o in-head q = in-l (complete₁-pred-comp₀ (Wₙ ω ss) x i j g o q)
  complete₁-pred-comp₁ (r₁ ∷ rs) ω x i j g o (in-tail p) q = in-r (complete₁-pred-comp₁ rs ω x i j g o p q)

  complete₂-pred-comp₁ : ∀ {t u v w X Y α β γ ss} -> ∀ rs ->
    (ω : EState t w) ->
    Complete* ω ->
    (i j : Item t w) ->
    (v ≡ w -> Void) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε) ->
    i ≋ h ->
    i ∈ rs ->
    j ≋ complet g h ->
      j ∈ pred-comp₁ ω ss rs
  complete₂-pred-comp₁ {ss = ss} .(i ∷ _) (start rs)  c i j n g h z₁ in-head z₃ = in-l (complete₂-pred-comp₀ (start ss) top i j n g h z₁ z₃)
  complete₂-pred-comp₁ {ss = ss} .(i ∷ _) (step ω rs) c i j n g h z₁ in-head z₃ = in-l (complete₂-pred-comp₀ (step ω ss) c i j n g h z₁ z₃)
  complete₂-pred-comp₁ {ss = ss} (_ ∷ rs) ω c i j n g h z₁ (in-tail z₂) z₃ = in-r (complete₂-pred-comp₁ rs ω c i j n g h z₁ z₂ z₃)

  complete₃-pred-comp₁ : ∀ {t u v X Y α β γ ss} -> ∀ rs ->
    (ω : EState t v) ->
    Complete* ω ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / γ ∙ ε) ->
    i ≋ g ->
    i ∈ rs ->
    j ≋ complet g h ->
      j ∈ pred-comp₁ ω ss rs
  complete₃-pred-comp₁ {ss = ss} .(i ∷ _) (start rs) c i j g h z₁ in-head z₃ = in-l (complete₃-pred-comp₀ (start ss) i j g h z₁ z₃)
  complete₃-pred-comp₁ {ss = ss} .(i ∷ _) (step ω rs) c i j g h z₁ in-head z₃ = in-l (complete₃-pred-comp₀ (step ω ss) i j g h z₁ z₃)
  complete₃-pred-comp₁ {ss = ss} (_ ∷ rs) ω c i j g h z₁ (in-tail z₂) z₃ = in-r (complete₃-pred-comp₁ rs ω c i j g h z₁ z₂ z₃)

  in-after : ∀ {v w} ->
    (i : Item w v) ->
    (ω : EState w v) ->
    (rs ss : Item w v *)
    (m : ℕ)
    (p : suc (length (Σ.proj₁ (all-items {w} {v}) \\ ss)) ≤ m)
    (q : Unique (rs ++ ss)) ->
      Set
  in-after i ω rs ss zero () q
  in-after i ω ε ss (suc m) p q = ⊥
  in-after i ω rs@(_ ∷ _) ss (suc m) p q =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let q₁ = wf-pcw₂ x₁ (rs ++ ss) q in
    i ∈ Sₙ (pred-comp₂ ω (rs ++ ss) x₂ m p₁ q₁)

  complete₁₋₁-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : EState t v) ->
    (i : Item t v) ->
    in-after i ω rs ss m p q ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₋₁-pred-comp₂ ss rs zero () q ω i a
  complete₁₋₁-pred-comp₂ ss ε (suc m) p q ω i ()
  complete₁₋₁-pred-comp₂ ss (x ∷ rs) (suc m) p q ω i a = a

  complete₁₀-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : EState t v) ->
    (i : Item t v) ->
    i ∈ ss ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₀-pred-comp₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₀-pred-comp₂ {ss = ss} {ε} {suc m} {p} (start rs) i s = s
  complete₁₀-pred-comp₂ {ss = ss} {ε} {suc m} {p} (step ω rs) i s = s
  complete₁₀-pred-comp₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} {q} ω i s =
    complete₁₀-pred-comp₂ {m = m} ω i (in-r s)

  complete₁₁-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : EState t v) ->
    (i : Item t v) ->
    i ∈ rs ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁₁-pred-comp₂ {ss = ss} {rs} {zero} {()} ω i s
  complete₁₁-pred-comp₂ {ss = ss} {ε} {suc m} {p} ω i ()
  complete₁₁-pred-comp₂ {ss = ss} {rs@(_ ∷ _)} {suc m} {p} ω i s =
    complete₁₀-pred-comp₂ {m = m} ω i (in-l s)

  complete₁₂-pred-comp₂ : ∀ {t v ss rs m p q} ->
    (ω : EState t v) ->
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
    case in-either x₂ (rs ++ ss) y₂ of
      λ { (r z) → complete₁₀-pred-comp₂ {m = m} ω j z
        ; (l z) → complete₁₁-pred-comp₂ {m = m} ω j z
        }

  Inert : ∀ {t v} -> Item t v * -> Item t v * -> Set
  Inert {t} {v} ss rs =
    ∀ {u X Y α β δ} ->
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g -> i ∈ ss ->
    j ≋ predict x g ->
      j ∈ (rs ++ ss)

  inert' : ∀ {t v rs ss} (ω : EState t v) ->
    Inert ss rs ->
    Inert (rs ++ ss) (pred-comp₁ ω ss rs \\ (rs ++ ss))
  inert' {rs = ε} {ss} ω nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  inert' {rs = rs@(r₁ ∷ rs₀)} {ss} ω nx x i j g z₁ z₂ z₃ =
    case in-either rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx x i j g z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) →
        let y₁ = complete₁-pred-comp₁ rs ω x i j g z₁ x₁ z₃ in
        include-\\ y₁
      }

  complete₁-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : EState t v) ->
    Inert ss rs ->
    ∀ {u X Y α β δ}
    (x : (Y , δ) ∈ CFG.rules G) ->
    (i j : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    i ≋ g ->
    i ∈ Sₙ (pred-comp₂ ω ss rs m p q) ->
    j ≋ predict x g ->
      j ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₁-pred-comp₂ ss rs            zero    () q ω           nx
  complete₁-pred-comp₂ ss ε             (suc m) p  q (start rs)  nx = nx
  complete₁-pred-comp₂ ss ε             (suc m) p  q (step ω rs) nx = nx
  complete₁-pred-comp₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           nx =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let q₁ = wf-pcw₂ (pred-comp₁ ω ss rs) (rs ++ ss) q in
    complete₁-pred-comp₂ (rs ++ ss) _ m p₁ q₁ ω (inert' ω nx)

  Inert₂ : ∀ {t v} -> Item t v * -> Item t v * -> Set
  Inert₂ {t} {v} ss rs =
    ∀ {u w X Y α β γ} ->
    (j k : Item t v) ->
    (w ≡ v -> Void) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ ss ->
    k ≋ complet g h ->
      k ∈ (rs ++ ss)

  inert₂' : ∀ {t v rs ss} (ω : EState t v) ->
    Complete* ω ->
    Inert₂ ss rs ->
    Inert₂ (rs ++ ss) (pred-comp₁ ω ss rs \\ (rs ++ ss))
  inert₂' {rs = ε} {ss} ω c nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  inert₂' {t} {v} {rs = rs@(r₁ ∷ rs₀)} {ss} ω c nx {u} {w} j k n g h z₁ z₂ z₃ =
    case in-either rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx j k n g h z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) →
        let y₁ = complete₂-pred-comp₁ rs ω c j k n g h z₁ x₁ z₃ in
        include-\\ y₁
      }

  complete₂-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : EState t v) ->
    Complete* ω ->
    Inert₂ ss rs ->
    ∀ {u w X Y α β γ}
    (j k : Item t v) ->
    (w ≡ v -> Void) ->
    (g : G ∙ t ⊢ u / w ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ w / v ⟶* Y / γ ∙ ε) ->
    j ≋ h -> j ∈ Sₙ (pred-comp₂ ω ss rs m p q) ->
    k ≋ complet g h ->
      k ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₂-pred-comp₂ ss rs            zero    () q ω           c
  complete₂-pred-comp₂ ss ε             (suc m) p  q (start rs)  c nx = nx
  complete₂-pred-comp₂ ss ε             (suc m) p  q (step ω rs) c nx = nx
  complete₂-pred-comp₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           c nx =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let q₁ = wf-pcw₂ (pred-comp₁ ω ss rs) (rs ++ ss) q in
    complete₂-pred-comp₂ (rs ++ ss) _ m p₁ q₁ ω c (inert₂' ω c nx)

  Inert₃ : ∀ {t v} -> Item t v * -> Item t v * -> Set
  Inert₃ {t} {v} ss rs =
    ∀ {u X Y α β γ} ->
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / γ ∙ ε) ->
    j ≋ g -> j ∈ ss ->
    k ≋ complet g h ->
      k ∈ (rs ++ ss)

  inert₃' : ∀ {t v rs ss} (ω : EState t v) ->
    Complete* ω ->
    Inert₃ ss rs ->
    Inert₃ (rs ++ ss) (pred-comp₁ ω ss rs \\ (rs ++ ss))
  inert₃' {rs = ε} {ss} ω c nx x i j g z₁ z₂ z₃ = nx x i j g z₁ z₂ z₃
  inert₃' {t} {v} {rs = rs@(r₁ ∷ rs₀)} {ss} ω c nx {u} {w} j k g h z₁ z₂ z₃ =
    case in-either rs ss z₂ of
      λ { (r x₁) →
        let x₁ = nx j k g h z₁ x₁ z₃  in
        in-r x₁
      ; (l x₁) →
        let y₁ = complete₃-pred-comp₁ rs ω c j k g h z₁ x₁ z₃ in
        include-\\ y₁
      }

  complete₄-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : EState t v) ->
    Complete* ω ->
    Inert₃ ss rs ->
    ∀ {u X Y α β γ}
    (j k : Item t v) ->
    (g : G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β) ->
    (h : G ∙ t ⊢ v / v ⟶* Y / γ ∙ ε) ->
    j ≋ g -> j ∈ Sₙ (pred-comp₂ ω ss rs m p q) ->
    k ≋ complet g h ->
      k ∈ Sₙ (pred-comp₂ ω ss rs m p q)
  complete₄-pred-comp₂ ss rs            zero    () q ω           c
  complete₄-pred-comp₂ ss ε             (suc m) p  q (start rs)  c nx = nx
  complete₄-pred-comp₂ ss ε             (suc m) p  q (step ω rs) c nx = nx
  complete₄-pred-comp₂ ss rs@(r₁ ∷ rs₀) (suc m) p  q ω           c nx =
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let q₁ = wf-pcw₂ (pred-comp₁ ω ss rs) (rs ++ ss) q in
    complete₄-pred-comp₂ (rs ++ ss) _ m p₁ q₁ ω c (inert₃' ω c nx)

  complete-pred-comp₂ : ∀ {a t v ss rs m p q} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : EState t v) ->
    Complete* ω ->
    Inert ss rs ->
    Inert₂ ss rs ->
    Inert₃ ss rs ->
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
  complete-pred-comp₂ {a} {t} {v} {ss} {rs} {m} {p} {q} h ω c nx nx₂ nx₄ s u g i e =
    complete-ind {P = λ i -> i ∈ Sₙ (pred-comp₂ ω ss rs m p q)}
      h
      s
      u
      (complete₁-pred-comp₂ ss rs m p q ω nx)
      (complete₂-pred-comp₂ ss rs m p q ω c nx₂)
      (complete₄-pred-comp₂ ss rs m p q ω c nx₄)
      g i e

  complete₀-pred-comp : ∀ {a t v} ->
    (Σ λ u -> u ++ (a ∷ v) ≡ t) ∣ v ≡ t ->
    (ω : EState t v) ->
    Complete* ω ->
    Inert ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    Inert₂ ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
    Inert₃ ε (Σ.proj₁ (deduplicate (Sₙ ω))) ->
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
  complete₀-pred-comp {a} {t} s ω c nx nx₂ nx₄ fx fx₂ g i p =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    complete-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} s ω c nx nx₂ nx₄
      (λ g₁ i₁ x → complete₁₁-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} ω i₁ (fx g₁ i₁ x))
      (λ {refl x i₁ x₃ → complete₁₁-pred-comp₂ {p = ≤ₛ (≤-self _)} {q = x₂} ω i₁ (fx₂ refl x i₁ x₃)})
      g i p

  complete₃-pred-comp₂ : ∀ {t v} -> ∀ ss rs m p q ->
    (ω : EState t v) ->
    Complete* ω ->
    Complete* (pred-comp₂ ω ss rs m p q)
  complete₃-pred-comp₂ ss rs zero () q ω c
  complete₃-pred-comp₂ ss ε (suc m) p q (start rs) c = top
  complete₃-pred-comp₂ ss ε (suc m) p q (step ω rs) c = c
  complete₃-pred-comp₂ ss rs@(_ ∷ _) (suc m) p q ω c =
    let x₁ = pred-comp₁ ω ss rs in
    let x₂ = x₁ \\ (rs ++ ss) in
    let p₁ = wf-pcw₃ (Σ.proj₀ all-items) p q in
    let q₁ = wf-pcw₂ x₁ (rs ++ ss) q in
    complete₃-pred-comp₂ (rs ++ ss) x₂ m p₁ q₁ ω c

  complete₁-pred-comp : ∀ {t v} ->
    (ω : EState t v) ->
    Complete* ω ->
    Complete* (pred-comp ω)
  complete₁-pred-comp ω =
    let x₁ = deduplicate (Sₙ ω) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    complete₃-pred-comp₂ ε _ _ (≤ₛ (≤-self _)) x₂ ω

  complete₂-pred-comp : ∀ {t v} ->
    (ω : EState t v) ->
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
    (ω : EState t v) ->
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
      x₅ = complete₀-pred-comp s ω c (λ x i j g x₁ ()) (λ j k n g h x ()) (λ j k g h x ())
        (λ {g i x → complete-deduplicate (Sₙ ω) (fx g i x)})
        λ {refl x i x₁ → complete-deduplicate (Sₙ ω) (fx₂ refl x i x₁)}
    in
    complete₂-pred-comp ω c x₅

  complete-step : ∀ {a₀ a t v} ->
    (Σ λ u -> u ++ (a₀ ∷ a ∷ v) ≡ t) ∣ (a ∷ v) ≡ t ->
    (ω : EState t (a ∷ v)) ->
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
    (ω : EState t (a ∷ v)) ->
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
    (ω : EState t v) ->
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
          ; (l (σ p₁ p₀)) → void (ε.ε₂ eqₜ (trans (sym (in₀ _ _ _)) (sym p₀)))
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
