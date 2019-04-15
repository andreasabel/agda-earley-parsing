open import base
open import accessible

module earley (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T

module parser (G : CFG) where

  open import count N T decidₙ decidₜ
  
  v-step : ∀ {Y α x β} -> CFG.rules G ∋ (Y , α ++ (x ∷ β)) -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β)
  v-step {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (in₀ x α β) v

  record Item (v : T *) : Set where
    constructor _∘_↦_∘_
    field
      Y : N
      u : T *
      α β : (N ∣ T) *
      .{χ} : CFG.rules G ∋ (Y , α ++ β)
      .{ψ} : G ⊢ u / v ⟶* Y / β

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
  
  eq-item : ∀ {v} -> (a b : Item v) -> a ≡ b ??
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) with eq-N X Y , eq-T* j k , eq-α α₁ α₂ , eq-α β₁ β₂
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (X ∘ j ↦ α₁ ∘ β₁) | yes refl , yes refl , yes refl , yes refl = yes refl
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | no x₁ , x₂ , x₃ , x₄ = no (λ {refl → x₁ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , no x₂ , x₃ , x₄ = no (λ {refl → x₂ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , no x₃ , x₄ = no (λ {refl → x₃ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , x₃ , no x₄ = no (λ {refl → x₄ refl})

  data _suffOf_ {T : Set} : T * -> T * -> Set where
    suffix-id : {as : T *} -> as suffOf as
    suffix-∷ : {b : T} {as bs : T *} -> as suffOf bs -> as suffOf b ∷ bs
  infix 18 _suffOf_

  all-rules₀ : ∀ {v} ->
    ∀ Y u α β ->
    Σ λ as -> ∀ γ δ .χ .ψ ->
      (i : Item v) -> i ≡ (Y ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) ->
      δ suffOf β -> α ++ β ≡ γ ++ δ ->
      (Y , u , γ , δ) ∈ as
  all-rules₀ Y u α ε = σ ((Y , u , α , ε) ∷ ε) λ { γ ε χ ψ i x suffix-id q → {!q!}}
  all-rules₀ Y u α (x ∷ β) with all-rules₀ Y u (α ←∷ x) β
  all-rules₀ Y u α (x ∷ β) | σ p₁ p₀ = σ ((Y , u , α , x ∷ β) ∷ p₁) λ {
      γ β χ ψ i x₁ suffix-id q → {!!} ;
      γ δ χ ψ i x₁ (suffix-∷ p) q → in-tail (p₀ γ δ χ ψ i x₁ p (trans (sym (in₀ x α β)) (sym q)))
    }
  
  all-rules₁ : ∀ {v} ->
    ∀ Y u β ->
    Σ λ as -> ∀ γ δ .χ .ψ ->
      (i : Item v) -> i ≡ (Y ∘ u ↦ γ ∘ δ [ χ ∘ ψ ]) ->
      γ ++ δ ≡ β ->
      (Y , u , γ , δ) ∈ as
  all-rules₁ Y u β  = {!!}

  all-rules : ∀ {v} ->
    Σ λ as -> {i : Item v} -> i ∈ as
  all-rules = {!!}
  
  --all-rules₀ : ∀ {n} ->
  --  (X : N) (j : ℕ) (α β : (N ∣ T) *) ->
  --  .(CFG.rules G ∋ (X , α ++ β)) ->
  --  .(j ≤ n) ->
  --  Item n *
  --all-rules₀ X j α ε p q = (X ∘ j ↦ α ∘ ε) {p} {q} ∷ ε
  --all-rules₀ X j α (x ∷ β) p q =
  --  (X ∘ j ↦ α ∘ x ∷ β) {p} {q} ∷
  --  all-rules₀ X j (α ←∷ x) β (in₂ (λ q → CFG.rules G ∋ (X , q)) (in₀ x α β) p) q
  
  --all-rules₁ :
  --  (X : N) (j : ℕ) (β : (N ∣ T) *) ->
  --  .(CFG.rules G ∋ (X , β)) ->
  --  Item j *
  --all-rules₁ X zero β p = all-rules₀ X zero ε β p ≤₀
  --all-rules₁ X (suc j) β p = all-rules₀ X (suc j) ε β p (≤-self _) ++ map promote (all-rules₁ X j β p)
  --
  --all-rules₂ : (j : ℕ) -> (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) -> Item j *
  --all-rules₂ j ε f = ε
  --all-rules₂ j ((X , β) ∷ rs) f = all-rules₁ X j β (f in-head) ++ all-rules₂ j rs (f ∘ in-tail)
  --
  --all-rules : (j : ℕ) -> Item j *
  --all-rules j = all-rules₂ j (CFG.rules G) id

  open Unique Item eq-item
  
  relevant-χ : ∀ {v} -> (i : Item v) -> CFG.rules G ∋ (Item.Y i , Item.α i ++ Item.β i)
  relevant-χ ((Y ∘ j ↦ α ∘ β) {χ}) = elem' eq-rule (Y , α ++ β) (CFG.rules G) χ

  data WSet : T * -> Set where
    start :
      (v : T *) ->
      (rs : Item v * ) ->
      WSet v
  
    step : {a : T} {v : T *} ->
      (w : WSet (a ∷ v)) ->
      (rs : Item v * ) ->
      WSet v
  
  Sₙ : {v : T *} ->
    WSet v ->
    Item v *
  Sₙ (start v rs) = rs
  Sₙ (step w rs) = rs

  Wₙ : {v : T *} ->
    (w : WSet v) ->
    (rs : Item v * ) ->
    WSet v
  Wₙ (start v rs) rs₁ = start v rs₁
  Wₙ (step w rs) rs₁ = step w rs₁
  
  scanner-w₀ : ∀ {v} ->
    (a : T) ->
    Item (a ∷ v)* ->
    Item v *
  scanner-w₀ a ε = ε
  scanner-w₀ a ((X ∘ u ↦ α ∘ ε) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β) {χ} {ψ} ∷ rs) with decidₜ a b
  ... | yes refl = (X ∘ u ↦ α ←∷ r a ∘ β [ v-step χ ∘ scanner ψ ]) ∷ (scanner-w₀ a rs)
  ... | no x = scanner-w₀ a rs
  
  scanner-w :
    (a : T) (v : T *) ->
    WSet (a ∷ v) ->
    WSet v
  scanner-w a v w = step w (scanner-w₀ a (Sₙ w))

  complete-w₀ : ∀ {u v} ->
    (w : WSet v) ->
    Item u *
  complete-w₀ {u} {v} w            with eq-T* u v
  complete-w₀ {u} {u} w            | yes refl = Sₙ w
  complete-w₀ {u} {v} (start v rs) | no x = ε
  complete-w₀ {u} {v} (step w rs)  | no x = complete-w₀ w

  complete-w₁ : ∀ {X u v α} -> ∀ .χ .ψ ->
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])->
    Item u * -> Item v *
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ε = ε
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) with decidₙ X Z
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) | no x = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β [ χ₁ ∘ ψ₁ ]) ∷ rs) | yes refl =
    (Y ∘ u₁ ↦ α₁ ←∷ l X ∘ β [ v-step χ₁ ∘ complet ψ₁ ψ ]) ∷ complete-w₁ χ ψ _ refl rs

  complete-w₂ : ∀ {X u v α} -> ∀ .χ .ψ ->
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ]) ->
    WSet v ->
    Item v *
  complete-w₂ χ ψ i p w = complete-w₁ χ ψ i p (complete-w₀ w)
  
  predict-w₀ : ∀ {v X u α Y β} -> ∀ .χ .ψ ->
    (i : Item v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) * ->
    Item v *
  predict-w₀ χ ψ i p ε = ε
  predict-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ ps) =
    (Y ∘ _ ↦ ε ∘ γ [ p ∘ predict p ψ ]) ∷ (predict-w₀ χ ψ _ refl ps)

  predict-w₁ : ∀ {v X u α Y β} -> ∀ .χ .ψ ->
    (i : Item v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    WSet v ->
    Item v *
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w with lookup Y (CFG.rules G)
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w | ps = predict-w₀ χ ψ _ refl ps

  deduplicate : ∀ {v} -> Item v * -> Σ {Item v *} λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with deduplicate as
  deduplicate (x ∷ as) | σ p₁ p₀ with elem eq-item x p₁
  deduplicate (x ∷ as) | σ p₁ p₀ | yes x₁ = σ p₁ p₀
  deduplicate (x ∷ as) | σ p₁ p₀ | no x₁ = σ (x ∷ p₁) (u-∷ p₀ x₁)
  
  pred-comp-w₀ : ∀ {v X u α β} -> ∀ .χ .ψ
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ->
    (w : WSet v) ->
    Σ {Item v *} λ as -> Unique as
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ ε) refl w = deduplicate (complete-w₂ χ ψ _ refl w)
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ r a ∷ β) refl w = σ ε u-ε
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w = deduplicate (predict-w₁ χ ψ _ refl w)

  pred-comp-w₂ : {v : T *} ->
    (w : WSet v) ->
    (ss : Item v *) ->
    (rs : Item v *) ->
    (m : ℕ) ->
    (p : m ≡ (suc ∘ length) (Σ.proj₁ all-rules \\ ss)) -> 
    Unique (rs ++ ss) ->
    WSet v
  pred-comp-w₂ w ss rs zero () q
  pred-comp-w₂ w ss ε (suc m) p q = w
  pred-comp-w₂ {v} w ss (r₁ ∷ rs) (suc m) p q =
    let x₁ = pred-comp-w₀ _ _ r₁ refl (Wₙ w ss) in
    let x₂ = Σ.proj₁ x₁ \\ (r₁ ∷ (ss ++ rs)) in
    let p₁ = trans (unsuc p) (sym (diff-suc {ys = ss} eq-item (Σ.proj₀ all-rules) (eq-not q in-head))) in
    let p₂ = (unique-\\ (Σ.proj₁ x₁) (r₁ ∷ (ss ++ rs)) (Σ.proj₀ x₁)) in
    let p₃ = (u-∷ p₂ (no-include-\\₂ (Σ.proj₁ x₁) _ in-head)) in
    let p₄ = (tmp rs x₂ ss q p₃ (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-r x))) (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-l x)))) in
    pred-comp-w₂ w (r₁ ∷ ss) (rs ++ x₂) m p₁ p₄

  pred-comp-w : ∀ {v} ->
    WSet v ->
    WSet v
  pred-comp-w w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    pred-comp-w₂ (Wₙ w ε) ε (Σ.proj₁ x₁) m (app suc refl) x₂
    where
      m = suc (length (Σ.proj₁ all-rules \\ ε))

  step-w : ∀ {a v} ->
    WSet (a ∷ v) ->
    WSet v
  step-w {a = a} {v = v} w = scanner-w a v (pred-comp-w w)
  
  parse : ∀ {v} ->
     WSet v ->
     WSet ε
  parse {v = ε} w = pred-comp-w w
  parse {v = x ∷ v} w = parse (step-w w)
