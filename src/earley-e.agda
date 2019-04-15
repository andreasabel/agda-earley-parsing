open import base
open import accessible

module earley-e (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

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
      {𝕦} : T *
      .{χ} : CFG.rules G ∋ (Y , α ++ β)
      .{ψ} : length v ≤ length u

  infixl 3 _∘_↦_∘_

  pattern _∘_↦_∘_[_∘_∘_] Y u α β χ ψ = (Y ∘ u ↦ α ∘ β) {χ} {ψ}
  infixl 3 _∘_↦_∘_[_∘_∘_]

  promote : ∀ {u us} -> Item (u ∷ us) -> Item us
  promote (Y ∘ u ↦ α ∘ β [ 𝕦 ∘ χ ∘ ψ ]) = Y ∘ u ↦ α ∘ β [ 𝕦 ∘ χ ∘ suc-≤ ψ ]

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

  all-rules₀ : ∀ {n} ->
    (X : N) (u : T *) (α β : (N ∣ T) *) ->
    .(CFG.rules G ∋ (X , α ++ β)) ->
    length n ≤ length u ->
    Item n *
  all-rules₀ X j α ε p q = (X ∘ j ↦ α ∘ ε [ 𝕦 ∘ p ∘ q ]) ∷ ε
  all-rules₀ X j α (x ∷ β) p q =
    (X ∘ j ↦ α ∘ x ∷ β [ p ∘ q ]) ∷
    all-rules₀ X j (α ←∷ x) β (in₂ (λ q → CFG.rules G ∋ (X , q)) (in₀ x α β) p) q
  
  all-rules₁ :
    (X : N) (u : T *) (β : (N ∣ T) *) ->
    .(CFG.rules G ∋ (X , β)) ->
    Item u *
  all-rules₁ X ε β p = all-rules₀ X ε ε β p ≤₀
  all-rules₁ X (u ∷ us) β p = all-rules₀ X (u ∷ us) ε β p (≤-self _) ++ map {!!} (all-rules₁ X us β p)

  all-rules₂ : (u : T *) -> (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) -> Item u *
  all-rules₂ j ε f = ε
  all-rules₂ j ((X , β) ∷ rs) f = all-rules₁ X j β (f in-head) ++ all-rules₂ j rs (f ∘ in-tail)
  
  all-rules : (u : T *) -> Item u *
  all-rules j = all-rules₂ j (CFG.rules G) id

  in-all₀₀ : ∀ {j} ->
    (i : Item j) ->
      all-rules₀ (Item.Y i) (Item.u i) (Item.α i) (Item.β i) (Item.χ i) {!!} ∋ i
  in-all₀₀ (Y ∘ j ↦ α ∘ ε) = in-head
  in-all₀₀ (Y ∘ j ↦ α ∘ x ∷ β) = in-head

  in-all₀₁ : ∀ {γ η j} ->
    (i : Item j) ->
    .{χ : _} ->
    (p : Item.α i ≡ γ ++ η) ->
      all-rules₀ (Item.Y i) (Item.u i) γ (η ++ Item.β i) χ {!!} ∋ i
  in-all₀₁ {γ} {ε} (Y ∘ j ↦ .(γ ++ ε) ∘ β [ χ ∘ ψ ]) {χ₂} refl =
    let x₁ = in₂ (λ μ -> ∀ .{χ} -> all-rules₀ Y j γ β χ₂ {!!} ∋ (Y ∘ j ↦ μ ∘ β [ χ ∘ ψ ])) (sym (++-ε γ)) in
    let x₂ = in₂ (λ χ -> CFG.rules G ∋ (Y , (χ ++ β))) (++-ε γ) in
    x₁ (in-all₀₀ ((Y ∘ j ↦ γ ∘ β)) ) {χ}
  in-all₀₁ {γ} {x ∷ η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀}) {χ} p =
    let x₁ = trans p (sym (in₀ x γ η)) in
    let x₂ = in-all₀₁ {γ ←∷ x} {η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀}) {in₂ (λ x₂ → CFG.rules G ∋ (Y , x₂)) (in₀ x γ (η ++ β)) χ} x₁ in
    in-tail x₂

  in-all₀ : ∀ {j} ->
    (i : Item j) ->
      all-rules₀ (Item.Y i) (Item.u i) ε (Item.α i ++ Item.β i) (Item.χ i) {!!} ∋ i
  in-all₀ i = in-all₀₁ i {Item.χ i} refl

  in-all₁ : ∀ {j} ->
    (i : Item j) ->
      all-rules₁ (Item.Y i) j (Item.α i ++ Item.β i) (Item.χ i) ∋ i
  in-all₁ {j}         (Y ∘ k ↦ α ∘ β [ χ ∘ ψ ])      with eq-T* j k
  in-all₁ {.ε}        (Y ∘ ε ↦ α ∘ β [ χ ∘ ψ ])      | yes refl = in-all₀ (Y ∘ ε ↦ α ∘ β)
  in-all₁ {.(k ∷ ks)} (Y ∘ k ∷ ks ↦ α ∘ β [ χ ∘ ψ ]) | yes refl = in-l (in-all₀ (Y ∘ (k ∷ ks) ↦ α ∘ β))
  in-all₁ {ε}         (Y ∘ ε ↦ α ∘ β [ χ ∘ ψ ])      | no x = void (x refl)
  in-all₁ {ε}         (Y ∘ k ∷ ks ↦ α ∘ β [ χ ∘ ψ ]) | no x = {!!}
  in-all₁ {j ∷ js}    (Y ∘ ε ↦ α ∘ β [ χ ∘ ψ ])      | no x = in-r (in-map {!!} {_} {Y ∘ ε ↦ α ∘ β [ χ ∘ {!!} ]} (in-all₁ ((Y ∘ ε ↦ α ∘ β) {χ})))
  in-all₁ {j ∷ js}    (Y ∘ k ∷ ks ↦ α ∘ β [ χ ∘ ψ ]) | no x = in-r (in-map {!!} {_} {Y ∘ k ∷ ks ↦ α ∘ β [ χ ∘ {!suffix-∷!} ]} (in-all₁ (Y ∘ (k ∷ ks) ↦ α ∘ β)))

  in-all₂ : ∀ {j} ->
    (i : Item j) ->
    (xs : (N × (N ∣ T) *) *) ->
    (q : xs ∋ (Item.Y i , Item.α i ++ Item.β i) ) -> 
    (f : ∀ {r} -> xs ∋ r -> CFG.rules G ∋ r) ->
      all-rules₂ j xs f ∋ i
  in-all₂ i ε () f
  in-all₂ i ((Y , β) ∷ xs) in-head f = in-l (in-all₁ i)
  in-all₂ i ((Y , β) ∷ xs) (in-tail q) f = in-r (in-all₂ i xs q (f ∘ in-tail))

  relevant-χ : ∀ {j} -> (i : Item j) -> CFG.rules G ∋ (Item.Y i , Item.α i ++ Item.β i)
  relevant-χ ((Y ∘ j ↦ α ∘ β) {χ}) = elem' eq-rule (Y , α ++ β) (CFG.rules G) χ

  in-all : ∀ {j} -> (i : Item j) -> all-rules j ∋ i
  in-all i = in-all₂ i (CFG.rules G) (relevant-χ i) id

  open Unique Item eq-item
  
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
  scanner-w₀ a ((X ∘ u ↦ α ∘ r b ∷ β [ χ ∘ ψ ]) ∷ rs) with decidₜ a b
  ... | yes refl = (X ∘ u ↦ α ←∷ r a ∘ β [ v-step χ ∘ suc-≤ ψ ]) ∷ (scanner-w₀ a rs)
  ... | no x = scanner-w₀ a rs
  
  Valid : ∀ {v} -> Item v -> Set
  Valid {v} i = G ⊢ Item.u i / v ⟶* Item.Y i / Item.β i

  Sound : ∀ {v} -> WSet v -> Set
  Sound {v₁} (start v₁ rs) = ∀ {i} -> i ∈ rs -> Valid i
  Sound {v} (step w rs) = Sound w × (∀ {i} -> i ∈ rs -> Valid i)

  H : ∀ {v w} -> Sound {v} w -> (∀ {i} -> i ∈ Sₙ w -> Valid i)
  H {v₁} {start v₁ rs} s = s
  H {v} {step w rs} s = snd s

  sound-scanner-w₀ : ∀ {a v} -> ∀ rs ->
    (∀ {i} -> i ∈ rs -> Valid i) ->
    (∀ {i} -> i ∈ scanner-w₀ {v} a rs -> Valid i)
  sound-scanner-w₀ ε f ()
  sound-scanner-w₀ ((X ∘ u ↦ α ∘ ε) ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ ((X ∘ u ↦ α ∘ l Y ∷ β) ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p with decidₜ a b
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r b ∷ β) ∷ rs) f p | no x = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) f in-head | yes refl = scanner (f in-head)
  sound-scanner-w₀ {a} ((X ∘ u ↦ α ∘ r a ∷ β) ∷ rs) f (in-tail p) | yes refl
    = sound-scanner-w₀ rs (f ∘ in-tail) p

  scanner-w :
    (a : T) (v : T *) ->
    WSet (a ∷ v) ->
    WSet v
  scanner-w a v w = step w (scanner-w₀ a (Sₙ w))

  sound-scanner-w : ∀ {a v} -> ∀ w ->
    Sound w -> Sound (scanner-w a v w)
  sound-scanner-w (start v rs) s = s , sound-scanner-w₀ rs s
  sound-scanner-w (step w rs) (s , s₁) = s , s₁ , sound-scanner-w₀ rs s₁

  complete-w₀ : ∀ {u v} ->
    (w : WSet v) ->
    Item u *
  complete-w₀ {u} {v} w            with eq-T* u v
  complete-w₀ {u} {u} w            | yes refl = Sₙ w
  complete-w₀ {u} {v} (start v rs) | no x = ε
  complete-w₀ {u} {v} (step w rs)  | no x = complete-w₀ w

  sound-complete-w₀ : ∀ {u v} -> ∀ w ->
    Sound w -> (∀ {i} -> i ∈ complete-w₀ {u} {v} w -> Valid i)
  sound-complete-w₀ {u} {v} w s p             with eq-T* u v
  sound-complete-w₀ {v} {v} w s p             | yes refl = H s p
  sound-complete-w₀ {u} {v} (start v rs) s () | no x
  sound-complete-w₀ {u} {v} (step w rs) s p   | no x = sound-complete-w₀ w (fst s) p

  complete-w₁ : ∀ {X u v α} -> ∀ .χ .ψ ->
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])->
    Item u * -> Item v *
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ε = ε
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ ε) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ r a ∷ β) ∷ rs) = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) with decidₙ X Z
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l Z ∷ β) ∷ rs) | no x = complete-w₁ χ ψ _ refl rs
  complete-w₁ χ ψ (X ∘ u ↦ α ∘ ε) refl ((Y ∘ u₁ ↦ α₁ ∘ l X ∷ β [ χ₁ ∘ ψ₁ ]) ∷ rs) | yes refl =
    (Y ∘ u₁ ↦ α₁ ←∷ l X ∘ β [ v-step χ₁ ∘ {!!} ]) ∷ complete-w₁ χ ψ _ refl rs

  sound-complete-w₁ : ∀ {X u v α} -> ∀ .χ .ψ ->
    (i : Item v) -> (p : i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])) ->
    (rs : Item u *) ->
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

  complete-w₂ : ∀ {u X v α} -> ∀ .χ .ψ ->
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ]) ->
    WSet v ->
    Item v *
  complete-w₂ χ ψ i p w = complete-w₁ χ ψ i p (complete-w₀ w)

  sound-complete-w₂ : ∀ {u X v α} -> ∀ .χ .ψ ->
    (i : Item v) -> (p : i ≡ (X ∘ u ↦ α ∘ ε [ χ ∘ ψ ])) ->
    Valid i -> (w : WSet v) -> Sound w ->
    (∀ {j} -> j ∈ complete-w₂ χ ψ i p w -> Valid j)
  sound-complete-w₂ χ ψ i p v w s q =
    sound-complete-w₁ χ ψ i p (complete-w₀ w) v (sound-complete-w₀ w s) q
  
  predict-w₀ : ∀ {u v X α Y β} -> ∀ .χ .ψ ->
    (i : Item v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) * ->
    Item v *
  predict-w₀ χ ψ i p ε = ε
  predict-w₀ {u} {v} χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ ps) =
    (Y ∘ v ↦ ε ∘ γ [ p ∘ {!!} ]) ∷ (predict-w₀ {u} χ ψ _ refl ps)

  sound-predict-w₀ : ∀ {u v X α Y β} -> ∀ .χ .ψ ->
    (i : Item v) -> (p : i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ])) ->
    (f : (Σ λ t -> (t ∈ CFG.rules G) × (fst t ≡ Y)) *) ->
    Valid i ->
    (∀ {j} -> j ∈ predict-w₀ χ ψ i p f -> Valid j)
  sound-predict-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl ε v ()
  sound-predict-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v in-head = predict p v
  sound-predict-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl (σ (Y , γ) (p , refl) ∷ f) v (in-tail q) =
    sound-predict-w₀ χ ψ _ refl f v q

  predict-w₁ : ∀ {u X v α Y β} -> ∀ .χ .ψ ->
    (i : Item v) ->  i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ]) ->
    WSet v ->
    Item v *
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w with lookup Y (CFG.rules G)
  predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w | ps = predict-w₀ {u} χ ψ _ refl ps

  sound-predict-w₁ : ∀ {v X u α Y β} -> ∀ .χ .ψ ->
    (i : Item v) ->  (p : i ≡ (X ∘ u ↦ α ∘ l Y ∷ β [ χ ∘ ψ ])) ->
    (w : WSet v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ predict-w₁ χ ψ i p w -> Valid j)
  sound-predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q with lookup Y (CFG.rules G)
  sound-predict-w₁ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q | ps = sound-predict-w₀ χ ψ _ refl ps v q

  deduplicate : ∀ {v} -> Item v * -> Σ {Item v *} λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with elem eq-item x (Σ.proj₁ (deduplicate as))
  deduplicate (x ∷ as) | yes x₁ = deduplicate as
  deduplicate (x ∷ as) | no x₁ = σ (x ∷ (Σ.proj₁ (deduplicate as))) (u-∷ (Σ.proj₀ (deduplicate as)) x₁)

  sound-deduplicate : ∀ {v} -> (as : Item v *) ->
    (∀ {i} -> i ∈ as -> Valid i) ->
    (∀ {i} -> i ∈ Σ.proj₁ (deduplicate as) -> Valid i)
  sound-deduplicate ε f ()
  sound-deduplicate (x ∷ as) f p           with elem eq-item x (Σ.proj₁ (deduplicate as))
  sound-deduplicate (x ∷ as) f p           | yes x₁ = sound-deduplicate as (f ∘ in-tail) p
  sound-deduplicate (x ∷ as) f in-head     | no x₁ = f in-head
  sound-deduplicate (x ∷ as) f (in-tail p) | no x₁ = sound-deduplicate as (f ∘ in-tail) p
  
  pred-comp-w₀ : ∀ {u v X α β} -> ∀ .χ .ψ
    (i : Item v) -> i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ]) ->
    (w : WSet v) ->
    Σ {Item v *} λ as -> Unique as
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ ε) refl w = deduplicate (complete-w₂ {u} χ ψ _ refl w)
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ r a ∷ β) refl w = σ ε u-ε
  pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w = deduplicate (predict-w₁ {u} χ ψ _ refl w)

  sound-pred-comp-w₀ : ∀ {u v X α β} -> ∀ .χ .ψ
    (i : Item v) -> (p : i ≡ (X ∘ u ↦ α ∘ β [ χ ∘ ψ ])) ->
    (w : WSet v) ->
    Valid i -> Sound w ->
    (∀ {j} -> j ∈ Σ.proj₁ (pred-comp-w₀ χ ψ i p w) -> Valid j)
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ ε) refl w v s q =
    sound-deduplicate (complete-w₂ {u} χ ψ _ refl w) (sound-complete-w₂ χ ψ _ refl v w s) q
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ r a ∷ β) refl w v s ()
  sound-pred-comp-w₀ χ ψ (X ∘ u ↦ α ∘ l Y ∷ β) refl w v s q =
    sound-deduplicate (predict-w₁ {u} χ ψ _ refl w) (sound-predict-w₁ χ ψ _ refl w v s) q

  pred-comp-w₂ : {n : T *} ->
    (w : WSet n) ->
    (ss : Item n *) ->
    (rs : Item n *) ->
    (m : ℕ) ->
    (p : m ≡ suc (length (all-rules n \\ ss))) -> 
    Unique (rs ++ ss) ->
    WSet n
  pred-comp-w₂ w ss rs zero () q
  pred-comp-w₂ w ss ε (suc m) p q = w
  pred-comp-w₂ {n} w ss (r₁ ∷ rs) (suc m) p q =
    let x₁ = pred-comp-w₀ _ _ r₁ refl w in
    let x₂ = Σ.proj₁ x₁ \\ (r₁ ∷ (ss ++ rs)) in
    let p₁ = trans (unsuc p) (sym (diff-suc eq-item (in-all _) (eq-not q in-head))) in
    let p₂ = (unique-\\ (Σ.proj₁ x₁) (r₁ ∷ (ss ++ rs)) (Σ.proj₀ x₁)) in
    let p₃ = (u-∷ p₂ (no-include-\\₂ (Σ.proj₁ x₁) _ in-head)) in
    let p₄ = (tmp rs x₂ ss q p₃ (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-r x))) (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-l x)))) in
    pred-comp-w₂ w (r₁ ∷ ss) (rs ++ x₂) m p₁ p₄

  pred-comp-w : ∀ {v} ->
    WSet v ->
    WSet v
  pred-comp-w {v} w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    let m = suc (length (all-rules v \\ ε)) in
    pred-comp-w₂ (Wₙ w ε) ε (Σ.proj₁ x₁) m (app suc refl) x₂

  step-w : ∀ {a v} ->
    WSet (a ∷ v) ->
    WSet v
  step-w {a = a} {v = v} w = scanner-w a v (pred-comp-w w)
  
  parse : ∀ {v} ->
     WSet v ->
     WSet ε
  parse {v = ε} w = pred-comp-w w
  parse {v = x ∷ v} w = parse (step-w w)
