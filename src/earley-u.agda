open import base
open import accessible

module earley-u (N T : Set) (n : StrictOrder N) (t : StrictOrder T) where

open import grammar N T

module parser (G : CFG) where

  decidₙ : (x x₁ : N) → x ≡ x₁ ??
  decidₙ = decid-≡ n

  decidₜ : (x x₁ : T) → x ≡ x₁ ??
  decidₜ = decid-≡ t
  
  open import count N T decidₙ decidₜ
  
  v-step : ∀ {Y α x β} -> CFG.rules G ∋ (Y , α ++ (x ∷ β)) -> CFG.rules G ∋ (Y , (α ←∷ x) ++ β)
  v-step {Y} {α} {x} {β} v = in₂ (λ x → CFG.rules G ∋ (Y , x)) (in₀ x α β) v

  record Item (n : ℕ) : Set where
    constructor _∘_↦_∘_
    field
      Y : N
      j : ℕ
      α β : (N ∣ T) *
      .{χ} : CFG.rules G ∋ (Y , α ++ β)
      .{ω} : j ≤ n
  infixl 3 _∘_↦_∘_


  module unique-item {n : ℕ} where
    
    ord-item : StrictOrder (Item n)
    ord-item = record {
      _<_ = {!!} ;
      transitive = {!!} ;
      tri = {!!} ;
      tri₁ = {!!} ;
      tri₂ = {!!}
      }

    open import unique ord-item public


  module fmap where

    open unique-item 

    fmap' : {m n : ℕ} {a : Item n} -> (Item n -> Item m) -> Uniq {n} a -> Unique {m}
    fmap' f (leaf a) = ⟫ leaf (f a)
    fmap' f (node a x as) = insert (f a) (fmap' f as)

    fmap : {m n : ℕ} -> (Item n -> Item m) -> Unique {n} -> Unique {m}
    fmap f empt = empt
    fmap f (⟫ x) = fmap' f x

    in-fmap' : {m n : ℕ} {a : Item n} (f : Item n -> Item m) {as : Uniq {n} a} {a : Item n} ->
      a isin' as -> f a isin fmap' f as
    in-fmap' f inₗ = in⟫ inₗ
    in-fmap' f (inₕ p) = in-insert
    in-fmap' f (inₜ p x₁) = in-already (in-fmap' f x₁)

    in-fmap : {m n : ℕ} (f : Item n -> Item m) {as : Unique {n}} {a : Item n} ->
      a isin as -> f a isin fmap f as
    in-fmap f {empt} ()
    in-fmap f {⟫ x} (in⟫ p) = in-fmap' f p

  open fmap
  open unique-item


  promote : ∀ {n} -> Item n -> Item (suc n)
  promote ((Y ∘ j ↦ α ∘ β) {χ} {ω}) = (Y ∘ j ↦ α ∘ β) {χ} {≤-suc ω}
  
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

  eq-rule : (a b : N × (N ∣ T) *) -> a ≡ b ??
  eq-rule (X , α) (Y , β) with eq-N X Y , eq-α α β
  eq-rule (X , α) (X , α) | yes refl , yes refl = yes refl
  eq-rule (X , α) (Y , β) | yes x , no x₁ = no λ {refl → x₁ refl}
  eq-rule (X , α) (Y , β) | no x , x₁ = no λ {refl → x refl}
  
  eq-item : ∀ {n} -> (a b : Item n) -> a ≡ b ??
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) with eq-N X Y , eq-ℕ j k , eq-α α₁ α₂ , eq-α β₁ β₂
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (X ∘ j ↦ α₁ ∘ β₁) | yes refl , yes refl , yes refl , yes refl = yes refl
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | no x₁ , x₂ , x₃ , x₄ = no (λ {refl → x₁ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , no x₂ , x₃ , x₄ = no (λ {refl → x₂ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , no x₃ , x₄ = no (λ {refl → x₃ refl})
  eq-item (X ∘ j ↦ α₁ ∘ β₁) (Y ∘ k ↦ α₂ ∘ β₂) | x₁ , x₂ , x₃ , no x₄ = no (λ {refl → x₄ refl})
  
  all-rules₀ : ∀ {n} ->
    (X : N) (j : ℕ) (α β : (N ∣ T) *) ->
    .(CFG.rules G ∋ (X , α ++ β)) ->
    .(j ≤ n) ->
    Unique {n}
  all-rules₀ X j α ε p q = ⟫ leaf ((X ∘ j ↦ α ∘ ε) {p} {q})
  all-rules₀ X j α (x ∷ β) p q = insert
    ((X ∘ j ↦ α ∘ x ∷ β) {p} {q})
    (all-rules₀ X j (α ←∷ x) β (in₂ (λ q → CFG.rules G ∋ (X , q)) (in₀ x α β) p) q)
  
  all-rules₁ :
    (X : N) (j : ℕ) (β : (N ∣ T) *) ->
    .(CFG.rules G ∋ (X , β)) ->
    Unique {j}
  all-rules₁ X zero β p = all-rules₀ X zero ε β p ≤₀
  all-rules₁ X (suc j) β p = all-rules₀ X (suc j) ε β p (≤-self _) ∷∷ fmap promote (all-rules₁ X j β p)

  all-rules₂ : (j : ℕ) -> (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) -> Unique {j}
  all-rules₂ j ε f = empt
  all-rules₂ j ((X , β) ∷ rs) f = all-rules₁ X j β (f in-head) ∷∷ all-rules₂ j rs (f ∘ in-tail)
  
  all-rules : (j : ℕ) -> Unique {j}
  all-rules j = all-rules₂ j (CFG.rules G) id

  in-all₀₀ : ∀ {j} ->
    (i : Item j) ->
      i isin all-rules₀ (Item.Y i) (Item.j i) (Item.α i) (Item.β i) (Item.χ i) (Item.ω i) 
  in-all₀₀ (Y ∘ j ↦ α ∘ ε) = in⟫ inₗ
  in-all₀₀ (Y ∘ j ↦ α ∘ x ∷ β) = in-insert

  in-all₀₁ : ∀ {γ η j} ->
    (i : Item j) ->
    .{χ : _} ->
    (p : Item.α i ≡ γ ++ η) ->
      i isin all-rules₀ (Item.Y i) (Item.j i) γ (η ++ Item.β i) χ (Item.ω i)
  in-all₀₁ {γ} {ε} ((Y ∘ j ↦ .(γ ++ ε) ∘ β) {χ} {ω}) {χ₂} refl =
    let x₁ = in₂ (λ μ -> ∀ .{χ} -> (Y ∘ j ↦ μ ∘ β) {χ} {ω} isin all-rules₀ Y j γ β χ₂ ω) (sym (++-ε γ)) in
    let x₂ = in₂ (λ χ -> CFG.rules G ∋ (Y , (χ ++ β))) (++-ε γ) in
    x₁ (in-all₀₀ ((Y ∘ j ↦ γ ∘ β)) ) {χ}
  in-all₀₁ {γ} {x ∷ η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀} {ω}) {χ} p =
    let x₁ = trans p (sym (in₀ x γ η)) in
    let x₂ = in-all₀₁ {γ ←∷ x} {η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀} {ω}) {in₂ (λ x₂ → CFG.rules G ∋ (Y , x₂)) (in₀ x γ (η ++ β)) χ} x₁ in
    in-already x₂

  in-all₀ : ∀ {j} ->
    (i : Item j) ->
      i isin all-rules₀ (Item.Y i) (Item.j i) ε (Item.α i ++ Item.β i) (Item.χ i) (Item.ω i)
  in-all₀ i = in-all₀₁ {ε} {Item.α i} i {Item.χ i} refl

  in-all₁ : ∀ {j} ->
    (i : Item j) ->
      i isin all-rules₁ (Item.Y i) j (Item.α i ++ Item.β i) (Item.χ i)
  in-all₁ {j}        ((Y ∘ k ↦ α ∘ β) {χ} {ω})      with eq-ℕ j k
  in-all₁ {.zero}    ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | yes refl = in-all₀ (Y ∘ zero ↦ α ∘ β)
  in-all₁ {.(suc k)} ((Y ∘ suc k ↦ α ∘ β) {χ} {ω})  | yes refl = in-∷∷-l (in-all₀ (Y ∘ suc k ↦ α ∘ β))
  in-all₁ {zero}     ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | no x = void (x refl)
  in-all₁ {zero}     ((Y ∘ suc k ↦ α ∘ β) {χ} {()}) | no x 
  in-all₁ {suc j}    ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | no x = in-∷∷-r
    {as = all-rules₀ Y (suc j) ε (α ++ β) χ (≤ₛ (≤-self j))}
    (in-fmap promote {_} {(Y ∘ zero ↦ α ∘ β) {χ} {≤₀}} (in-all₁ (Y ∘ zero ↦ α ∘ β)))
  in-all₁ {suc j}    ((Y ∘ suc k ↦ α ∘ β) {χ} {ω})  | no x = in-∷∷-r
    {as = all-rules₀ Y (suc j) ε (α ++ β) χ (≤ₛ (≤-self j))}
    (in-fmap promote {_} {(Y ∘ (suc k) ↦ α ∘ β) {χ} {≤-≠ (suc-le ω) x}} (in-all₁ (Y ∘ (suc k) ↦ α ∘ β)))

  in-all₂ : ∀ {j} ->
    (i : Item j) ->
    (xs : (N × (N ∣ T) *) *) ->
    (q : xs ∋ (Item.Y i , Item.α i ++ Item.β i) ) -> 
    (f : ∀ {r} -> xs ∋ r -> CFG.rules G ∋ r) ->
      i isin all-rules₂ j xs f
  in-all₂ i ε () f
  in-all₂ i ((Y , β) ∷ xs) in-head f = in-∷∷-l (in-all₁ i)
  in-all₂ i ((Y , β) ∷ xs) (in-tail q) f = in-∷∷-r
    {as = all-rules₁ Y _ β _} (in-all₂ i xs q (f ∘ in-tail))

  relevant-χ : ∀ {j} -> (i : Item j) -> CFG.rules G ∋ (Item.Y i , Item.α i ++ Item.β i)
  relevant-χ ((Y ∘ j ↦ α ∘ β) {χ}) = elem' eq-rule (Y , α ++ β) (CFG.rules G) χ

  in-all : ∀ {j} -> (i : Item j) -> i isin all-rules j
  in-all i = in-all₂ i (CFG.rules G) (relevant-χ i) id

  data WSet : ℕ -> T * -> Set where
    start :
      (v : T *) ->
      (rs : Unique {zero}) ->
      WSet zero v
  
    step : {a : T} {v : T *} {n : ℕ} ->
      (w : WSet n (a ∷ v)) ->
      (rs : Unique {suc n}) ->
      WSet (suc n) v
  
  Sₙ : {v : T *} {n : ℕ} ->
    WSet n v ->
    Unique {n}
  Sₙ (start v rs) = rs
  Sₙ (step w rs) = rs
  
  --Sₛ : {v : T *} {n : ℕ} ->
  --  WSet n v ->
  --  Item n * *
  --Sₛ (start v rs) = rs ∷ ε
  --Sₛ (step w rs) = rs ∷ Sₛ w
  
  Wₙ : {v : T *} {n : ℕ} ->
    (w : WSet n v) ->
    (rs : Unique {n} ) ->
    WSet n v
  Wₙ (start v rs) rs₁ = start v rs₁
  Wₙ (step w rs) rs₁ = step w rs₁
  
  scanner-w₀ : ∀ {n} ->
    T ->
    Item n * ->
    Unique {suc n}
  scanner-w₀ a ε = empt
  scanner-w₀ a ((X ∘ j ↦ α ∘ ε) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ j ↦ α ∘ l Y ∷ β) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ j ↦ α ∘ r b ∷ β) {χ} {ω} ∷ rs) with decidₜ a b
  ... | yes refl = insert ((X ∘ j ↦ α ←∷ r a ∘ β) {v-step χ} {≤-suc ω}) (scanner-w₀ a rs)
  ... | no x = scanner-w₀ a rs
  
  scanner-w : {n : ℕ} ->
    (a : T) (v : T *) ->
    WSet n (a ∷ v) ->
    WSet (suc n) v
  scanner-w a v w = step w (scanner-w₀ a (as-list (Sₙ w)))
  
  lookup-? : ∀ {n} -> N -> Item n * -> ((a b : N) -> a ≡ b ??) -> Unique {n}
  lookup-? X ε eq = empt
  lookup-? X ((Y ∘ j ↦ α ∘ ε) ∷ rs) eq = lookup-? X rs eq
  lookup-? X ((Y ∘ j ↦ α ∘ r a ∷ β) ∷ rs) eq = lookup-? X rs eq
  lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) eq with eq X Z
  lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) eq | no x = lookup-? X rs eq
  lookup-? X ((Y ∘ j ↦ α ∘ l X ∷ β) {χ} {ω} ∷ rs) eq | yes refl =
    insert ((Y ∘ j ↦ α ←∷ l X ∘ β) {v-step χ} {ω}) (lookup-? X rs eq)
  
  complete-w₀ : {v : T *} {n : ℕ} ->
    (X : N) ->
    (j : ℕ) ->
    WSet n v ->
    Unique {n}
  complete-w₀ {n = n} X zero    w = lookup-? X (as-list (Sₙ w)) decidₙ
  complete-w₀ X (suc j) (start v rs) = empt
  complete-w₀ X (suc j) (step w rs) = fmap promote (complete-w₀ X j w)
  
  predict-w₀-f : (n : ℕ) -> (r : N × (N ∣ T) *) -> CFG.rules G ∋ r -> Item n
  predict-w₀-f n (Y , α) p = (Y ∘ n ↦ ε ∘ α) {p} {≤-self n}
  
  predict-w₀ : {v : T *} {n : ℕ} ->
    (X : N) ->
    WSet n v ->
    Unique {n}
  predict-w₀ {n = n} X w =
    let rs = CFG.rules G in
    let x₁ = lookup X rs eq-N in
    mapₚ (predict-w₀-f n) x₁ (lookup-sound₃ rs X _ eq-N)
  
--  pred-comp-w₀ : {n : ℕ} {v : T *} ->
--    (w : WSet n v) ->
--    (X : N) (j : ℕ) (β : (N ∣ T)*) ->
--    Item n *
--  pred-comp-w₀ w X j ε = complete-w₀ X j w
--  pred-comp-w₀ w X j (r a ∷ α) = ε
--  pred-comp-w₀ w X j (l Y ∷ α) = predict-w₀ Y w
--  
--  pred-++ : ∀ {A n} {m : ℕ -> A} (xs ys : A *) ->
--    (f : ∀ {j} -> xs ∋ m j -> j ≤ n) ->
--    (g : ∀ {j} -> ys ∋ m j -> j ≤ n) ->
--    (∀ {j} -> (xs ++ ys) ∋ m j -> j ≤ n)
--  pred-++ ε ys f g p = g p
--  pred-++ (x ∷ xs) ys f g in-head = f in-head
--  pred-++ (x ∷ xs) ys f g (in-tail p) = pred-++ xs ys (f ∘ in-tail) g p
--  
----  _\\_ : ∀ {n} -> (x x₁ : Item n *) → Item n *
----  _\\_ = list-diff eq-item
----
----  pred-\\ : ∀ {A n} {m : ℕ -> A} ->
----    (eq : (a b : A) -> a ≡ b ??) ->
----    (xs ys : A *) ->
----    (f : ∀ {j} -> xs ∋ m j -> j ≤ n) ->
----    (∀ {j} -> (list-diff eq xs ys) ∋ m j -> j ≤ n)
----  pred-\\ eq ε ys f ()
----  pred-\\ eq (x ∷ xs) ys f p with elem eq x ys
----  pred-\\ eq (x ∷ xs) ys f p | yes x₁ = pred-\\ eq xs ys (f ∘ in-tail) p
----  pred-\\ eq (x ∷ xs) ys f in-head | no x₁ = f in-head
----  pred-\\ eq (x ∷ xs) ys f (in-tail p) | no x₁ = pred-\\ eq xs (x ∷ ys) (f ∘ in-tail) p
----  
----  pred-comp-w₁ : {n : ℕ} {v : T *} ->
----    (m : ℕ) ->
----    (w : WSet n v) ->
----    (rs : Item n *) ->
----    Item n * × WSet n v
----  pred-comp-w₁ zero w rs = rs , w
----  pred-comp-w₁ (suc m) w ε = ε , w
----  pred-comp-w₁ (suc m) w (r₁ ∷ rs) =
----    let x₁ = pred-comp-w₀ w (Item.Y r₁) (Item.j r₁) (Item.β r₁) in
----    let x₂ = (x₁ \\ Sₙ w) \\ (r₁ ∷ rs) in
----    pred-comp-w₁ m (Wₙ w (r₁ ∷ Sₙ w)) (rs ++ x₂)
----
----  data Unique {T : Set} : T * -> Set where
----    u-ε : Unique ε
----    u-∷ : {a : T} {as : T *} -> Unique as -> (as ∋ a -> Void) -> Unique (a ∷ as)
----
----  eq-not : {T : Set} {rs ss : T *} {i : T} ->
----    Unique (rs ++ ss) -> rs ∋ i -> ss ∋ i -> Void
----  eq-not (u-∷ urs x) in-head q = x (in-r q)
----  eq-not (u-∷ urs x) (in-tail p) q = eq-not urs p q
----
----  unique-++ : ∀ {T} (as bs : T *) ->
----    Unique as ->
----    Unique bs ->
----    (∀ {b} -> bs ∋ b -> as ∋ b -> Void) ->
----    Unique (as ++ bs)
----  unique-++ ε bs ua ub f = ub
----  unique-++ (x ∷ as) bs (u-∷ ua x₁) ub f =
----    u-∷ (unique-++ as bs ua ub λ z → f z ∘ in-tail) (in-neither x₁ (λ x₂ → f x₂ in-head))
----
----  unique-++₂ : {T : Set} (as bs cs : T *) ->
----    Unique (as ++ cs) ->
----    Unique bs ->
----    (∀ {b} -> as ∋ b -> bs ∋ b -> Void) ->
----    (∀ {b} -> cs ∋ b -> bs ∋ b -> Void) ->
----    Unique ((as ++ bs) ++ cs)
----  unique-++₂ ε bs cs uac ub f g = unique-++ bs cs ub uac g
----  unique-++₂ (x ∷ as) bs cs (u-∷ uac x₁) ub f g = u-∷ (unique-++₂ as bs cs uac ub (f ∘ in-tail) g)
----    (in-neither {bs = cs} (in-neither (not-in-l x₁) (f in-head)) (not-in-r x₁))
----    
----  unique-++-∷ : {T : Set} {a : T} -> (as bs : T *) ->
----    Unique (as ++ bs) ->
----    ((as ++ bs) ∋ a -> Void) ->
----    Unique (as ++ (a ∷ bs))
----  unique-++-∷ ε bs uab f = u-∷ uab f
----  unique-++-∷ (x ∷ as) bs (u-∷ uab x₁) f = u-∷ (unique-++-∷ as bs uab (f ∘ in-tail))
----    (in-neither {bs = _ ∷ bs} (not-in-l x₁) λ { in-head → f in-head ; (in-tail x₂) → x₁ (in-r x₂)})
----
----  no-include-\\ : {n : ℕ} -> {x : Item n} (as bs : Item n *) ->
----    (as ∋ x -> Void) ->
----    (as \\ bs) ∋ x -> Void
----  no-include-\\ ε bs f p = f p
----  no-include-\\ (x₁ ∷ as) bs f p                   with elem eq-item x₁ bs
----  no-include-\\ (x₁ ∷ as) bs f p                   | yes x₂ = no-include-\\ as bs (f ∘ in-tail) p
----  no-include-\\ (x₁ ∷ as) bs f in-head             | no x₂ = f in-head
----  no-include-\\ {n} {x} (x₁ ∷ as) bs f (in-tail p) | no x₂ = no-include-\\ as (x₁ ∷ bs) (f ∘ in-tail) p
----
----  no-include-\\₂ : {n : ℕ} -> {x : Item n} (as bs : Item n *) ->
----    bs ∋ x ->
----    (as \\ bs) ∋ x -> Void
----  no-include-\\₂ ε bs p ()
----  no-include-\\₂ (x₁ ∷ as) bs p q           with elem eq-item x₁ bs
----  no-include-\\₂ (x₁ ∷ as) bs p q           | yes x₂ = no-include-\\₂ as bs p q
----  no-include-\\₂ (x₁ ∷ as) bs p in-head     | no x₂ = void (x₂ p)
----  no-include-\\₂ (x₁ ∷ as) bs p (in-tail q) | no x₂ = no-include-\\₂ as (x₁ ∷ bs) (in-tail p) q
----
----  unique-\\ : {n : ℕ} -> (as bs : Item n *) ->
----    Unique as ->
----    Unique (as \\ bs)
----  unique-\\ ε bs ua = ua
----  unique-\\ (x ∷ as) bs (u-∷ ua f) with elem eq-item x bs
----  unique-\\ (x ∷ as) bs (u-∷ ua f) | yes x₁ = unique-\\ as bs ua
----  unique-\\ (x ∷ as) bs (u-∷ ua f) | no x₁ = u-∷ (unique-\\ as (x ∷ bs) ua) (no-include-\\ as (x ∷ bs) f)
----  
----  tmp : {T : Set} {a : T} (as bs cs : T *) ->
----    Unique ((a ∷ as) ++ cs) ->
----    Unique (a ∷ bs) ->
----    (∀ {b} -> as ∋ b -> bs ∋ b -> Void) ->
----    (∀ {b} -> cs ∋ b -> bs ∋ b -> Void) ->
----    Unique ((as ++ bs) ++ (a ∷ cs))
----  tmp as bs cs (u-∷ uac x) (u-∷ ub x₃) f g =
----    let x₁ = unique-++₂ as bs cs uac ub f g in
----    unique-++-∷ (as ++ bs) cs x₁ (in-neither {bs = cs} (in-neither (not-in-l x) x₃) (not-in-r x))
----
----  pred-comp-w₂ : {n : ℕ} {v : T *} ->
----    (w : WSet n v) ->
----    (ss : Item n *) ->
----    (rs : Item n *) ->
----    (m : ℕ) ->
----    (p : m ≡ suc (length (all-rules n \\ ss))) -> 
----    Unique (rs ++ ss) ->
----    Item n * × WSet n v
----  pred-comp-w₂ w ss rs zero () q
----  pred-comp-w₂ w ss ε (suc m) p q = ε , w
----  pred-comp-w₂ w ss (r₁ ∷ rs) (suc m) p q =
----    let x₁ = pred-comp-w₀ (Wₙ w ss) (Item.Y r₁) (Item.j r₁) (Item.β r₁) in
----    let x₂ = x₁ \\ (r₁ ∷ (ss ++ rs)) in
----    let p₁ = trans (unsuc p) (sym (diff-suc eq-item (in-all _) (eq-not q in-head))) in
----    pred-comp-w₂ w (r₁ ∷ ss) (rs ++ x₂) m p₁ (tmp rs x₂ ss q (u-∷ (unique-\\ x₁ (r₁ ∷ (ss ++ rs)) {!!}) (no-include-\\₂ x₁ _ in-head)) (λ x → no-include-\\₂ x₁ _ (in-tail (in-r x))) (λ x → no-include-\\₂ x₁ _ (in-tail (in-l x))))
----
----  pred-comp-w : ∀ {n v} ->
----    WSet n v ->
----    WSet n v
----  pred-comp-w {n} w = snd (pred-comp-w₂ (Wₙ w ε) ε (Sₙ w) m (app suc {!!}) {!!})
----    where
----      m = suc (length (all-rules n))
----  
----  step-w : ∀ {n a v} ->
----    WSet n (a ∷ v) ->
----    WSet (suc n) v
----  step-w {a = a} {v = v} w = scanner-w a v (pred-comp-w w)
----  
----  parse : ∀ {n v} ->
----     WSet n v ->
----     WSet (length v + n) ε
----  parse {v = ε} w = pred-comp-w w
----  parse {n = n} {v = x ∷ v} w = f +ₛ (parse (step-w w))
----    where
----      f : ∀ {v j k} -> j ≡ k -> WSet j v -> WSet k v
----      f refl w = w
----  
----  --Ss = Sₛ
----  
----  --test : WSet G₀ zero t
----  --test = start (s₀ ∷ a₀ ∷ s₀ ∷ ε) ((S₀ ∘ zero ↦ ε ∘ l S₀ ∷ ε) ∷ ε)
----  --
----  --test1 : _
----  --test1 = step-w G₀ test
----  --
----  --test2 : _
----  --test2 = step-w G₀ test1
----  --
----  --test3 : _
----  --test3 = step-w G₀ test2
----  --
----  --testn : _
----  --testn = parse G₀ test
----  --
----  --pcw0 : _
----  --pcw0 = pred-comp-w₀
