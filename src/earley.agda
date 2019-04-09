open import base
open import accessible

module earley (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

open import grammar N T

module parser (G : CFG) where

  data Unique {T : Set} : T * -> Set where
    u-ε : Unique ε
    u-∷ : {a : T} {as : T *} -> Unique as -> (as ∋ a -> Void) -> Unique (a ∷ as)

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
    Item n *
  all-rules₀ X j α ε p q = (X ∘ j ↦ α ∘ ε) {p} {q} ∷ ε
  all-rules₀ X j α (x ∷ β) p q =
    (X ∘ j ↦ α ∘ x ∷ β) {p} {q} ∷
    all-rules₀ X j (α ←∷ x) β (in₂ (λ q → CFG.rules G ∋ (X , q)) (in₀ x α β) p) q
  
  all-rules₁ :
    (X : N) (j : ℕ) (β : (N ∣ T) *) ->
    .(CFG.rules G ∋ (X , β)) ->
    Item j *
  all-rules₁ X zero β p = all-rules₀ X zero ε β p ≤₀
  all-rules₁ X (suc j) β p = all-rules₀ X (suc j) ε β p (≤-self _) ++ map promote (all-rules₁ X j β p)

  all-rules₂ : (j : ℕ) -> (rs : (N × (N ∣ T)*)*) -> (∀ {r} -> rs ∋ r -> CFG.rules G ∋ r) -> Item j *
  all-rules₂ j ε f = ε
  all-rules₂ j ((X , β) ∷ rs) f = all-rules₁ X j β (f in-head) ++ all-rules₂ j rs (f ∘ in-tail)
  
  all-rules : (j : ℕ) -> Item j *
  all-rules j = all-rules₂ j (CFG.rules G) id

  in-all₀₀ : ∀ {j} ->
    (i : Item j) ->
      all-rules₀ (Item.Y i) (Item.j i) (Item.α i) (Item.β i) (Item.χ i) (Item.ω i) ∋ i
  in-all₀₀ (Y ∘ j ↦ α ∘ ε) = in-head
  in-all₀₀ (Y ∘ j ↦ α ∘ x ∷ β) = in-head

  in-all₀₁ : ∀ {γ η j} ->
    (i : Item j) ->
    .{χ : _} ->
    (p : Item.α i ≡ γ ++ η) ->
      all-rules₀ (Item.Y i) (Item.j i) γ (η ++ Item.β i) χ (Item.ω i) ∋ i
  in-all₀₁ {γ} {ε} ((Y ∘ j ↦ .(γ ++ ε) ∘ β) {χ} {ω}) {χ₂} refl =
    let x₁ = in₂ (λ μ -> ∀ .{χ} -> all-rules₀ Y j γ β χ₂ ω ∋ (Y ∘ j ↦ μ ∘ β) {χ} {ω}) (sym (++-ε γ)) in
    let x₂ = in₂ (λ χ -> CFG.rules G ∋ (Y , (χ ++ β))) (++-ε γ) in
    x₁ (in-all₀₀ ((Y ∘ j ↦ γ ∘ β)) ) {χ}
  in-all₀₁ {γ} {x ∷ η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀} {ω}) {χ} p =
    let x₁ = trans p (sym (in₀ x γ η)) in
    let x₂ = in-all₀₁ {γ ←∷ x} {η} {j₁} ((Y ∘ j ↦ α ∘ β) {χ₀} {ω}) {in₂ (λ x₂ → CFG.rules G ∋ (Y , x₂)) (in₀ x γ (η ++ β)) χ} x₁ in
    in-tail x₂

  in-all₀ : ∀ {j} ->
    (i : Item j) ->
      all-rules₀ (Item.Y i) (Item.j i) ε (Item.α i ++ Item.β i) (Item.χ i) (Item.ω i) ∋ i
  in-all₀ i = in-all₀₁ i {Item.χ i} refl

  in-all₁ : ∀ {j} ->
    (i : Item j) ->
      all-rules₁ (Item.Y i) j (Item.α i ++ Item.β i) (Item.χ i) ∋ i
  in-all₁ {j}        ((Y ∘ k ↦ α ∘ β) {χ} {ω})      with eq-ℕ j k
  in-all₁ {.zero}    ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | yes refl = in-all₀ (Y ∘ zero ↦ α ∘ β)
  in-all₁ {.(suc k)} ((Y ∘ suc k ↦ α ∘ β) {χ} {ω})  | yes refl = in-l (in-all₀ (Y ∘ suc k ↦ α ∘ β))
  in-all₁ {zero}     ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | no x = void (x refl)
  in-all₁ {zero}     ((Y ∘ suc k ↦ α ∘ β) {χ} {()}) | no x 
  in-all₁ {suc j}    ((Y ∘ zero ↦ α ∘ β) {χ} {ω})   | no x = in-r (in-map promote {_} {Y ∘ zero ↦ α ∘ β} (in-all₁ ((Y ∘ zero ↦ α ∘ β) {χ} {≤₀})))
  in-all₁ {suc j}    ((Y ∘ suc k ↦ α ∘ β) {χ} {ω})  | no x = in-r (in-map promote {_} {(Y ∘ (suc k) ↦ α ∘ β) {χ} {≤-≠ (suc-le ω) x}} (in-all₁ (Y ∘ (suc k) ↦ α ∘ β)))

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

  data WSet : ℕ -> T * -> Set where
    start :
      (v : T *) ->
      (rs : Item zero * ) ->
      WSet zero v
  
    step : {a : T} {v : T *} {n : ℕ} ->
      (w : WSet n (a ∷ v)) ->
      (rs : Item (suc n) * ) ->
      WSet (suc n) v
  
  Sₙ : {v : T *} {n : ℕ} ->
    WSet n v ->
    Item n *
  Sₙ (start v rs) = rs
  Sₙ (step w rs) = rs
  
  --Sₛ : {v : T *} {n : ℕ} ->
  --  WSet n v ->
  --  Item n * *
  --Sₛ (start v rs) = rs ∷ ε
  --Sₛ (step w rs) = rs ∷ Sₛ w
  
  Wₙ : {v : T *} {n : ℕ} ->
    (w : WSet n v) ->
    (rs : Item n * ) ->
    WSet n v
  Wₙ (start v rs) rs₁ = start v rs₁
  Wₙ (step w rs) rs₁ = step w rs₁
  
  scanner-w₀ : ∀ {n} ->
    T ->
    Item n * ->
    Item (suc n) *
  scanner-w₀ a ε = ε
  scanner-w₀ a ((X ∘ j ↦ α ∘ ε) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ j ↦ α ∘ l Y ∷ β) ∷ rs) = scanner-w₀ a rs
  scanner-w₀ a ((X ∘ j ↦ α ∘ r b ∷ β) {χ} {ω} ∷ rs) with decidₜ a b
  ... | yes refl = (X ∘ j ↦ α ←∷ r a ∘ β) {v-step χ} {≤-suc ω} ∷ (scanner-w₀ a rs)
  ... | no x = scanner-w₀ a rs
  
  scanner-w : {n : ℕ} ->
    (a : T) (v : T *) ->
    WSet n (a ∷ v) ->
    WSet (suc n) v
  scanner-w a v w = step w (scanner-w₀ a (Sₙ w))
  
  lookup-? : ∀ {n} -> N -> Item n * -> Item n *
  lookup-? X ε = ε
  lookup-? X ((Y ∘ j ↦ α ∘ ε) ∷ rs) = lookup-? X rs
  lookup-? X ((Y ∘ j ↦ α ∘ r a ∷ β) ∷ rs) = lookup-? X rs
  lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) with decidₙ X Z
  lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) | no x = lookup-? X rs
  lookup-? X ((Y ∘ j ↦ α ∘ l X ∷ β) {χ} {ω} ∷ rs) | yes refl =
    (Y ∘ j ↦ α ←∷ l X ∘ β) {v-step χ} {ω} ∷ lookup-? X rs

  complete-w₀ : {v : T *} {n : ℕ} ->
    (X : N) ->
    (j : ℕ) ->
    WSet n v ->
    Item n *
  complete-w₀ X zero    w = lookup-? X (Sₙ w)
  complete-w₀ X (suc j) (start v rs) = ε
  complete-w₀ X (suc j) (step w rs) = map promote (complete-w₀ X j w)
  
  predict-w₀-f : (n : ℕ) -> (r : N × (N ∣ T) *) -> CFG.rules G ∋ r -> Item n
  predict-w₀-f n (Y , α) p = (Y ∘ n ↦ ε ∘ α) {p} {≤-self n}
  
  predict-w₀ : {v : T *} {n : ℕ} ->
    (X : N) ->
    WSet n v ->
    Item n *
  predict-w₀ {n = n} X w =
    let rs = CFG.rules G in
    let x₁ = lookup X rs eq-N in
    mapₚ (predict-w₀-f n) x₁ (lookup-sound₃ rs X _ eq-N)
  
  deduplicate : {n : ℕ} -> Item n * -> Σ {Item n *} λ as -> Unique as
  deduplicate ε = σ ε u-ε
  deduplicate (x ∷ as) with deduplicate as
  deduplicate (x ∷ as) | σ p₁ p₀ with elem eq-item x p₁
  deduplicate (x ∷ as) | σ p₁ p₀ | yes x₁ = σ p₁ p₀
  deduplicate (x ∷ as) | σ p₁ p₀ | no x₁ = σ (x ∷ p₁) (u-∷ p₀ x₁)
  
  pred-comp-w₀ : {n : ℕ} {v : T *} ->
    (w : WSet n v) ->
    (X : N) (j : ℕ) (β : (N ∣ T)*) ->
    Σ {Item n *} λ as -> Unique as
  pred-comp-w₀ w X j ε = deduplicate (complete-w₀ X j w)
  pred-comp-w₀ w X j (r a ∷ α) = σ ε u-ε
  pred-comp-w₀ w X j (l Y ∷ α) = deduplicate (predict-w₀ Y w)

  pred-++ : ∀ {A n} {m : ℕ -> A} (xs ys : A *) ->
    (f : ∀ {j} -> xs ∋ m j -> j ≤ n) ->
    (g : ∀ {j} -> ys ∋ m j -> j ≤ n) ->
    (∀ {j} -> (xs ++ ys) ∋ m j -> j ≤ n)
  pred-++ ε ys f g p = g p
  pred-++ (x ∷ xs) ys f g in-head = f in-head
  pred-++ (x ∷ xs) ys f g (in-tail p) = pred-++ xs ys (f ∘ in-tail) g p
  
  _\\_ : ∀ {n} -> (x x₁ : Item n *) → Item n *
  _\\_ = list-diff eq-item

  pred-\\ : ∀ {A n} {m : ℕ -> A} ->
    (eq : (a b : A) -> a ≡ b ??) ->
    (xs ys : A *) ->
    (f : ∀ {j} -> xs ∋ m j -> j ≤ n) ->
    (∀ {j} -> (list-diff eq xs ys) ∋ m j -> j ≤ n)
  pred-\\ eq ε ys f ()
  pred-\\ eq (x ∷ xs) ys f p with elem eq x ys
  pred-\\ eq (x ∷ xs) ys f p | yes x₁ = pred-\\ eq xs ys (f ∘ in-tail) p
  pred-\\ eq (x ∷ xs) ys f in-head | no x₁ = f in-head
  pred-\\ eq (x ∷ xs) ys f (in-tail p) | no x₁ = pred-\\ eq xs (x ∷ ys) (f ∘ in-tail) p
  
  eq-not : {T : Set} {rs ss : T *} {i : T} ->
    Unique (rs ++ ss) -> rs ∋ i -> ss ∋ i -> Void
  eq-not (u-∷ urs x) in-head q = x (in-r q)
  eq-not (u-∷ urs x) (in-tail p) q = eq-not urs p q

  unique-++ : ∀ {T} (as bs : T *) ->
    Unique as ->
    Unique bs ->
    (∀ {b} -> bs ∋ b -> as ∋ b -> Void) ->
    Unique (as ++ bs)
  unique-++ ε bs ua ub f = ub
  unique-++ (x ∷ as) bs (u-∷ ua x₁) ub f =
    u-∷ (unique-++ as bs ua ub λ z → f z ∘ in-tail) (in-neither x₁ (λ x₂ → f x₂ in-head))

  unique-++₂ : {T : Set} (as bs cs : T *) ->
    Unique (as ++ cs) ->
    Unique bs ->
    (∀ {b} -> as ∋ b -> bs ∋ b -> Void) ->
    (∀ {b} -> cs ∋ b -> bs ∋ b -> Void) ->
    Unique ((as ++ bs) ++ cs)
  unique-++₂ ε bs cs uac ub f g = unique-++ bs cs ub uac g
  unique-++₂ (x ∷ as) bs cs (u-∷ uac x₁) ub f g = u-∷ (unique-++₂ as bs cs uac ub (f ∘ in-tail) g)
    (in-neither {bs = cs} (in-neither (not-in-l x₁) (f in-head)) (not-in-r x₁))
    
  unique-++-∷ : {T : Set} {a : T} -> (as bs : T *) ->
    Unique (as ++ bs) ->
    ((as ++ bs) ∋ a -> Void) ->
    Unique (as ++ (a ∷ bs))
  unique-++-∷ ε bs uab f = u-∷ uab f
  unique-++-∷ (x ∷ as) bs (u-∷ uab x₁) f = u-∷ (unique-++-∷ as bs uab (f ∘ in-tail))
    (in-neither {bs = _ ∷ bs} (not-in-l x₁) λ { in-head → f in-head ; (in-tail x₂) → x₁ (in-r x₂)})

  no-include-\\ : {n : ℕ} -> {x : Item n} (as bs : Item n *) ->
    (as ∋ x -> Void) ->
    (as \\ bs) ∋ x -> Void
  no-include-\\ ε bs f p = f p
  no-include-\\ (x₁ ∷ as) bs f p                   with elem eq-item x₁ bs
  no-include-\\ (x₁ ∷ as) bs f p                   | yes x₂ = no-include-\\ as bs (f ∘ in-tail) p
  no-include-\\ (x₁ ∷ as) bs f in-head             | no x₂ = f in-head
  no-include-\\ {n} {x} (x₁ ∷ as) bs f (in-tail p) | no x₂ = no-include-\\ as (x₁ ∷ bs) (f ∘ in-tail) p

  no-include-\\₂ : {n : ℕ} -> {x : Item n} (as bs : Item n *) ->
    bs ∋ x ->
    (as \\ bs) ∋ x -> Void
  no-include-\\₂ ε bs p ()
  no-include-\\₂ (x₁ ∷ as) bs p q           with elem eq-item x₁ bs
  no-include-\\₂ (x₁ ∷ as) bs p q           | yes x₂ = no-include-\\₂ as bs p q
  no-include-\\₂ (x₁ ∷ as) bs p in-head     | no x₂ = void (x₂ p)
  no-include-\\₂ (x₁ ∷ as) bs p (in-tail q) | no x₂ = no-include-\\₂ as (x₁ ∷ bs) (in-tail p) q

  unique-\\ : {n : ℕ} -> (as bs : Item n *) ->
    Unique as ->
    Unique (as \\ bs)
  unique-\\ ε bs ua = ua
  unique-\\ (x ∷ as) bs (u-∷ ua f) with elem eq-item x bs
  unique-\\ (x ∷ as) bs (u-∷ ua f) | yes x₁ = unique-\\ as bs ua
  unique-\\ (x ∷ as) bs (u-∷ ua f) | no x₁ = u-∷ (unique-\\ as (x ∷ bs) ua) (no-include-\\ as (x ∷ bs) f)
  
  tmp : {T : Set} {a : T} (as bs cs : T *) ->
    Unique ((a ∷ as) ++ cs) ->
    Unique (a ∷ bs) ->
    (∀ {b} -> as ∋ b -> bs ∋ b -> Void) ->
    (∀ {b} -> cs ∋ b -> bs ∋ b -> Void) ->
    Unique ((as ++ bs) ++ (a ∷ cs))
  tmp as bs cs (u-∷ uac x) (u-∷ ub x₃) f g =
    let x₁ = unique-++₂ as bs cs uac ub f g in
    unique-++-∷ (as ++ bs) cs x₁ (in-neither {bs = cs} (in-neither (not-in-l x) x₃) (not-in-r x))

  pred-comp-w₂ : {n : ℕ} {v : T *} ->
    (w : WSet n v) ->
    (ss : Item n *) ->
    (rs : Item n *) ->
    (m : ℕ) ->
    (p : m ≡ suc (length (all-rules n \\ ss))) -> 
    Unique (rs ++ ss) ->
    Item n * × WSet n v
  pred-comp-w₂ w ss rs zero () q
  pred-comp-w₂ w ss ε (suc m) p q = ε , w
  pred-comp-w₂ {n} {v} w ss (r₁ ∷ rs) (suc m) p q =
    let x₁ = pred-comp-w₀ (Wₙ w ss) (Item.Y r₁) (Item.j r₁) (Item.β r₁) in
    let x₂ = Σ.proj₁ x₁ \\ (r₁ ∷ (ss ++ rs)) in
    let p₁ = trans (unsuc p) (sym (diff-suc eq-item (in-all _) (eq-not q in-head))) in
    let p₂ = (unique-\\ (Σ.proj₁ x₁) (r₁ ∷ (ss ++ rs)) (Σ.proj₀ x₁)) in
    let p₃ = (u-∷ p₂ (no-include-\\₂ (Σ.proj₁ x₁) _ in-head)) in
    let p₄ = (tmp rs x₂ ss q p₃ (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-r x))) (λ x → no-include-\\₂ (Σ.proj₁ x₁) _ (in-tail (in-l x)))) in
    pred-comp-w₂ w (r₁ ∷ ss) (rs ++ x₂) m p₁ p₄

  pred-comp-w : ∀ {n v} ->
    WSet n v ->
    WSet n v
  pred-comp-w {n} w =
    let x₁ = deduplicate (Sₙ w) in
    let x₂ = (unique-++ (Σ.proj₁ x₁) ε (Σ.proj₀ x₁) u-ε λ ()) in
    snd (pred-comp-w₂ (Wₙ w ε) ε (Σ.proj₁ x₁) m (app suc refl) x₂)
    where
      m = suc (length (all-rules n \\ ε))
  
  step-w : ∀ {n a v} ->
    WSet n (a ∷ v) ->
    WSet (suc n) v
  step-w {a = a} {v = v} w = scanner-w a v (pred-comp-w w)
  
  parse : ∀ {n v} ->
     WSet n v ->
     WSet (length v + n) ε
  parse {v = ε} w = pred-comp-w w
  parse {n = n} {v = x ∷ v} w = f +ₛ (parse (step-w w))
    where
      f : ∀ {v j k} -> j ≡ k -> WSet j v -> WSet k v
      f refl w = w

  sound-scanner-w₀ : ∀ {a v u n} (rs : Item n *) ->
    (∀ {i} -> rs ∋ i -> G ⊢ u / a ∷ v ⟶* Item.Y i / Item.β i) ->
    (∀ {i} -> scanner-w₀ a rs ∋ i -> G ⊢ u / v ⟶* Item.Y i / Item.β i)
  sound-scanner-w₀ {a} ε f ()
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ ε) {χ} {ω} ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ l x ∷ β) ∷ rs) f p = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ r x ∷ β) ∷ rs) f p           with decidₜ a x
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ r a ∷ β) ∷ rs) f  in-head    | yes refl = let x₁ = f in-head in scanner x₁
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ r a ∷ β) ∷ rs) f (in-tail p) | yes refl = sound-scanner-w₀ rs (f ∘ in-tail) p
  sound-scanner-w₀ {a} ((Y ∘ j ↦ α ∘ r x ∷ β) ∷ rs) f p | no x₁ = sound-scanner-w₀ rs (f ∘ in-tail) p

  sound-scanner-w : ∀ {a v u n} (w : WSet n (a ∷ v)) ->
    (∀ {i} -> Sₙ w ∋ i -> G ⊢ u / a ∷ v ⟶* Item.Y i / Item.β i) ->
    (∀ {i} -> Sₙ (scanner-w a v w) ∋ i -> G ⊢ u / v ⟶* Item.Y i / Item.β i)
  sound-scanner-w w f p = sound-scanner-w₀ (Sₙ w) f p

  sound-lookup-? : ∀ {v u w n} -> ∀ X -> (rs : Item n *) ->
    G ⊢ v / w ⟶* X / ε ->
    (∀ {i} -> rs ∋ i -> G ⊢ u / v ⟶* Item.Y i / Item.β i) ->
    (∀ {i} -> lookup-? X rs ∋ i -> G ⊢ u / w ⟶* Item.Y i / Item.β i)
  sound-lookup-? X ε g f ()
  sound-lookup-? X ((Y ∘ j ↦ α ∘ ε) ∷ rs) g f p = sound-lookup-? X rs g (f ∘ in-tail) p
  sound-lookup-? X ((Y ∘ j ↦ α ∘ r x ∷ β) ∷ rs) g f p = sound-lookup-? X rs g (f ∘ in-tail) p
  sound-lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) g f p           with decidₙ X Z
  sound-lookup-? X ((Y ∘ j ↦ α ∘ l Z ∷ β) ∷ rs) g f p           | no x = sound-lookup-? X rs g (f ∘ in-tail) p
  sound-lookup-? X ((Y ∘ j ↦ α ∘ l X ∷ β) ∷ rs) g f in-head     | yes refl = let x₁ = f in-head in complet x₁ g
  sound-lookup-? X ((Y ∘ j ↦ α ∘ l X ∷ β) ∷ rs) g f (in-tail p) | yes refl = sound-lookup-? X rs g (f ∘ in-tail) p

  sound-complete-w₀ : ∀ {v u w n} -> ∀ X j -> (ω : WSet n v) ->
    G ⊢ v / w ⟶* X / ε ->
    (∀ {i} -> Sₙ ω ∋ i -> G ⊢ u / v ⟶* Item.Y i / Item.β i) ->
    (∀ {i} -> complete-w₀ X j ω ∋ i -> G ⊢ u / w ⟶* Item.Y i / Item.β i)
  sound-complete-w₀ X zero ω g f p = sound-lookup-? X (Sₙ ω) g f p
  sound-complete-w₀ X (suc j) (start v rs) g f ()
  sound-complete-w₀ X (suc j) (step ω rs) g f p = let x₁ = sound-complete-w₀ X j ω {!!} {!!} {!!} in {!in-map!}

--  sound-complete-w₀ : ∀ {v u n} (w : WSet n v) ->
--    (∀ 
    
--  Ss = Sₛ
--  
--  test : WSet G₀ zero t
--  test = start (s₀ ∷ a₀ ∷ s₀ ∷ ε) ((S₀ ∘ zero ↦ ε ∘ l S₀ ∷ ε) ∷ ε)
--  
--  test1 : _
--  test1 = step-w G₀ test
--  
--  test2 : _
--  test2 = step-w G₀ test1
--  
--  test3 : _
--  test3 = step-w G₀ test2
--  
--  testn : _
--  testn = parse G₀ test
--  
--  pcw0 : _
--  pcw0 = pred-comp-w₀
