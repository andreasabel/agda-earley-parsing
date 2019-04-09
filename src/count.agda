open import base

module count (N T : Set) (decidₙ : Dec N) (decidₜ : Dec T) where

  open import grammar N T
  
  count : ((a b : N) -> a ≡ b ??) -> (N × (N ∣ T)* )* -> N * -> ℕ
  count eq ε v = zero
  count eq ((X , α) ∷ rs) v with elem eq X v
  count eq ((X , α) ∷ rs) v | yes x = count eq rs v
  count eq ((X , α) ∷ rs) v | no x = suc (count eq rs (X ∷ v))
  
  count-G : (G : CFG) -> ℕ
  count-G G = count decidₙ (CFG.rules G) ε
  
  --count-law-1-i : {N T : Set}
  --  (v : N *) ->
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  ({Y : N} -> (p₁ p₂ : Y ∈ rs) -> p₁ ≡ p₂) ->
  --  ({Y : N} -> v ∋ Y -> Y ∈ rs -> Void) ->
  --  count eq rs v ≡ length rs
  --count-law-1-i     v eq ε f g = refl
  --count-law-1-i     v eq ((X , α) ∷ rs) f g with elem eq X v
  --count-law-1-i     v eq ((X , α) ∷ rs) f g | yes x with g x in-head
  --count-law-1-i     v eq ((X , α) ∷ rs) f g | yes x | ()
  --count-law-1-i {N} v eq ((X , α) ∷ rs) f g | no x = app suc (count-law-1-i (X ∷ v) eq rs f' g')
  --  where
  --    f' : {Y : N} -> (p₁ p₂ : Y ∈ rs) -> p₁ ≡ p₂
  --    f' {Y} p₁ p₂ with eq X Y
  --    f' {Y} p₁ p₂ | yes refl with f (in-tail p₁) in-head
  --    f' {Y} p₁ p₂ | yes refl | ()
  --    f' {Y} p₁ p₂ | no x = let x₁ = f (in-tail p₁) (in-tail p₂) in
  --      app (λ { in-head → p₂ ; (in-tail p) → p}) x₁
  --
  --    g' : {Y : N} -> (X ∷ v) ∋ Y -> Y ∈ rs → Void
  --    g' {Y} p₁ p₂ with eq X Y
  --    g' {Y} p₁ p₂ | yes refl with f (in-tail p₂) in-head
  --    g' {Y} p₁ p₂ | yes refl | ()
  --    g' {Y} in-head p₂ | no x = x refl
  --    g' {Y} (in-tail p₁) p₂ | no x = g p₁ (in-tail p₂)
  --    
  --count-law₁ : {N T : Set}
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  ({Y : N} -> (p₁ p₂ : Y ∈ rs) -> p₁ ≡ p₂) ->
  --  count eq rs ε ≡ length rs
  --count-law₁ eq rs f = count-law-1-i ε eq rs f (λ {Y} ())
  
  --count-u₃ : {N T : Set} {X : N} {α : (N ∣ T)*} (v : N *) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  count eq ((X , α) ∷ rs) (X ∷ v) ≡ count eq ((X , α) ∷ rs) v ->
  --  (v ∋ X -> Void) ->
  --  X ∈ rs ->
  --  Void
  --count-u₃ {X = X} v rs eq p₁ p₂ p₃ with elem eq X v
  --count-u₃ {X = X} v rs eq p₁ p₂ p₃ | yes x = p₂ x
  --count-u₃ {X = X} v rs eq p₁ p₂ p₃ | no  x with elem eq X (X ∷ v)
  --count-u₃ {X = X} v rs eq p₁ p₂ p₃ | no  x | yes x₁ = oddsuc refl p₁
  --count-u₃ {X = X} v rs eq p₁ p₂ p₃ | no  x | no  x₁ = x₁ in-head
  
  ∋-comm : {T : Set} {a b c : T} {bs : T *} ->
    (a ∷ b ∷ bs) ∋ c -> (b ∷ a ∷ bs) ∋ c
  ∋-comm in-head = in-tail in-head
  ∋-comm (in-tail in-head) = in-head
  ∋-comm (in-tail (in-tail p₁)) = in-tail (in-tail p₁)
  
  --count-u₆ : {N T : Set} (u v : N *) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  ({a : N} -> u ∋ a -> v ∋ a) ->
  --  ({a : N} -> v ∋ a -> u ∋ a) ->
  --  count eq rs u ≡ count eq rs v
  --count-u₆ u v ε eq f g = refl
  --count-u₆ u v ((Z , α) ∷ rs) eq f g with elem eq Z u
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | yes x with elem eq Z v
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | yes x | yes x₁ = count-u₆ u v rs eq f g
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | yes x | no  x₁ with x₁ (f x)
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | yes x | no  x₁ | ()
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | no  x with elem eq Z v
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | no  x | yes x₁ with x (g x₁)
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | no  x | yes x₁ | ()
  --count-u₆ u v ((Z , α) ∷ rs) eq f g | no  x | no  x₁ = app suc (count-u₆ (Z ∷ u) (Z ∷ v) rs eq f' g')
  --  where
  --    f' : {a : _} -> (Z ∷ u) ∋ a -> (Z ∷ v) ∋ a
  --    f' in-head = in-head
  --    f' (in-tail p) = in-tail (f p)
  --
  --    g' : {a : _} -> (Z ∷ v) ∋ a -> (Z ∷ u) ∋ a
  --    g' in-head = in-head
  --    g' (in-tail p) = in-tail (g p)
  --
  --count-u₅ : {N T : Set} (X Y : N) (v : N *) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  count eq rs (Y ∷ X ∷ v) ≡ count eq rs (X ∷ Y ∷ v)
  --count-u₅ X Y v rs eq = count-u₆ (Y ∷ X ∷ v) (X ∷ Y ∷ v) rs eq f f
  --  where
  --    f : {a : _} {X Y : _} -> (Y ∷ X ∷ v) ∋ a -> (X ∷ Y ∷ v) ∋ a
  --    f in-head = in-tail in-head
  --    f (in-tail in-head) = in-head
  --    f (in-tail (in-tail p)) = in-tail (in-tail p)
  
  --count-u₄ : {N T : Set} {X : N} (v : N *) ->
  --  (rs : (N × (N ∣ T)* )*) ->
  --  (eq : (a b : N) -> a ≡ b ??) ->
  --  (X ∈ rs -> Void) ->
  --  count eq rs (X ∷ v) ≡ count eq rs v
  --count-u₄ {X = X} v ε eq p₁ = refl
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ with eq X Y
  --count-u₄ {X = Y} v ((Y , α) ∷ rs) eq p₁ | yes refl with p₁ in-head
  --count-u₄ {X = Y} v ((Y , α) ∷ rs) eq p₁ | yes refl | ()
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x with elem eq Y (X ∷ v)
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | yes x₁ with elem eq Y v
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | yes x₁           | yes x₂ = count-u₄ v rs eq (λ z → p₁ (in-tail z))
  --count-u₄ {X = Y} v ((Y , α) ∷ rs) eq p₁ | no x | yes in-head      | no x₂ with x refl
  --count-u₄ {X = Y} v ((Y , α) ∷ rs) eq p₁ | no x | yes in-head      | no x₂ | ()
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | yes (in-tail x₁) | no x₂ with x₂ x₁
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | yes (in-tail x₁) | no x₂ | ()
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | no  x₁ with elem eq Y v
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | no  x₁           | yes x₂ with x₁ (in-tail x₂)
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | no  x₁           | yes x₂ | ()
  --count-u₄ {X = X} v ((Y , α) ∷ rs) eq p₁ | no x | no  x₁           | no x₂ =
  --  let x₁ = count-u₄ (Y ∷ v) rs eq p' in
  --  let x₂ = count-u₅ X Y v rs eq in
  --  app suc (trans x₂ (sym x₁))
  --  where
  --    p' : (x₃ : X ∈ rs) → Void
  --    p' p = p₁ (in-tail p)
  
  lookup :
    N ->
    (N × (N ∣ T)*) * ->
    ((a b : N) -> a ≡ b ??) ->
      (N × (N ∣ T)* )* 
  lookup Y ε eq = ε
  lookup Y ((X , ss) ∷ as) eq with eq Y X
  lookup Y ((X , ss) ∷ as) eq | no x    = lookup Y as eq
  lookup Y ((Y , ss) ∷ as) eq | yes refl = (Y , ss) ∷ (lookup Y as eq)
  
  lookup' : (Y : N) (G : CFG) ->
    (N × (N ∣ T)* )* 
  lookup' Y G = lookup Y (CFG.rules G) decidₙ

  l₁ : {as : (N × (N ∣ T)* )*} {u : N × (N ∣ T)*} {Y : N} {α : (N ∣ T) *} ->
    (eq : (a b : N) -> (a ≡ b ??)) ->
    lookup Y as eq ∋ (Y , α) ->
      lookup Y (u ∷ as) eq ∋ (Y , α)
  l₁ {as = ε} eq ()
  l₁ {as =    (X , α) ∷ as} {Z , β} {Y} eq a with eq Y Z
  l₁ {(X , α) ∷ as} {Z , β} {Z} eq a | yes refl = in-tail a
  l₁ {(X , α) ∷ as} {Z , β} {Y} eq a | no x = a
  
  lookup-complete : {as : (N × (N ∣ T)* )*} {Y : N} {α : (N ∣ T)*} ->
    (eq : (a b : N) -> a ≡ b ?? ) ->
    as ∋ (Y , α) ->
      lookup Y as eq ∋ (Y , α)
  lookup-complete {Y = Y} eq in-head with eq Y Y
  lookup-complete {Y = Y} eq in-head | no p with p refl
  lookup-complete {Y = Y} eq in-head | no p | ()
  lookup-complete {Y = Y} eq in-head | yes refl = in-head
  lookup-complete {Y = Y} eq (in-tail {u = u} a) = let x₁ = lookup-complete eq a in l₁ {u = u} eq x₁
  
  lookup-sound : {as : (N × (N ∣ T)* )*} {Y : N} {α : (N ∣ T)*} ->
    (eq : (a b : N) -> a ≡ b ??) ->
    lookup Y as eq ∋ (Y , α) ->
      as ∋ (Y , α)
  lookup-sound {as = ε} eq ()
  lookup-sound {as =    (X , β) ∷ as} {Y} eq a               with eq Y X
  lookup-sound {(X , β) ∷ as} {Y} eq a               | no x = in-tail (lookup-sound eq a)
  lookup-sound {(X , β) ∷ as} {X} {β} eq in-head     | yes refl = in-head
  lookup-sound {(X , β) ∷ as} {X} {α} eq (in-tail a) | yes refl = in-tail (lookup-sound eq a)
  
  lookup-sound₂ : (as : _) (Y : _) (r : _) ->
    (eq : (a b : N) -> a ≡ b ??) ->
    lookup Y as eq ∋ r ->
      Σ λ α -> r ≡ (Y , α)
  lookup-sound₂ ε Y (X , α) eq ()
  lookup-sound₂ ((X , β) ∷ as) Y (Z , α) eq p           with eq Y X
  lookup-sound₂ ((X , β) ∷ as) Y (Z , α) eq p           | no x = lookup-sound₂ as Y (Z , α) eq p
  lookup-sound₂ ((Y , β) ∷ as) Y (Y , β) eq in-head     | yes refl = σ β refl
  lookup-sound₂ ((Y , β) ∷ as) Y (Z , α) eq (in-tail p) | yes refl = lookup-sound₂ as Y (Z , α) eq p
  
  lookup-sound₃ : (as : _) (Y : _) (r : _) ->
    (eq : (a b : N) -> a ≡ b ??) ->
    lookup Y as eq ∋ r ->
      as ∋ r
  lookup-sound₃ as Y r₀ eq p with lookup-sound₂ as Y r₀ eq p
  lookup-sound₃ as Y (Y , α) eq p | σ α refl = lookup-sound eq p
  
  lookup₃ : {α : (N ∣ T)*} ->
    (X Y : N) ->
    (as : (N × (N ∣ T)* )*) ->
    (eq : (a b : N) -> a ≡ b ??) ->
    lookup Y as eq ∋ (X , α) ->
      X ≡ Y
  lookup₃ X Y ε              eq ()
  lookup₃ X Y ((Z , β) ∷ as) eq p           with eq Y Z
  lookup₃ Y Y ((Y , β) ∷ as) eq in-head     | yes refl = refl
  lookup₃ X Y ((Y , β) ∷ as) eq (in-tail p) | yes refl = lookup₃ X Y as eq p
  lookup₃ X Y ((Z , β) ∷ as) eq p           | no x = lookup₃ X Y as eq p
