open import base

module grammar (N T : Set) where

record CFG : Set where
  constructor _!_!_!_!_
  field
    start : N
    rules : (N × (N ∣ T)* )*
    valid : (X : N) -> Σ λ α -> (X , α) ∈ rules

data _⊢_∈_ (G : CFG) :  T * -> (N ∣ T) * -> Set where
  empty :
    G ⊢ ε ∈ ε

  concat : {u v : T *} {A : N} {α : (N ∣ T) *} ->
    G ⊢ u ∈ l A ∷ ε -> G ⊢ v ∈ α -> G ⊢ u ++ v ∈ l A ∷ α

  term : {u : T *} {a : T} {α : (N ∣ T) *} ->
    G ⊢ u ∈ α -> G ⊢ a ∷ u ∈ r a ∷ α

  nonterm : {A : N} {α : (N ∣ T) *} {u : T *} ->
    CFG.rules G ∋ (A , α) -> G ⊢ u ∈ α -> G ⊢ u ∈ l A ∷ ε
infixr 10 _⊢_∈_

data _⊢_/_∈_ (G : CFG) : T * -> T * -> (N ∣ T)* -> Set where
  empt : {w : T *} ->
    G ⊢ w / w ∈ ε

  conc : {u v w : T *} {X : N} {α : (N ∣ T) *} ->
    G ⊢ u / v ∈ l X ∷ ε ->
    G ⊢ v / w ∈ α ->
      G ⊢ u / w ∈ l X ∷ α

  term : {a : T} {u v : T *} {α : (N ∣ T) *} ->
    G ⊢ u / v ∈ α ->
      G ⊢ a ∷ u / v ∈ r a ∷ α

  nont : {u v : T *} {X : N} {α : (N ∣ T) *} ->
    (X , α) ∈ CFG.rules G ->
    G ⊢ u / v ∈ α ->
    G ⊢ u / v ∈ l X ∷ ε

infixl 10 _⊢_/_∈_


s : ∀ {u v w α G} ->
  G ⊢ u / v ∈ α ->
  G ⊢ u ++ w / v ++ w ∈ α
s empt = empt
s (conc (conc a empt) a₁) = s (conc a a₁)
s (conc (nont x a) a₁) = conc (nont x (s a)) (s a₁)
s (term a) = term (s a)
s (nont x a) = nont x (s a)

sound₀ :  ∀ {G u α} ->
  G ⊢ u ∈ α ->
  G ⊢ u / ε ∈ α
sound₀ empty = empt
sound₀ (concat {v = v} a b) = conc (s (sound₀ a)) (sound₀ b)
sound₀ (term a) = term (sound₀ a)
sound₀ (nonterm x a) = nont x (sound₀ a)

suffix-first : ∀ {u v α} {G : CFG} ->
  G ⊢ u / v ∈ α ->
  v suffixOf u
suffix-first empt = suffix-id
suffix-first (conc a a₁) =
  let x₁ = suffix-first a₁ in
  let x₂ = suffix-first a in
  suffix-trans x₂ x₁
suffix-first (term a) = suffix-∷ (suffix-first a)
suffix-first (nont x a) = suffix-first a

c₃ : ∀ {a b α} {G : CFG} ->
  a ≡ b -> G ⊢ a ∈ α -> G ⊢ b ∈ α
c₃ refl b = b

c₂ : ∀ {u v α} {G : CFG} ->
  (g : G ⊢ u / v ∈ α) ->
  G ⊢ dropSuffix u v (suffix-first g) ∈ α
c₂ empt = empty 
c₂ (conc a a₁) =
  let x₁ = c₂ a₁ in
  let x₂ = c₂ a  in
  let x₃ = concat x₂ x₁ in
  c₃ (dropSuffix-++ (suffix-first a) (suffix-first a₁)) x₃
c₂ (term a) = term (c₂ a)
c₂ (nont x a) = nonterm x (c₂ a)

complete₀ : ∀ {u α} {G : CFG} ->
  G ⊢ u / ε ∈ α ->
  G ⊢ u ∈ α
complete₀ empt = empty
complete₀ (conc a a₁) =
  let x₁ = complete₀ a₁ in
  let x₂ = c₂ a in
  let x₃ = concat x₂ x₁ in
  c₃ (dropSuffix-++₂ (suffix-first a)) x₃
complete₀ (term a) = term (complete₀ a)
complete₀ (nont x a) = nonterm x (complete₀ a)

-- G ⊢ u / v ⟶* X / α

infixl 10 _⊢_/_⟶*_/_
data _⊢_/_⟶*_/_ (G : CFG) : T * -> T * -> N -> (N ∣ T) * -> Set where
  initial : {u : T *} ->
    G ⊢ u / u ⟶* CFG.start G / l (CFG.start G) ∷ ε

  scanner : {u v : T *} {a : T} {X : N} {β : (N ∣ T) *} ->
    G ⊢ u / a ∷ v ⟶* X / r a ∷ β ->
      G ⊢ u / v ⟶* X / β

  predict : {u v : T *} {X Y : N} {α β : (N ∣ T) *} -> 
    CFG.rules G ∋ (Y , α) ->
    G ⊢ u / v ⟶* X / l Y ∷ β ->
      G ⊢ v / v ⟶* Y / α

  complet : {u v w : T *} {X Y : N} {β : (N ∣ T) *} ->
    G ⊢ u / v ⟶* X / l Y ∷ β ->
    G ⊢ v / w ⟶* Y / ε ->
      G ⊢ u / w ⟶* X / β

sound : ∀ {u v w X β} {G : CFG} ->
  G ⊢ u / v ⟶* X / β ->
  G ⊢ v / w ∈ β ->
    G ⊢ u / w ∈ l X ∷ ε
sound initial b = b
sound (scanner a) b = sound a (term b)
sound (predict x a) b = nont x b
sound (complet a a₁) b =
  let x₁ = sound a₁ empt in
  let x₂ = conc x₁ b in
  sound a x₂

complete : ∀ {u v w X α} {G : CFG} ->
  G ⊢ u / v ⟶* X / α ->
  G ⊢ v / w ∈ α ->
    G ⊢ u / w ⟶* X / ε
complete a empt = a
complete a (conc (conc b empt) b₁) = complete a (conc b b₁)
complete a (conc (nont x b) b₁) =
  let x₁ = predict x a in
  let x₂ = complete x₁ b in
  let x₃ = complet a x₂ in
  complete x₃ b₁
complete a (term b) = complete (scanner a) b
complete a (nont x b) = complet a (complete (predict x a) b)

infixl 10 _⊢_/_⟶*_/_∙_
data _⊢_/_⟶*_/_∙_ (G : CFG) : T * -> T * -> N -> (N ∣ T) * -> (N ∣ T) * -> Set where
  initial : {u : T *} {α : (N ∣ T) *} ->
    CFG.rules G ∋ (CFG.start G , α) ->
    G ⊢ u / u ⟶* CFG.start G / ε ∙ α

  scanner : {u v : T *} {a : T} {X : N} {α β : (N ∣ T) *} ->
    G ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β ->
      G ⊢ u / v ⟶* X / α ←∷ r a ∙ β

  predict : {u v : T *} {X Y : N} {α β δ : (N ∣ T) *} -> 
    CFG.rules G ∋ (Y , δ) ->
    G ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
      G ⊢ v / v ⟶* Y / ε ∙ δ

  complet : {u v w : T *} {X Y : N} {α β γ : (N ∣ T) *} ->
    G ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
    G ⊢ v / w ⟶* Y / γ ∙ ε ->
      G ⊢ u / w ⟶* X / α ←∷ l Y ∙ β

data _⊢_&_∈_ (G : CFG) : T * -> T * -> (N ∣ T)* -> Set where
  empt : {w : T *} ->
    G ⊢ w & w ∈ ε

  conc : {u v w : T *} {X : N} {α β : (N ∣ T) *} ->
    (X , α) ∈ CFG.rules G ->
    G ⊢ u & v ∈ α ->
    G ⊢ v & w ∈ β ->
      G ⊢ u & w ∈ l X ∷ β

  term : {a : T} {u v : T *} {α : (N ∣ T) *} ->
    G ⊢ u & v ∈ α ->
      G ⊢ a ∷ u & v ∈ r a ∷ α

infixl 10 _⊢_&_∈_

in-g : ∀ {G u v X α β} ->
  G ⊢ u / v ⟶* X / α ∙ β ->
    CFG.rules G ∋ (X , α ++ β)
in-g (initial x) = x
in-g (scanner g) = in₂ (λ t -> (_ , t) ∈ _) (in₀ _ _ _) (in-g g)
in-g (predict x g) = x
in-g (complet g g₁) = in₂ (λ t -> (_ , t) ∈ _) (in₀ _ _ _) (in-g g)

sound₂ : ∀ {G u v w X α β} ->
  G ⊢ u / v ⟶* X / α ∙ β ->
    G ⊢ v & w ∈ β ->
    G ⊢ u & w ∈ α ++ β
sound₂ (initial x) b = b
sound₂ (scanner g) b = in₂ (λ t -> _ ⊢ _ & _ ∈ t) (in₀ _ _ _) (sound₂ g (term b))
sound₂ (predict x g) b = b
sound₂ (complet g g₁) b =
  let x₁ = in₂ (λ t -> _ ⊢ _ & _ ∈ t) (++-ε _) (sound₂ g₁ empt) in
  let x₂ = in₂ (λ t -> (_ , t) ∈ _) (++-ε _) (in-g g₁) in
  let x₃ = conc x₂ x₁ b in
  in₂ (λ t -> _ ⊢ _ & _ ∈ t) (in₀ _ _ _) (sound₂ g x₃)

complete₁ : ∀ {u v w X α β} {G : CFG} ->
  G ⊢ u / v ⟶* X / α ∙ β ->
  G ⊢ v & w ∈ β ->
    G ⊢ u / w ⟶* X / α ++ β ∙ ε
complete₁ a empt = in₂ (λ t -> _ ⊢ _ / _ ⟶* _ / t ∙ ε) (sym (++-ε _)) a
complete₁ a (conc x g g₁) =
  let x₁ = predict x a in
  let x₂ = complete₁ x₁ g in
  let x₃ = complet a x₂ in
  let x₄ = complete₁ x₃ g₁ in
  in₂ (λ t -> _ ⊢ _ / _ ⟶* _ / t ∙ _) (sym (in₀ _ _ _)) x₄
complete₁ a (term g) =
  let x₁ = complete₁ (scanner a) g in
  in₂ (λ t -> _ ⊢ _ / _ ⟶* _ / t ∙ _) (sym (in₀ _ _ _)) x₁

data _⊢_/_∙_⟶_/_∙_ (G : CFG) : T * -> T * -> N -> T * -> T * -> (N ∣ T)* -> Set where
  init : {t : T *} ->
    G ⊢ ε / t ∙ CFG.start G ⟶ ε / t ∙ (l (CFG.start G)) ∷ ε

  scan : {a : T} {s t u v : T *} {X : N} {β : (N ∣ T) *} ->
    G ⊢ s / t ∙ X ⟶ u / a ∷ v ∙ r a ∷ β ->
      G ⊢ s / t ∙ X ⟶ a ∷ u / v ∙ β

  pred : {s t u v : T *} {X Y : N} {α β : (N ∣ T) *} ->
    CFG.rules G ∋ (Y , α) ->
    G ⊢ s / t ∙ X ⟶ u / v ∙ l Y ∷ β ->
      G ⊢ u / v ∙ Y ⟶ u / v ∙ α

  comp : {s t u v w x : T *} {X Y : N} {β : (N ∣ T) *} ->
    G ⊢ s / t ∙ X ⟶ u / v ∙ l Y ∷ β ->
    G ⊢ u / v ∙ Y ⟶ w / x ∙ ε ->
      G ⊢ s / t ∙ X ⟶ w / x ∙ β

infixl 10 _⊢_/_∙_⟶_/_∙_

--equiv₁ : ∀ {s t u v X β} {G : CFG} ->
--  G ⊢ s / t ∙ X ⟶ u / v ∙ β ->
--    G ⊢ t / v ⟶* X / β
--equiv₁ init = initial
--equiv₁ (scan a) = scanner (equiv₁ a)
--equiv₁ (pred x a) = predict x (equiv₁ a)
--equiv₁ (comp a a₁) = complet (equiv₁ a) (equiv₁ a₁)

--equiv₂ : {G : CFG} {u v : T *} {X : N} {β : (N ∣ T) *} ->
--  G ⊢ u ∙ X ⟶ v ∙ β ->
--    Σ₂ λ s t -> G ⊢ s / u ∙ X ⟶ t / v ∙ β
--equiv₂ initial = σ₂ ε ε init
--equiv₂ (scanner a) with equiv₂ a
--equiv₂ (scanner a) | σ₂ p₁ p₂ p₀ = σ₂ p₁ (_ ∷ p₂) (scan p₀)
--equiv₂ (predict x a) with equiv₂ a
--equiv₂ (predict x a) | σ₂ p₁ p₂ p₀ = σ₂ p₂ p₂ (pred x p₀)
--equiv₂ (complet a a₁) with equiv₂ a
--equiv₂ (complet a a₁) | σ₂ p₁ p₂ p₀ with equiv₂ a₁
--equiv₂ (complet a a₁) | σ₂ p₁ p₂ p₀ | σ₂ q₁ q₂ q₀ = σ₂ {!!} {!!} (comp p₀ {!q₀!})
