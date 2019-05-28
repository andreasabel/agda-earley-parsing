open import base

module grammar (N T : Set) where

record CFG : Set where
  constructor _⟩_⟩_
  field
    start : N
    rules : (N × (N ∣ T)* )*
    valid : (X : N) -> Σ λ α -> (X , α) ∈ rules

infixr 10 _⊢_∈_
data _⊢_∈_ (G : CFG) :  T * -> (N ∣ T) * -> Set where
  empty :
    G ⊢ ε ∈ ε

  concat : {u v : T *} {A : N} {α : (N ∣ T) *} ->
    G ⊢ u ∈ l A ∷ ε -> G ⊢ v ∈ α -> G ⊢ u ++ v ∈ l A ∷ α

  term : {u : T *} {a : T} {α : (N ∣ T) *} ->
    G ⊢ u ∈ α -> G ⊢ a ∷ u ∈ r a ∷ α

  nonterm : {A : N} {α : (N ∣ T) *} {u : T *} ->
    CFG.rules G ∋ (A , α) -> G ⊢ u ∈ α -> G ⊢ u ∈ l A ∷ ε

infixl 10 _⊢_/_∈_
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

sound₀ :  ∀ {G u α} ->
  G ⊢ u ∈ α ->
  G ⊢ u / ε ∈ α
sound₀ empty = empt
sound₀ (term a) = term (sound₀ a)
sound₀ (nonterm x a) = nont x (sound₀ a)
sound₀ (concat {v = v} a b) = conc (s (sound₀ a)) (sound₀ b)
  where
    s : ∀ {u v w α G} ->
      G ⊢ u / v ∈ α ->
      G ⊢ u ++ w / v ++ w ∈ α
    s empt = empt
    s (conc (conc a empt) a₁) = s (conc a a₁)
    s (conc (nont x a) a₁) = conc (nont x (s a)) (s a₁)
    s (term a) = term (s a)
    s (nont x a) = nont x (s a)

complete₀ : ∀ {u v α G} ->
  G ⊢ u / v ∈ α ->
    Σ λ t -> (G ⊢ t ∈ α) × (t ++ v ≡ u)
complete₀ empt = σ ε (empty , refl)
complete₀ (term g) with complete₀ g
complete₀ (term g) | σ p₁ (x₀ , x₁) = σ (_ ∷ p₁) (term x₀ , (app (_ ∷_) x₁))
complete₀ (nont x g) with complete₀ g
complete₀ (nont x g) | σ p₁ (x₀ , x₁) = σ p₁ (nonterm x x₀ , x₁)
complete₀ (conc g g₁) with complete₀ g , complete₀ g₁
complete₀ (conc g g₁) | σ p₁ (x₀ , x₁) , σ q₁ (y₀ , y₁) =
  σ (p₁ ++ q₁) ((concat x₀ y₀) , p₁++q₁++v≡u)
  where
    p₁++q₁++v≡u = trans (trans (assoc-++ p₁ q₁ _) (sym (app (p₁ ++_) y₁))) (sym x₁)
  
infixl 10 _⊢_∥_∈_
data _⊢_∥_∈_ (G : CFG) : T * -> T * -> (N ∣ T)* -> Set where
  empt : {w : T *} ->
    G ⊢ w ∥ w ∈ ε

  conc : {u v w : T *} {X : N} {α β : (N ∣ T) *} ->
    (X , α) ∈ CFG.rules G ->
    G ⊢ u ∥ v ∈ α ->
    G ⊢ v ∥ w ∈ β ->
      G ⊢ u ∥ w ∈ l X ∷ β

  term : {a : T} {u v : T *} {α : (N ∣ T) *} ->
    G ⊢ u ∥ v ∈ α ->
      G ⊢ a ∷ u ∥ v ∈ r a ∷ α

infixl 10 _∙_⊢_/_⟶*_/_∙_
data _∙_⊢_/_⟶*_/_∙_ (G : CFG) :
  (t u v : T *) -> N -> (N ∣ T) * -> (N ∣ T) * -> Set where

  initial : {u : T *} {α : (N ∣ T) *} ->
    CFG.rules G ∋ (CFG.start G , α) ->
    G ∙ u ⊢ u / u ⟶* CFG.start G / ε ∙ α

  scanner : {t u v : T *} {a : T} {X : N} {α β : (N ∣ T) *} ->
    G ∙ t ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β ->
      G ∙ t ⊢ u / v ⟶* X / α ←∷ r a ∙ β

  predict : {t u v : T *} {X Y : N} {α β δ : (N ∣ T) *} -> 
    CFG.rules G ∋ (Y , δ) ->
    G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
      G ∙ t ⊢ v / v ⟶* Y / ε ∙ δ

  complet : {t u v w : T *} {X Y : N} {α β γ : (N ∣ T) *} ->
    G ∙ t ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
    G ∙ t ⊢ v / w ⟶* Y / γ ∙ ε ->
      G ∙ t ⊢ u / w ⟶* X / α ←∷ l Y ∙ β

in-g : ∀ {G t u v X α β} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
    CFG.rules G ∋ (X , α ++ β)
in-g (initial x) = x
in-g (scanner g) = in₂ (λ t -> (_ , t) ∈ _) (in₀ _ _ _) (in-g g)
in-g (predict x g) = x
in-g (complet g g₁) = in₂ (λ t -> (_ , t) ∈ _) (in₀ _ _ _) (in-g g)

suff-g₃ : ∀ {G t u v X α β} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
    Σ λ s -> s ++ v ≡ u
suff-g₃ (initial x) = σ ε refl
suff-g₃ (scanner g) with suff-g₃ g
suff-g₃ (scanner {a = a} g) | σ p₁ p₀ = σ (p₁ ←∷ a) (trans (sym (in₀ _ _ _)) (sym p₀))
suff-g₃ (predict x g) = σ ε refl
suff-g₃ (complet g g₁) with suff-g₃ g , suff-g₃ g₁
suff-g₃ (complet g g₁) | σ p₁ p₀ , σ q₁ q₀ =
  σ (p₁ ++ q₁) (trans (trans (assoc-++ p₁ _ _) (app (p₁ ++_) (sym q₀))) (sym p₀))

suff-g₂ : ∀ {G t u v X α β} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
    Σ λ s -> s ++ v ≡ t
suff-g₂ (initial x) = σ ε refl
suff-g₂ (scanner g) with suff-g₂ g
suff-g₂ (scanner {a = a} g) | σ p₁ p₀ = σ (p₁ ←∷ a) let x₁ = in₀ a p₁ _ in trans (sym x₁) (sym p₀)
suff-g₂ (predict x g) = suff-g₂ g
suff-g₂ (complet g g₁) = suff-g₂ g₁

suff-g₁ : ∀ {G t u v X α β} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
    Σ λ s -> s ++ u ≡ t
suff-g₁ (initial x) = σ ε refl
suff-g₁ (scanner g) = suff-g₁ g
suff-g₁ (predict x g) = suff-g₂ g
suff-g₁ (complet g g₁) = suff-g₁ g
  
sound₁ : ∀ {G t u v w X α β} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
    G ⊢ v ∥ w ∈ β ->
    G ⊢ u ∥ w ∈ α ++ β
sound₁ (initial x) b = b
sound₁ (scanner g) b = in₂ (λ t -> _ ⊢ _ ∥ _ ∈ t) (in₀ _ _ _) (sound₁ g (term b))
sound₁ (predict x g) b = b
sound₁ (complet g g₁) b =
  let x₁ = in₂ (λ t -> _ ⊢ _ ∥ _ ∈ t) (++-ε _) (sound₁ g₁ empt) in
  let x₂ = in₂ (λ t -> (_ , t) ∈ _) (++-ε _) (in-g g₁) in
  let x₃ = conc x₂ x₁ b in
  in₂ (λ t -> _ ⊢ _ ∥ _ ∈ t) (in₀ _ _ _) (sound₁ g x₃)

complete₁ : ∀ {t u v w X α β} {G : CFG} ->
  G ∙ t ⊢ u / v ⟶* X / α ∙ β ->
  G ⊢ v ∥ w ∈ β ->
    G ∙ t ⊢ u / w ⟶* X / α ++ β ∙ ε
complete₁ a empt = in₂ (λ t -> _ ∙ _ ⊢ _ / _ ⟶* _ / t ∙ ε) (sym (++-ε _)) a
complete₁ a (conc x g g₁) =
  let x₁ = predict x a in
  let x₂ = complete₁ x₁ g in
  let x₃ = complet a x₂ in
  let x₄ = complete₁ x₃ g₁ in
  in₂ (λ t -> _ ∙ _ ⊢ _ / _ ⟶* _ / t ∙ _) (sym (in₀ _ _ _)) x₄
complete₁ a (term g) =
  let x₁ = complete₁ (scanner a) g in
  in₂ (λ t -> _ ∙ _ ⊢ _ / _ ⟶* _ / t ∙ _) (sym (in₀ _ _ _)) x₁
