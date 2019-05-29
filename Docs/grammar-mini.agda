open import base

module grammar-mini (N T : Set) where

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
