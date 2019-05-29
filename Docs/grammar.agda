open import base

module grammar (N T : Set) where

open import grammar-mini N T public

infixl 10 _∙_⊢_/_⟶*_/_∙_
data _∙_⊢_/_⟶*_/_∙_ (G : CFG) (input : T *) :
  (u v : T *) -> N -> (N ∣ T) * -> (N ∣ T) * -> Set where

  initial : {α : (N ∣ T) *} ->
    (CFG.start G , α) ∈ CFG.rules G ->
      G ∙ input ⊢ input / input ⟶* CFG.start G / ε ∙ α

  scanner : {u v : T *} {a : T} {X : N} {α β : (N ∣ T) *} ->
    G ∙ input ⊢ u / a ∷ v ⟶* X / α ∙ r a ∷ β ->
      G ∙ input ⊢ u / v ⟶* X / α ←∷ r a ∙ β

  predict : {u v : T *} {X Y : N} {α β δ : (N ∣ T) *} -> 
    CFG.rules G ∋ (Y , δ) ->
    G ∙ input ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
      G ∙ input ⊢ v / v ⟶* Y / ε ∙ δ

  complet : {u v w : T *} {X Y : N} {α β γ : (N ∣ T) *} ->
    G ∙ input ⊢ u / v ⟶* X / α ∙ l Y ∷ β ->
    G ∙ input ⊢ v / w ⟶* Y / γ ∙ ε ->
      G ∙ input ⊢ u / w ⟶* X / α ←∷ l Y ∙ β

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
