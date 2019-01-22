open import base

record Grammar (N T : Set) : Set where
  field
    start : N
    rules : (N ⟶ (N ∣ T *)) *

data _⊢_∈_ {N T : Set} (G : Grammar N T) :  T * -> N ∣ T * -> Set where
  empty :
    G ⊢ ε ∈ ε

  concat : {u v : T *} {A : N} {α : N ∣ T *} ->
    G ⊢ u ∈ l A ∷ ε -> G ⊢ v ∈ α -> G ⊢ u ++ v ∈ l A ∷ α

  term : {u : T *} {a : T} {α : N ∣ T *} ->
    G ⊢ u ∈ α -> G ⊢ a ∷ u ∈ r a ∷ α

  nonterm : {A : N} {α : N ∣ T *} {u v : T *} ->
    Grammar.rules G ∋ (A ↦ α) -> G ⊢ u ∈ α -> G ⊢ u ∈ l A ∷ ε
infixr 10 _⊢_∈_

data _⊢_/_∈_ {N T : Set} (G : Grammar N T) : T * -> T * -> N ∣ T * -> Set where
  empt : {w : T *} ->
    G ⊢ w / w ∈ ε

  conc : {u v w : T *} {X : N} {α : N ∣ T *} ->
    G ⊢ u / v ∈ l X ∷ ε ->
    G ⊢ v / w ∈ α ->
      G ⊢ u / w ∈ l X ∷ α

  term : {a : T} {u v : T *} {α : N ∣ T *} ->
    G ⊢ u / v ∈ α ->
      G ⊢ a ∷ u / v ∈ r a ∷ α

  nont : {u v : T *} {X : N} {α : N ∣ T *} ->
    Grammar.rules G ∋ (X ↦ α) ->
    G ⊢ u / v ∈ α ->
    G ⊢ u / v ∈ l X ∷ ε

infixl 10 _⊢_/_∈_

infixl 10 _⊢_∙_⟶_∙_
data _⊢_∙_⟶_∙_ {N T : Set} (G : Grammar N T) : T * -> N -> T * -> N ∣ T * -> Set where
  initial : {u : T *} ->
    G ⊢ u ∙ Grammar.start G ⟶ u ∙ l (Grammar.start G) ∷ ε

  scanner : {u v : T *} {a : T} {X : N} {β : N ∣ T *} ->
    G ⊢ u ∙ X ⟶ a ∷ v ∙ r a ∷ β ->
      G ⊢ u ∙ X ⟶ v ∙ β

  predict : {u v : T *} {X Y : N} {α β : N ∣ T *} -> 
    Grammar.rules G ∋ (Y ↦ α) ->
    G ⊢ u ∙ X ⟶ v ∙ l Y ∷ β ->
      G ⊢ v ∙ Y ⟶ v ∙ α

  complet : {u v w : T *} {X Y : N} {β : N ∣ T *} ->
    G ⊢ u ∙ X ⟶ v ∙ l Y ∷ β ->
    G ⊢ v ∙ Y ⟶ w ∙ ε ->
      G ⊢ u ∙ X ⟶ w ∙ β

sound : {N T : Set} {G : Grammar N T} {u v w : T *} {X : N} {β : N ∣ T *} ->
  G ⊢ u ∙ X ⟶ v ∙ β ->
  G ⊢ v / w ∈ β ->
    G ⊢ u / w ∈ l X ∷ ε
sound initial b = b
sound (scanner a) b = sound a (term b)
sound (predict x a) b = nont x b
sound {v = v} (complet {v = v₁} a a₁) b =
  let x₁ = sound a₁ empt in
  let x₂ = conc x₁ b in
  sound a x₂

complete : {N T : Set} {G : Grammar N T} {u v w : T *} {X : N} {α : N ∣ T *} ->
  G ⊢ u ∙ X ⟶ v ∙ α ->
  G ⊢ v / w ∈ α ->
    G ⊢ u ∙ X ⟶ w ∙ ε
complete a empt = a
complete a (conc (conc b empt) b₁) = complete a (conc b b₁)
complete a (conc (nont x b) b₁) =
  let x₁ = predict x a in
  let x₂ = complete x₁ b in
  let x₃ = complet a x₂ in
  complete x₃ b₁
complete a (term b) = complete (scanner a) b
complete a (nont x b) = complet a (complete (predict x a) b)
