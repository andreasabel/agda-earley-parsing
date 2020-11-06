open import base

module unique {T : Set} (t : StrictOrder T) where
  open StrictOrder t

  min : T -> T -> T
  min a b with tri a b
  min a b | r d = b
  min a b | l x = a

  <-min : {a b c : T} -> a < b -> a < c -> a < min b c
  <-min {a} {b} {c} p q with tri b c
  <-min {a} {b} {c} p q | r d = q
  <-min {a} {b} {c} p q | l x = p

  data Uniq : T -> Set where
    leaf : (a : T) -> Uniq a
    node : (a : T) {b : T} -> a < b -> Uniq b -> Uniq a

  data Unique : Set where
    empt : Unique
    ⟫_ : {a : T} -> Uniq a -> Unique

  ins : {a : T} (b : T) -> Uniq a -> Uniq (min a b)
  ins b (leaf a) with tri a b
  ins a (leaf a) | r (r refl) = leaf a
  ins b (leaf a) | r (l x) = node b x (leaf a)
  ins b (leaf a) | l x = node a x (leaf b)
  ins b (node a p as) with tri a b
  ins a (node a p as) | r (r refl) = node a p as
  ins b (node a p as) | r (l x) = node b x (node a p as)
  ins b (node a p as) | l x = node a (<-min p x) (ins b as)

  insert : T -> Unique -> Unique
  insert a empt = ⟫ leaf a
  insert a (⟫ x) = ⟫ ins a x

  _conc'_ : {a b : T} -> Uniq a -> Uniq b -> Unique
  _conc'_ {a} {b} (leaf a     ) bs = ⟫ ins a bs
  _conc'_ {a} {b} (node a x as) bs = insert a (as conc' bs)

  _∷∷_ : Unique -> Unique -> Unique
  empt ∷∷ bs = bs
  (⟫ x) ∷∷ empt = ⟫ x
  (⟫ x) ∷∷ (⟫ y) = x conc' y

  as-list' : {a : T} -> Uniq a -> T *
  as-list' (leaf a) = a ∷ ε
  as-list' (node a x u) = a ∷ as-list' u

  as-list : Unique -> T *
  as-list empt = ε
  as-list (⟫ x) = as-list' x

  data _isin'_ {a : T} : T -> Uniq a -> Set where
    inₗ : a isin' (leaf a)
    inₕ : {c : T} {u : Uniq c} -> (p : a < c) -> a isin' node a p u
    inₜ : {b c : T} {u : Uniq c} -> (p : a < c) -> b isin' u -> b isin' node a p u

  data _isin_ : T -> Unique -> Set where
    in⟫ : {a b : T} {u : Uniq a} -> b isin' u -> b isin (⟫ u)

  in-ins : {a b : T} {bs : Uniq b} -> a isin' ins a bs
  in-ins {a} {b} {leaf b} with tri b a
  in-ins {b} {b} {leaf b} | r (r refl) = inₗ
  in-ins {a} {b} {leaf b} | r (l x) = inₕ x
  in-ins {a} {b} {leaf b} | l x = inₜ x inₗ
  in-ins {a} {b} {node b x bs} with tri b a
  in-ins {b} {b} {node b x bs} | r (r refl) = inₕ x
  in-ins {a} {b} {node b x bs} | r (l x₁) = inₕ x₁
  in-ins {a} {b} {node b x bs} | l x₁ = inₜ (<-min x x₁) (in-ins {bs = bs})

  in-insert : {a : T} {bs : Unique} -> a isin insert a bs
  in-insert {a} {empt} = in⟫ inₗ
  in-insert {a} {⟫ bs} = in⟫ (in-ins {bs = bs})

  in-mou : {a b c : T} {bs : Uniq b} -> c isin' bs -> c isin' ins a bs
  in-mou {a} {b} {b} inₗ with tri b a
  in-mou {b} {b} {b} inₗ | r (r refl) = inₗ
  in-mou {a} {b} {b} inₗ | r (l x) = inₜ x inₗ
  in-mou {a} {b} {b} inₗ | l x = inₕ x
  in-mou {a} {b} {b} (inₕ p) with tri b a
  in-mou {b} {b} {b} (inₕ p) | r (r refl) = inₕ p
  in-mou {a} {b} {b} (inₕ p) | r (l x) = inₜ x (inₕ p)
  in-mou {a} {b} {b} (inₕ p) | l x = inₕ (<-min p x)
  in-mou {a} {b} {c} (inₜ p p₁) with tri b a
  in-mou {b} {b} {c} (inₜ p p₁) | r (r refl) = inₜ p p₁
  in-mou {a} {b} {c} (inₜ p p₁) | r (l x) = inₜ x (inₜ p p₁)
  in-mou {a} {b} {c} (inₜ p p₁) | l x = inₜ (<-min p x) (in-mou p₁)

  in-already : {a b : T} {bs : Unique} -> b isin bs -> b isin insert a bs
  in-already {bs = empt} ()
  in-already {bs = ⟫ bs} (in⟫ p) = in⟫ (in-mou p)

  in-conc-l : {a b c : T} {as : Uniq a} {bs : Uniq b} -> c isin' as -> c isin (as conc' bs)
  in-conc-l {as = leaf a} {bs} inₗ = in⟫ (in-ins {bs = bs})
  in-conc-l {as = node a x as} {bs} (inₕ x) = in-insert
  in-conc-l {as = node a x as} {bs} (inₜ x p) = in-already (in-conc-l p)

  in-∷∷-l : {a : T} {as bs : Unique} -> a isin as -> a isin (as ∷∷ bs)
  in-∷∷-l {a} {empt} {bs} ()
  in-∷∷-l {a} {⟫ as} {empt} p = p
  in-∷∷-l {a} {⟫ as} {⟫ bs} (in⟫ p) = in-conc-l p

  in-conc-r : {a b c : T} {as : Uniq a} {bs : Uniq b} -> c isin' bs -> c isin (as conc' bs)
  in-conc-r {as = leaf a} {bs} p = in⟫ (in-mou p)
  in-conc-r {as = node a x as} {bs} p = in-already (in-conc-r {as = as} p)

  in-∷∷-r : {a : T} {as bs : Unique} -> a isin bs -> a isin (as ∷∷ bs)
  in-∷∷-r {a} {empt} {bs} p = p
  in-∷∷-r {a} {⟫ as} {empt} ()
  in-∷∷-r {a} {⟫ as} {⟫ bs} (in⟫ p) = in-conc-r {as = as} p

  _elemOf_ : {a : T} (t : T) -> (u : Uniq a) -> t isin' u ??
  t elemOf leaf a with tri t a
  a elemOf leaf a | r (r refl) = yes inₗ
  t elemOf leaf a | r (l x) = no λ {inₗ → void (tri₁ x x)}
  t elemOf leaf a | l x = no λ {inₗ → void (tri₁ x x)}
  t elemOf node a p as with tri t a
  a elemOf node a p as | r (r refl) = yes (inₕ p)
  t elemOf node a p as | r (l x) with t elemOf as
  t elemOf node a p as | r (l x) | yes x₁ = yes (inₜ p x₁)
  t elemOf node a p as | r (l x) | no x₁ = no λ {(inₕ p) → void (tri₁ x x) ; (inₜ p x₂) → void (x₁ x₂)}
  t elemOf node a p as | l x with t elemOf as
  t elemOf node a p as | l x | yes x₁ = yes (inₜ p x₁)
  t elemOf node a p as | l x | no x₁ = no λ {(inₕ p) → void (tri₁ x x) ; (inₜ p x₂) → void (x₁ x₂)}

  _\\'_ : {a b : T} -> Uniq a -> Uniq b -> Unique
  leaf a \\' bs with a elemOf bs
  leaf a \\' bs | yes x = empt
  leaf a \\' bs | no x = ⟫ leaf a
  node a x as \\' bs with a elemOf bs
  node a x as \\' bs | yes x₁ = as \\' bs
  node a x as \\' bs | no x₁ = insert a (as \\' ins a bs)

  _\\_ : Unique -> Unique -> Unique
  empt \\ b = empt
  (⟫ x) \\ empt = ⟫ x
  (⟫ x) \\ (⟫ y) = x \\' y

  data _⊂_ : {a b : T} -> Uniq a -> Uniq b -> Set where
    ⊂₀ : {a b : T} {as : Uniq b} ->
      (p : a < b) -> as ⊂ node a p as

    ⊂ᵣ : {a b c : T} {as : Uniq a} {bs : Uniq b} ->
      (p : c < b) -> as ⊂ bs -> as ⊂ node c p bs

    ⊂ₗ : {a b c : T} {as : Uniq a} {bs : Uniq b} ->
      (p : c < a) (q : c < b) -> as ⊂ bs -> node c p as ⊂ node c q bs

--  data Acc-⊂ : {a : T} -> Uniq a -> Set where
--    acc : ∀ {b} {bs : Uniq b} -> (∀ {a} {as : Uniq a} -> as ⊂ bs -> Acc-⊂ as) -> Acc-⊂ bs
--
--  acc-s : {a : T} -> Acc-⊂ (leaf a)
--  acc-s = acc λ ()
--
--  acc-⊂-2 : ∀ {b₀ b₁} (p : b₀ < b₁) ->
--    ∀ {a} (as : Uniq a) -> as ⊂ node b₀ p (leaf b₁) -> Acc-⊂ as
--  acc-⊂-2 p .(leaf _) (⊂₀ .p) = acc-s
--  acc-⊂-2 p as (⊂ᵣ .p ())
--  acc-⊂-2 p .(node _ p₁ _) (⊂ₗ p₁ .p ())
--
--  acc-2 : ∀ {b₀ b₁} (p : b₀ < b₁) -> Acc-⊂ (node b₀ p (leaf b₁))
--  acc-2 p = acc (acc-⊂-2 p _)
--
--  acc-node-⊂-2 : ∀ {b₀ b₁ b₂} (p : b₀ < b₁) ->
--    ∀ {a} (p₁ : b₂ < a) (as : Uniq a) -> as ⊂ node b₀ p (leaf b₁) -> Acc-⊂ (node b₂ p₁ as)
--  acc-node-⊂-2 p p₁ .(leaf _) (⊂₀ .p) = acc-2 p₁
--  acc-node-⊂-2 p p₁ as (⊂ᵣ .p ())
--  acc-node-⊂-2 p p₁ .(node _ p₂ _) (⊂ₗ p₂ .p ())
--
--  acc-⊂-3 : ∀ {b₀ b₁ b₂} (p₀ : b₀ < b₁) (p₁ : b₁ < b₂) ->
--    ∀ {a} (as : Uniq a) -> as ⊂ node b₀ p₀ (node b₁ p₁ (leaf b₂)) -> Acc-⊂ as
--  acc-⊂-3 p₀ p₁ as (⊂₀ .p₀) = acc-2 p₁
--  acc-⊂-3 p₀ p₁ as (⊂ᵣ .p₀ sub) = acc-⊂-2 p₁ as sub
--  acc-⊂-3 p₀ p₁ as (⊂ₗ p .p₀ sub) = acc-node-⊂-2 p₁ p _ sub
--
--  acc-3 : ∀ {b₀ b₁ b₂} (p₀ : b₀ < b₁) (p₁ : b₁ < b₂) ->
--    Acc-⊂ (node b₀ p₀ (node b₁ p₁ (leaf b₂)))
--  acc-3 p₀ p₁ = acc (acc-⊂-3 p₀ p₁ _)
--
--  acc-node-⊂-3 : ∀ {b₀ b₁ b₂ b₃} (p₀ : b₀ < b₁) (p₁ : b₁ < b₂) ->
--    ∀ {a} (p₃ : b₃ < a) (as : Uniq a) -> as ⊂ node b₀ p₀ (node b₁ p₁ (leaf b₂)) -> Acc-⊂ (node b₃ p₃ as)
--  acc-node-⊂-3 p₀ p₁ p₃ .(node _ p₁ (leaf _)) (⊂₀ .p₀) = acc-3 p₃ p₁
--  acc-node-⊂-3 p₀ p₁ p₃ as (⊂ᵣ .p₀ sub) = acc-node-⊂-2 p₁ p₃ as sub
--  acc-node-⊂-3 p₀ p₁ p₃ .(node _ p _) (⊂ₗ p .p₀ sub) = {!sub!}
--
--  acc-⊂-4 : ∀ {b₀ b₁ b₂ b₃} (p₀ : b₀ < b₁) (p₁ : b₁ < b₂) (p₂ : b₂ < b₃)->
--    ∀ {a} (as : Uniq a) -> as ⊂ node b₀ p₀ (node b₁ p₁ (node b₂ p₂ (leaf b₃))) -> Acc-⊂ as
--  acc-⊂-4 p₀ p₁ p₂ _ (⊂₀ .p₀) = acc-3 p₁ p₂
--  acc-⊂-4 p₀ p₁ p₂ as (⊂ᵣ .p₀ sub) = acc-⊂-3 p₁ p₂ as sub
--  acc-⊂-4 p₀ p₁ p₂ .(node _ p _) (⊂ₗ p .p₀ sub) = acc-node-⊂-3 p₁ p₂ p _ sub
