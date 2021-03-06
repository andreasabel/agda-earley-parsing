open import Agda.Builtin.Equality public

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)
infixl 20 _∘_

id : {T : Set} -> T -> T
id x = x

app : {T U : Set} {a b : T} (f : T -> U) -> a ≡ b -> f a ≡ f b
app f refl = refl

trans : {T : Set} {a b c : T} -> a ≡ b -> c ≡ b -> a ≡ c
trans refl refl = refl

sym : {T : Set} {a b : T} -> a ≡ b -> b ≡ a
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : (a b : ℕ) -> ℕ
zero + b = b
suc a + b = suc (a + b)

+ₛ : {a b : ℕ} -> a + suc b ≡ suc (a + b)
+ₛ {zero} = refl
+ₛ {suc a} = app suc +ₛ

+-zero : {a : ℕ} -> a + zero ≡ a
+-zero {zero} = refl
+-zero {suc a} = app suc +-zero

suc-comm : {a b : ℕ} -> b + suc a ≡ suc (b + a)
suc-comm {a} {zero} = refl
suc-comm {a} {suc b} = app suc suc-comm

+-comm : {a b : ℕ} -> a + b ≡ b + a
+-comm {zero} {b} = sym +-zero
+-comm {suc a} {b} = trans (app suc (+-comm {a} {b})) suc-comm

+-assoc : (a b c : ℕ) -> a + (b + c) ≡ (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c = app suc (+-assoc a b c)

record Injective {A B : Set} (f : A -> B) : Set where
  field
    inj : ({a b : A} -> f a ≡ f b -> a ≡ b)

unsuc : {a b : ℕ} -> suc a ≡ suc b -> a ≡ b
unsuc refl = refl

inj-suc : Injective suc
inj-suc = record { inj = unsuc }

data _≤_ : ℕ -> ℕ -> Set where
  ≤₀ : {n : ℕ} -> zero ≤ n
  ≤ₛ : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

subtract : (a b : ℕ) -> b ≤ a -> ℕ
subtract a zero ≤₀ = a
subtract (suc a) (suc b) (≤ₛ p) = subtract a b p

_-_ : (x x₁ : ℕ) (x₂ : x₁ ≤ x) → ℕ
_-_ = subtract

≤-zero : {n : ℕ} -> n ≤ zero -> n ≡ zero
≤-zero ≤₀ = refl

≤-suc : {n m : ℕ} -> n ≤ m -> n ≤ suc m
≤-suc ≤₀ = ≤₀
≤-suc (≤ₛ p) = ≤ₛ (≤-suc p)

suc-le : {n m : ℕ} -> suc n ≤ suc m -> n ≤ m
suc-le (≤ₛ a) = a

suc-≤ : {n m : ℕ} -> suc n ≤ m -> n ≤ m
suc-≤ (≤ₛ p) = ≤-suc p

≤-self : (n : ℕ) -> n ≤ n
≤-self zero = ≤₀
≤-self (suc n) = ≤ₛ (≤-self n)

≤-trans : {m n o : ℕ} -> m ≤ n -> n ≤ o -> m ≤ o
≤-trans ≤₀ q = ≤₀
≤-trans (≤ₛ p) (≤ₛ q) = ≤ₛ (≤-trans p q)

data Void : Set where

⊥ : Set
⊥ = Void

data ⊤ : Set where
 top : ⊤

any : {T : Set} -> T -> ⊤
any T = top

¬_ : (A : Set) -> Set
¬ A = A -> Void

infixr 0 ¬_

void : {l : _} {T : Set l} -> .Void -> T
void ()

void₁ : {T : Set₁} -> Void -> T
void₁ ()

+-imp : {a b : ℕ} -> a ≡ suc (a + b) -> Void
+-imp {zero} {b} ()
+-imp {suc a} {b} p = +-imp (unsuc p)

≤-imp : {a : ℕ} -> suc a ≤ a -> Void
≤-imp (≤ₛ p) = ≤-imp p

oddsuc : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> Void
oddsuc refl ()

≤-≠ : {m n : ℕ} -> m ≤ n -> (suc n ≡ suc m -> Void) -> suc m ≤ n
≤-≠ {zero}  {zero}  ≤₀ p₁ = void (p₁ refl)
≤-≠ {zero}  {suc n} ≤₀ p₁ = ≤ₛ ≤₀
≤-≠ {suc m} {zero}  () p₁
≤-≠ {suc m} {suc n} p₀ p₁ = ≤ₛ (≤-≠ (suc-le p₀) λ {refl → p₁ refl})

_≠_ : {T : Set} -> T -> T -> Set
a ≠ b = a ≡ b -> Void

data _∣_ (A B : Set) : Set where
  r : B -> A ∣ B
  l : A -> A ∣ B
infixr 3 _∣_

data Bool : Set where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

data Maybe : Set -> Set where
  Just : {T : Set} -> T -> Maybe T
  Nothing : {T : Set} -> Maybe T

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B
infixl 2 _,_
infixl 20 _×_

record Σₗ {l : _} {A : Set l} (f : A -> Set) : Set l where
  constructor σ
  field
    proj₁ : A
    proj₀ : f proj₁

record Σ {A : Set} (f : A -> Set) : Set where
  constructor σ
  field
    proj₁ : A
    proj₀ : f proj₁

record Σ₂ {A B : Set} (f : A -> B -> Set) : Set where
  constructor σ₂
  field
    proj₁ : A
    proj₂ : B
    proj₀ : f proj₁ proj₂

record Σ₃ {A B C : Set} (f : A -> B -> C -> Set) : Set where
  constructor σ₃
  field
    proj₁ : A
    proj₂ : B
    proj₃ : C
    proj₀ : f proj₁ proj₂ proj₃

record Σ₄ {A B C D : Set} (f : A -> B -> C -> D -> Set) : Set where
  constructor σ₄
  field
    p₁ : A
    p₂ : B
    p₃ : C
    p₄ : D
    p₀ : f p₁ p₂ p₃ p₄

fst : {A B : Set} -> A × B -> A
fst (a , b) = a

snd : {A B : Set} -> A × B -> B
snd (a , b) = b

data _?? (A : Set) : Set where
  yes : A -> A ??
  no  : (A -> Void) -> A ??
infixl 1 _??

record Equality (A : Set) : Set where
  field
    eq : (a b : A) -> a ≡ b ??

record StrictOrder (A : Set) : Set₁ where
  field
    _<_ : A -> A -> Set
    transitive : {a b c : A} -> a < b -> b < c -> a < c
    tri  : (a b : A) -> a < b ∣ b < a ∣ a ≡ b
    tri₁ : {a b : A} -> a < b -> b < a -> Void
    tri₂ : {a b : A} -> a < b -> a ≡ b -> Void

decid-≡ : {T : Set} -> StrictOrder T -> (a b : T) -> a ≡ b ??
decid-≡ s a b with StrictOrder.tri s a b
decid-≡ s a b | r (r x) = yes x
decid-≡ s a b | r (l x) = no λ x₁ → StrictOrder.tri₂ s x (sym x₁)
decid-≡ s a b | l x = no (StrictOrder.tri₂ s x)

--ord-× : {T U : Set} -> StrictOrder T -> StrictOrder U -> StrictOrder (T × U)
--ord-× t u = record {
--  _<_ = λ { (a , a₁) (b , b₁) → StrictOrder._<_ t a b ∣ (a ≡ b) × StrictOrder._<_ u a₁ b₁ } ;
--  transitive = {!!} ;
--  tri = {!!} ;
--  tri₁ = {!!} ;
--  tri₂ = {!!}
--  }

eq-ℕ : (a b : ℕ) -> a ≡ b ??
eq-ℕ zero zero = yes refl
eq-ℕ zero (suc b) = no (λ ())
eq-ℕ (suc a) zero = no (λ ())
eq-ℕ (suc a) (suc b) with eq-ℕ a b
eq-ℕ (suc a) (suc b) | yes x = yes (app suc x)
eq-ℕ (suc a) (suc b) | no x = no (λ x₁ → x (unsuc x₁))

data _* (T : Set) : Set where
  ε : T *
  _∷_ : T -> T * -> T *
infixr 80 _*
infixr 20 _∷_

{-# BUILTIN LIST _* #-}

inj-cons : ∀ {T a} -> Injective {T} (_∷ a)
inj-cons = record { inj = λ {refl → refl} }

uncons : ∀ {T as bs} (a b : T) -> a ∷ as ≡ b ∷ bs -> as ≡ bs
uncons a b refl = refl

uncons₂ : ∀ {T as bs} (a b : T) -> a ∷ as ≡ b ∷ bs -> a ≡ b
uncons₂ a b refl = refl

_←∷_ : {T : Set} -> T * -> T -> T *
ε ←∷ a = a ∷ ε
(x ∷ as) ←∷ a = x ∷ (as ←∷ a)

map : {T U : Set} -> (T -> U) -> T * -> U *
map f ε = ε
map f (x ∷ xs) = f x ∷ map f xs

filter : {T : Set} -> (T -> Bool) -> T * -> T *
filter f ε = ε
filter f (x ∷ xs) with f x
filter f (x ∷ xs) | true = x ∷ filter f xs
filter f (x ∷ xs) | false = filter f xs

data _∋_ {T : Set} : T * -> T -> Set where
  in-head : {t : T} {ts : T *} -> (t ∷ ts) ∋ t
  in-tail : {t u : T} {ts : T *} -> ts ∋ t -> (u ∷ ts) ∋ t

_∈_ : {T : Set} -> T -> T * -> Set
a ∈ b = b ∋ a

untail : ∀ {T ts} {t u : T} {a b : ts ∋ t} -> in-tail {T} {t} {u} a ≡ in-tail b -> a ≡ b
untail refl = refl

data _suffixOf_ {T : Set} : T * -> T * -> Set where
  suffix-id : {as : T *} -> as suffixOf as
  suffix-∷ : {b : T} {as bs : T *} -> as suffixOf bs -> as suffixOf b ∷ bs

infix 18 _suffixOf_

mapₚ : ∀ {T U} {P : T -> Set} -> ((t : T) -> P t -> U) -> (xs : T *) -> (∀ {t} -> xs ∋ t -> P t) -> U *
mapₚ f ε p = ε
mapₚ f (x ∷ xs) p = f x (p in-head) ∷ mapₚ f xs (p ∘ in-tail)

length : {T : Set} -> T * -> ℕ
length ε = zero
length (x ∷ xs) = suc (length xs)

tail : {T : Set} -> T * -> T *
tail ε = ε
tail (x ∷ xs) = xs

elem : {T : Set} -> (eq : (a b : T) -> a ≡ b ??) -> (t : T) -> (ts : T *) -> ts ∋ t ??
elem eq t ε = no (λ ())
elem eq t (x ∷ ts) with eq t x
elem eq t (t ∷ ts) | yes refl = yes in-head
elem eq t (x ∷ ts) | no x₁ with elem eq t ts
elem eq t (x ∷ ts) | no x₁ | yes x₂ = yes (in-tail x₂)
elem eq t (x ∷ ts) | no x₁ | no x₂ = no (nul x₁ x₂)
  where
    nul : {T : Set} {t x : T} {ts : T *} -> (t ≡ x -> Void) -> (ts ∋ t -> Void) -> (x ∷ ts) ∋ t -> Void
    nul p q in-head = p refl
    nul p q (in-tail p₁) = q p₁

in-tail' : {T : Set} {ts : T *} {x t : T} -> (x ∷ ts) ∋ t -> (t ≡ x -> Void) -> ts ∋ t
in-tail' in-head f = void (f refl)
in-tail' (in-tail p) f = p

elem' : {T : Set} -> (eq : (a b : T) -> a ≡ b ??) -> (t : T) -> (ts : T *) -> .(ts ∋ t)-> ts ∋ t
elem' eq t ε ()
elem' eq t (x ∷ ts) p with eq t x
elem' eq t (t ∷ ts) p | yes refl = in-head
elem' eq t (x ∷ ts) p | no x₁ = in-tail (elem' eq t ts (in-tail' p x₁))

_++_ : {T : Set} -> T * -> T * -> T *
ε ++ b = b
(x ∷ a) ++ b = x ∷ (a ++ b)

join : {T : Set} -> T * * -> T *
join ε = ε
join (ts ∷ tss) = ts ++ join tss

suffix-++ : {T : Set} (as bs : T *) -> bs suffixOf as ++ bs
suffix-++ ε bs = suffix-id
suffix-++ (x ∷ as) bs = suffix-∷ (suffix-++ as bs)

++-ε : {T : Set} (as : T *) -> as ++ ε ≡ as
++-ε ε = refl
++-ε (x ∷ as) = app (x ∷_) (++-ε as)

assoc-++ : ∀ {T} -> (as bs cs : T *) -> (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
assoc-++ ε bs cs = refl
assoc-++ (x ∷ as) bs cs = app (x ∷_) (assoc-++ as bs cs)

in-r : {T : Set} {b : T} {as bs : T *} -> bs ∋ b -> (as ++ bs) ∋ b
in-r {as = ε} p = p
in-r {as = x ∷ as} p = in-tail (in-r p)

in-l : {T : Set} {a : T} {as bs : T *} -> as ∋ a -> (as ++ bs) ∋ a
in-l in-head = in-head
in-l (in-tail p) = in-tail (in-l p)

in-either : ∀ {T} {a : T} -> ∀ as bs -> a ∈ (as ++ bs) -> a ∈ as ∣ a ∈ bs
in-either ε bs p = r p
in-either (a ∷ as) bs in-head = l in-head
in-either (a ∷ as) bs (in-tail p) with in-either as bs p
in-either (a ∷ as) bs (in-tail p) | r x = r x
in-either (a ∷ as) bs (in-tail p) | l x = l (in-tail x)

in-lr₂ : ∀ {T} {a b : T} -> ∀ as bs -> a ∈ (as ++ (b ∷ bs)) -> a ∈ ((b ∷ as) ++ bs)
in-lr₂ ε bs p = p
in-lr₂ (x ∷ as) bs in-head = in-tail in-head
in-lr₂ (x ∷ as) bs (in-tail p) with in-lr₂ as bs p
in-lr₂ (x ∷ as) bs (in-tail p) | in-head = in-head
in-lr₂ (x ∷ as) bs (in-tail p) | in-tail d = in-tail (in-tail d)

in-lr₃ : ∀ {T} {a b : T} -> ∀ as bs -> a ∈ ((b ∷ as) ++ bs) -> a ∈ (as ++ (b ∷ bs))
in-lr₃ ε bs p = p
in-lr₃ (a ∷ as) bs in-head = in-r {as = a ∷ as} in-head
in-lr₃ (a ∷ as) bs (in-tail in-head) = in-head
in-lr₃ (a ∷ as) bs (in-tail (in-tail p)) with in-either as bs p
in-lr₃ (a ∷ as) bs (in-tail (in-tail p)) | r x = in-tail (in-r (in-tail x))
in-lr₃ (a ∷ as) bs (in-tail (in-tail p)) | l x = in-tail (in-l x)

in-lr₄ : ∀ {T} {a b : T} -> ∀ as bs -> a ∈ (as ++ bs) -> a ∈ (as ++ (b ∷ bs))
in-lr₄ as bs p with in-either as bs p
in-lr₄ as bs p | r x = in-r (in-tail x)
in-lr₄ as bs p | l x = in-l x

in-lr₅ : ∀ {T} {a b : T} -> ∀ as bs -> b ∈ as -> a ∈ (as ++ (b ∷ bs)) -> a ∈ (as ++ bs)
in-lr₅ as bs p q with in-either as _ q
in-lr₅ as bs p q | r in-head = in-l p
in-lr₅ as bs p q | r (in-tail x) = in-r x
in-lr₅ as bs p q | l x = in-l x

in-neither : ∀ {T as bs} {a : T} -> (as ∋ a -> Void) -> (bs ∋ a -> Void) -> (as ++ bs) ∋ a -> Void
in-neither {T} {ε} {bs} p q s = q s
in-neither {T} {x ∷ as} {bs} p q in-head = p in-head
in-neither {T} {x ∷ as} {bs} p q (in-tail s) = in-neither (p ∘ in-tail) q s

in-both : ∀ {T as bs} {a : T} -> (P : T -> Set) ->
  (a ∈ as -> P a) -> (a ∈ bs -> P a) -> a ∈ (as ++ bs) -> P a
in-both {T} {ε} {bs} P p q s = q s
in-both {T} {x ∷ as} {bs} P p q in-head = p in-head
in-both {T} {x ∷ as} {bs} P p q (in-tail s) = in-both P (p ∘ in-tail) q s

not-in-l : {T : Set} {b : T} {as bs : T *} -> ((as ++ bs) ∋ b -> Void) -> as ∋ b -> Void
not-in-l f in-head = f in-head
not-in-l f (in-tail p) = not-in-l (f ∘ in-tail) p

not-in-r : {T : Set} {b : T} {as bs : T *} -> ((as ++ bs) ∋ b -> Void) -> bs ∋ b -> Void
not-in-r {as = ε} f p = f p
not-in-r {as = x ∷ as} f p = not-in-r (f ∘ in-tail) p

in-map : {T U : Set} (f : T -> U) {as : T *} {a : T} -> as ∋ a -> map f as ∋ f a
in-map f {ε} ()
in-map f {x ∷ as} in-head = in-head
in-map f {x ∷ as} (in-tail p) = in-tail (in-map f p)

in₀ : {T : Set} (a : T) (as bs : T *) -> as ++ (a ∷ bs) ≡ (as ←∷ a) ++ bs
in₀ a ε bs = refl
in₀ a (x ∷ as) bs = app (x ∷_) (in₀ a as bs)

in₁ : ∀ {T xs a} {b : T} -> a ≡ b -> xs ∋ a -> xs ∋ b
in₁ refl p = p

in₂ : ∀ {T : Set} {a b : T} (P : T -> Set) -> a ≡ b -> P a -> P b
in₂ P refl p = p

in₃ : ∀ {T} (a b c d : T *) -> a ≡ b ++ c -> b ++ (c ++ d) ≡ a ++ d
in₃ a b c d p = let x₁ = sym (assoc-++ b c d) in sym (trans (app (_++ d) p) x₁)

in₄ : ∀ {N T rs} {X : N} {α β : _} {x : N ∣ T} -> (X , (α ++ (x ∷ β))) ∈ rs -> (X , ((α ←∷ x) ++ β)) ∈ rs
in₄ {rs = rs} {X} χ = in₂ (λ q → (X , q) ∈ rs) (in₀ _ _ _) χ

case_of_ : ∀ {a b} {A : Set a} {B : Set b} -> A -> (A -> B) -> B
case x of f = f x

case'_of_ : {A B : Set} -> (a₁ : A) -> ((a₂ : A) -> a₁ ≡ a₂ -> B) -> B
case' x of f = f x refl

dropSuffix : {T : Set} -> (as bs : T *) -> bs suffixOf as -> T *
dropSuffix as as suffix-id = ε
dropSuffix (a ∷ as) bs (suffix-∷ p) = a ∷ dropSuffix as bs p

suffix-trans : {T : Set} {as bs cs : T *} -> bs suffixOf as -> cs suffixOf bs -> cs suffixOf as
suffix-trans suffix-id q = q
suffix-trans (suffix-∷ p) q = suffix-∷ (suffix-trans p q)

dropSuffix-++ : {T : Set} {u v w : T *} (p : v suffixOf u) (q : w suffixOf v) ->
  dropSuffix u v p ++ dropSuffix v w q ≡ dropSuffix u w (suffix-trans p q)
dropSuffix-++ suffix-id q = refl
dropSuffix-++ (suffix-∷ {b = b} p) q =
  let x₁ = dropSuffix-++ p q in
  app (b ∷_) x₁

dropSuffix-++₂ : {T : Set} {u v : T *} (p : v suffixOf u) ->
  dropSuffix u v p ++ v ≡ u
dropSuffix-++₂ suffix-id = refl
dropSuffix-++₂ (suffix-∷ {b = b} p) = app (b ∷_) (dropSuffix-++₂ p)

_∷←_ : {T : Set} -> T * -> T -> T *
ε ∷← b = b ∷ ε
(x ∷ a) ∷← b = x ∷ (a ∷← b)

reverse : {T : Set} -> T * -> T *
reverse ε = ε
reverse (x ∷ xs) = reverse xs ∷← x

filter-unique : {T : Set} -> ((a b : T) -> a ≡ b ??) -> T * -> T *
filter-unique eq ε = ε
filter-unique eq (x ∷ xs) with elem eq x xs
filter-unique eq (x ∷ xs) | yes x₁ = filter-unique eq xs
filter-unique eq (x ∷ xs) | no x₁ = x ∷ filter-unique eq xs

not-in-head : {T : Set} ->
  (x y : T) ->
  (xs : T *) ->
  (y ≡ x -> Void) ->
  (x ∷ xs) ∋ y ->
  xs ∋ y
not-in-head x x xs f in-head with f refl
... | ()
not-in-head x y xs f (in-tail p) = p

filter-unique-s₀ : {T : Set} ->
  (eq : (a b : T) -> a ≡ b ??) ->
  (xs : T *) ->
  (x : T) ->
  xs ∋ x ->
  filter-unique eq xs ∋ x
filter-unique-s₀ eq ε x ()
filter-unique-s₀ eq (x₁ ∷ xs) x  p with eq x x₁
filter-unique-s₀ eq (x₁ ∷ xs) x  p | yes refl with elem eq x₁ xs
filter-unique-s₀ eq (x₁ ∷ xs) x₁ p | yes refl | yes x = filter-unique-s₀ eq xs x₁ x
filter-unique-s₀ eq (x₁ ∷ xs) x₁ p | yes refl | no x = in-head
filter-unique-s₀ eq (x₁ ∷ xs) x  p | no x₂    with elem eq x₁ xs
filter-unique-s₀ eq (x₁ ∷ xs) x  p | no x₂    | yes x₃ = filter-unique-s₀ eq xs x (not-in-head x₁ x xs x₂ p)
filter-unique-s₀ eq (x₁ ∷ xs) x  p | no x₂    | no x₃ = in-tail (filter-unique-s₀ eq xs x (not-in-head x₁ x xs x₂ p))

list-diff : {T : Set} -> ((a b : T) -> a ≡ b ??) ->
  T * -> T * -> T *
list-diff eq ε ys = ε
list-diff eq (x ∷ xs) ys with elem eq x ys
...                      | yes x₁ = list-diff eq xs ys
...                      | no x₁ = x ∷ list-diff eq xs (x ∷ ys)

unord-maintain : ∀ {T xs ys} ->
  ({x : T} -> xs ∋ x -> ys ∋ x) ->
  (∀ {y x} -> (y ∷ xs) ∋ x -> (y ∷ ys) ∋ x)
unord-maintain f in-head = in-head
unord-maintain f (in-tail p) = in-tail (f p)

diff-unord : ∀ {T} (xs ys zs : T *) ->
  (eq : (a b : T) -> a ≡ b ??) ->
  (∀ {x} -> zs ∋ x -> ys ∋ x) ->
  (∀ {x} -> ys ∋ x -> zs ∋ x) ->
  list-diff eq xs ys ≡ list-diff eq xs zs
diff-unord ε ys zs eq f g = refl
diff-unord (x ∷ xs) ys zs eq f g with elem eq x ys
diff-unord (x ∷ xs) ys zs eq f g | b      with elem eq x zs
diff-unord (x ∷ xs) ys zs eq f g | yes x₁ | yes x₂ = diff-unord xs ys zs eq f g
diff-unord (x ∷ xs) ys zs eq f g | yes x₁ | no x₂ with x₂ (g x₁)
... | ()
diff-unord (x ∷ xs) ys zs eq f g | no x₁  | yes x₂ with x₁ (f x₂)
... | ()
diff-unord (x ∷ xs) ys zs eq f g | no x₁  | no x₂ =
  app (x ∷_) (diff-unord xs (x ∷ ys) (x ∷ zs) eq (unord-maintain f) (unord-maintain g))

diff-flip : ∀ {T} (x y : T) (xs ys : T *) ->
  (eq : (a b : T) -> a ≡ b ??) ->
  list-diff eq xs (x ∷ y ∷ ys) ≡ list-diff eq xs (y ∷ x ∷ ys)
diff-flip x y xs ys eq = diff-unord xs (x ∷ y ∷ ys) (y ∷ x ∷ ys) eq f g
  where
    f : ∀ {z} -> (y ∷ x ∷ ys) ∋ z -> (x ∷ y ∷ ys) ∋ z
    f in-head = in-tail in-head
    f (in-tail in-head) = in-head
    f (in-tail (in-tail p)) = in-tail (in-tail p)

    g : ∀ {z} -> (x ∷ y ∷ ys) ∋ z -> (y ∷ x ∷ ys) ∋ z
    g in-head = in-tail in-head
    g (in-tail in-head) = in-head
    g (in-tail (in-tail p)) = in-tail (in-tail p)

not-in : ∀ {T} {x y : T} {xs : T *} ->
  ((y ∷ xs) ∋ x -> Void) ->
  (xs ∋ x -> Void)
not-in p₁ p₂ = p₁ (in-tail p₂)

diff-idem-l : {T : Set} (x : T) (xs ys : T *) ->
  (eq : (a b : T) -> a ≡ b ??) ->
  (xs ∋ x -> Void) ->
  list-diff eq xs ys ≡ list-diff eq xs (x ∷ ys)
diff-idem-l x ε ys eq p₁ = refl
diff-idem-l x (x₁ ∷ xs) ys eq p₁ with elem eq x₁ ys
... | b      with elem eq x₁ (x ∷ ys)
diff-idem-l x (x₁ ∷ xs) ys eq p₁ | yes x₂ | yes x₃ = diff-idem-l x xs ys eq (not-in p₁)
diff-idem-l x (x₁ ∷ xs) ys eq p₁ | yes x₂ | no x₃ with x₃ (in-tail x₂)
... | ()
diff-idem-l x (x  ∷ xs) ys eq p₁ | no x₂  | yes in-head with p₁ in-head
... | ()
diff-idem-l x (x₁ ∷ xs) ys eq p₁ | no x₂  | yes (in-tail x₃) with x₂ x₃
... | ()
diff-idem-l x (x₁ ∷ xs) ys eq p₁ | no x₂  | no x₃ =
  let w₁ = diff-flip x₁ x xs ys eq in
  app (x₁ ∷_) (trans (diff-idem-l x xs (x₁ ∷ ys) eq λ x₄ → p₁ (in-tail x₄)) w₁)

diff-suc : {T : Set} {x : T} {xs ys : T *} ->
  (eq : (x y : T) -> x ≡ y ??) ->
  xs ∋ x ->
  (ys ∋ x -> Void) ->
  length (list-diff eq xs ys) ≡ suc (length (list-diff eq xs (x ∷ ys)))
diff-suc {T} {x} {ε} {ys} eq () p₂
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq p₁ p₂           with elem eq x₁ ys
...                                                | b      with elem eq x₁ (x ∷ ys)
diff-suc {T} {x} {x  ∷ xs} {ys} eq in-head p₂      | yes x₂ | yes x₃ with p₂ x₂
diff-suc {T} {x} {x  ∷ xs} {ys} eq in-head p₂      | yes x₂ | yes x₃ | ()
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq (in-tail p₁) p₂ | yes x₂ | yes x₃ = diff-suc eq p₁ p₂
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq p₁ p₂           | yes x₂ | no x₃  with x₃ (in-tail x₂)
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq p₁ p₂           | yes x₂ | no x₃  | ()
diff-suc {T} {x} {x  ∷ xs} {ys} eq p₁ p₂           | no x₂  | yes in-head = refl
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq p₁ p₂           | no x₂  | yes (in-tail x₃) with x₂ x₃
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq p₁ p₂           | no x₂  | yes (in-tail x₃) | ()
diff-suc {T} {x} {x  ∷ xs} {ys} eq in-head p₂      | no x₂  | no x₃ with x₃ in-head
diff-suc {T} {x} {x  ∷ xs} {ys} eq in-head p₂      | no x₂  | no x₃ | ()
diff-suc {T} {x} {x₁ ∷ xs} {ys} eq (in-tail p₁) p₂ | no x₂  | no x₃ =
  let f' = λ { in-head → x₃ in-head ; (in-tail x₄) → p₂ x₄} in
  app suc (trans (diff-suc {T} eq p₁ f') (app suc (app length (diff-flip x₁ x xs ys eq))))

module Unique {T : Set} (Item : T * -> T * -> Set) (eq-item : ∀ {w v}(a b : Item w v) -> a ≡ b ??) where

  data Unique {T : Set} : T * -> Set where
    u-ε : Unique ε
    u-∷ : {a : T} {as : T *} -> Unique as -> (as ∋ a -> Void) -> Unique (a ∷ as)

  pred-++ : ∀ {A n} {m : ℕ -> A} (xs ys : A *) ->
    (f : ∀ {j} -> xs ∋ m j -> j ≤ n) ->
    (g : ∀ {j} -> ys ∋ m j -> j ≤ n) ->
    (∀ {j} -> (xs ++ ys) ∋ m j -> j ≤ n)
  pred-++ ε ys f g p = g p
  pred-++ (x ∷ xs) ys f g in-head = f in-head
  pred-++ (x ∷ xs) ys f g (in-tail p) = pred-++ xs ys (f ∘ in-tail) g p

  _\\_ : ∀ {w n} -> (x x₁ : Item w n *) → Item w n *
  _\\_ = list-diff eq-item

  s-pcw₀ : ∀ {w v} {as bs : Item w v *} -> (P : _ -> Set) ->
    (∀ {i} -> i ∈ as -> P i) ->
    (∀ {i} -> i ∈ (as \\ bs) -> P i)
  s-pcw₀ {as = ε} {bs} P f ()
  s-pcw₀ {as = x ∷ as} {bs} P f p           with elem eq-item x bs
  s-pcw₀ {as = x ∷ as} {bs} P f p           | yes x₁ = s-pcw₀ P (f ∘ in-tail) p
  s-pcw₀ {as = x ∷ as} {bs} P f in-head     | no x₁ = f in-head
  s-pcw₀ {as = x ∷ as} {bs} P f (in-tail p) | no x₁ = s-pcw₀ P (f ∘ in-tail) p

  s-pcw : ∀ {w v} {as bs cs : Item w v *} -> (P : _ -> Set) ->
    (∀ {i} -> i ∈ as -> P i) ->
    (∀ {i} -> i ∈ bs -> P i) ->
    (∀ {i} -> i ∈ (as ++ (bs \\ cs)) -> P i)
  s-pcw {as = ε} P f g p = s-pcw₀ P g p
  s-pcw {as = x ∷ as} P f g in-head = f in-head
  s-pcw {as = x ∷ as} P f g (in-tail p) = s-pcw {as = as} P (f ∘ in-tail) g p

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

  no-include-\\ : ∀ {w n} -> {x : Item w n} (as bs : Item w n *) ->
    (as ∋ x -> Void) ->
    (as \\ bs) ∋ x -> Void
  no-include-\\ ε bs f p = f p
  no-include-\\ (x₁ ∷ as) bs f p                   with elem eq-item x₁ bs
  no-include-\\ (x₁ ∷ as) bs f p                   | yes x₂ = no-include-\\ as bs (f ∘ in-tail) p
  no-include-\\ (x₁ ∷ as) bs f in-head             | no x₂ = f in-head
  no-include-\\ {n} {x} (x₁ ∷ as) bs f (in-tail p) | no x₂ = no-include-\\ as (x₁ ∷ bs) (f ∘ in-tail) p

  idem-\\ : ∀ {w v} (as bs : Item w v *) ->
    (as \\ bs) \\ bs ≡ as \\ bs
  idem-\\ ε bs = refl
  idem-\\ (a ∷ as) bs with elem eq-item a bs
  idem-\\ (a ∷ as) bs | yes x = idem-\\ as bs
  idem-\\ (a ∷ as) bs | no x with elem eq-item a bs
  idem-\\ (a ∷ as) bs | no x | yes x₁ = void (x x₁)
  idem-\\ (a ∷ as) bs | no x | no x₁ = app (a ∷_) (idem-\\ as (a ∷ bs))

  no-include-\\₂ : ∀ {w n} -> {x : Item w n} (as bs : Item w n *) ->
    bs ∋ x ->
    (as \\ bs) ∋ x -> Void
  no-include-\\₂ ε bs p ()
  no-include-\\₂ (x₁ ∷ as) bs p q           with elem eq-item x₁ bs
  no-include-\\₂ (x₁ ∷ as) bs p q           | yes x₂ = no-include-\\₂ as bs p q
  no-include-\\₂ (x₁ ∷ as) bs p in-head     | no x₂ = void (x₂ p)
  no-include-\\₂ (x₁ ∷ as) bs p (in-tail q) | no x₂ = no-include-\\₂ as (x₁ ∷ bs) (in-tail p) q

  include-\\ : ∀ {w v as bs} {a : Item w v} ->
    a ∈ as ->
    a ∈ ((as \\ bs) ++ bs)
  include-\\ {as = ε} {bs} ()
  include-\\ {as = a ∷ as} {bs} {a₀} p           with elem eq-item a bs
  include-\\ {as = a ∷ as} {bs} {a₀} in-head     | yes x = in-r x
  include-\\ {as = a ∷ as} {bs} {a₀} (in-tail p) | yes x = include-\\ p
  include-\\ {as = a ∷ as} {bs} {a₀} in-head     | no x  = in-head
  include-\\ {as = a ∷ as} {bs} {a₀} (in-tail p) | no x  =
    case in-either _ (a ∷ bs) (include-\\ {as = as} {a ∷ bs} p) of
      λ { (r in-head) → in-head
        ; (r (in-tail x₂)) → in-r x₂
        ; (l x₂) → in-tail (in-l x₂)
        }

  unique-\\ : ∀ {w n} -> (as bs : Item w n *) ->
    Unique as ->
    Unique (as \\ bs)
  unique-\\ ε bs ua = ua
  unique-\\ (x ∷ as) bs (u-∷ ua f) with elem eq-item x bs
  unique-\\ (x ∷ as) bs (u-∷ ua f) | yes x₁ = unique-\\ as bs ua
  unique-\\ (x ∷ as) bs (u-∷ ua f) | no x₁ = u-∷ (unique-\\ as (x ∷ bs) ua) (no-include-\\ as (x ∷ bs) f)

  unique-\\₂ : ∀ {w n} -> (as bs : Item w n *) ->
    Unique (as \\ bs)
  unique-\\₂ ε bs = u-ε
  unique-\\₂ (x ∷ as) bs with elem eq-item x bs
  unique-\\₂ (x ∷ as) bs | yes x₁ = unique-\\₂ as bs
  unique-\\₂ (x ∷ as) bs | no x₁ = u-∷ (unique-\\₂ as (x ∷ bs)) (no-include-\\₂ as (x ∷ bs) in-head)

  tmp : {T : Set} {a : T} (as bs cs : T *) ->
    Unique ((a ∷ as) ++ cs) ->
    Unique (a ∷ bs) ->
    (∀ {b} -> as ∋ b -> bs ∋ b -> Void) ->
    (∀ {b} -> cs ∋ b -> bs ∋ b -> Void) ->
    Unique ((as ++ bs) ++ (a ∷ cs))
  tmp as bs cs (u-∷ uac x) (u-∷ ub x₃) f g =
    let x₁ = unique-++₂ as bs cs uac ub f g in
    unique-++-∷ (as ++ bs) cs x₁ (in-neither {bs = cs} (in-neither (not-in-l x) x₃) (not-in-r x))

  wf-pcw₀ : ∀ {w v r₁ m} {as ss rs : Item w v *}
    (f : ∀ {a} -> a ∈ as)
    (p : suc m ≡ suc (length (as \\ ss)))
    (q : Unique (r₁ ∷ (rs ++ ss))) ->
    m ≡ suc (length (as \\ (r₁ ∷ ss)))
  wf-pcw₀ f p q =
    trans (unsuc p) (sym (diff-suc eq-item f (eq-not q in-head)))

  wf-pcw₁ : ∀ {w v} -> ∀ r₁ -> (as rs ss : Item w v *) ->
    Unique as ->
    Unique ((r₁ ∷ rs) ++ ss) ->
    Unique ((rs ++ (as \\ (r₁ ∷ (ss ++ rs)))) ++ (r₁ ∷ ss))
  wf-pcw₁ r₁ as rs ss p q =
    let x₂ = as \\ (r₁ ∷ (ss ++ rs)) in
    let p₂ = unique-\\ as (r₁ ∷ (ss ++ rs)) p in
    let p₃ = u-∷ p₂ (no-include-\\₂ as _ in-head) in
    tmp rs x₂ ss q p₃
      (λ x → no-include-\\₂ as _ (in-tail (in-r x)))
      (λ x → no-include-\\₂ as _ (in-tail (in-l x)))

  wf-pcw₂ : ∀ {w v} -> (as bs : Item w v *) ->
    Unique bs ->
    Unique ((as \\ bs) ++ bs)
  wf-pcw₂ as bs ub = unique-++ (as \\ bs) bs (unique-\\₂ as bs) ub (no-include-\\₂ as bs)

  pcw₀ : ∀ {w v as bs} {b : Item w v} ->
    b ∈ as ->
    Unique (b ∷ bs) ->
    (suc ∘ length) (as \\ (b ∷ bs)) ≡ length (as \\ bs)
  pcw₀ {as = ε} {bs} {b} () q
  pcw₀ {as = a ∷ as} {bs} {b} p q with elem eq-item a (b ∷ bs)
  pcw₀ {as = a ∷ as} {bs} {b} p q | yes x₁ with elem eq-item a bs
  pcw₀ {as = a ∷ as} {bs} {a} in-head (u-∷ q x) | yes x₁ | yes x₂ = void (x x₂)
  pcw₀ {as = a ∷ as} {bs} {b} (in-tail p) q | yes x₁ | yes x₂ = pcw₀ p q
  pcw₀ {as = a ∷ as} {bs} {a} p q | yes in-head | no x₂ = refl
  pcw₀ {as = a ∷ as} {bs} {b} p q | yes (in-tail x₁) | no x₂ = void (x₂ x₁)
  pcw₀ {as = a ∷ as} {bs} {b} p q | no x₁  with elem eq-item a bs
  pcw₀ {as = a ∷ as} {bs} {b} p q | no x₁  | yes x₂ = void (x₁ (in-tail x₂))
  pcw₀ {as = a ∷ as} {bs} {a} in-head (u-∷ q q₀) | no x | no y = void (x in-head)
  pcw₀ {as = a ∷ as} {bs} {b} (in-tail p) (u-∷ q q₀) | no x | no y =
    let x₁ = diff-flip a b as bs eq-item in
    let y₁ = λ { in-head → void (x in-head) ; (in-tail z) → void (q₀ z)} in
    let x₂ = pcw₀ {as = as} {a ∷ bs} p (u-∷ (u-∷ q y) y₁) in
    let x₃ = app (suc ∘ length) x₁ in
    let x₄ = trans (sym x₂) x₃ in
    app suc (sym x₄)

  pcw₁ : ∀ {w v} (as bs cs : Item w v *) ->
     length (as \\ (cs ++ bs)) ≤ length (as \\ bs)
  pcw₁ ε bs cs = ≤₀
  pcw₁ (x ∷ as) bs cs with elem eq-item x bs
  pcw₁ (x ∷ as) bs cs | yes x₁ with elem eq-item x (cs ++ bs)
  pcw₁ (x ∷ as) bs cs | yes x₁ | yes x₂ = pcw₁ as bs cs
  pcw₁ (x ∷ as) bs cs | yes x₁ | no x₂ = void (x₂ (in-r x₁))
  pcw₁ (x ∷ as) bs cs | no x₁  with elem eq-item x (cs ++ bs)
  pcw₁ (x ∷ as) bs cs | no x₁  | yes x₂ with in-either cs bs x₂
  pcw₁ (x ∷ as) bs cs | no x₁  | yes x₂ | l x₃ =
    let x₁ = pcw₁ as (x ∷ bs) cs in
    let x₂ = diff-unord as (cs ++ (x ∷ bs)) (cs ++ bs) eq-item (in-lr₄ cs bs) (in-lr₅ cs bs x₃) in
    let x₃ = app length x₂ in
    let x₄ = in₂ (λ t -> t ≤ length (as \\ (x ∷ bs))) x₃ x₁ in
    ≤-suc x₄
  pcw₁ (x ∷ as) bs cs | no x₁  | yes x₂ | r x₃ = void (x₁ x₃)
  pcw₁ (x ∷ as) bs cs | no x₁  | no x₂ =
    let x₁ = diff-unord as (x ∷ (cs ++ bs)) (cs ++ (x ∷ bs)) eq-item (in-lr₂ cs bs) (in-lr₃ cs bs) in
    let x₂ = pcw₁ as (x ∷ bs) cs in
    let x₃ = in₂ (_≤ length (as \\ (x ∷ bs))) (app length (sym x₁)) x₂ in
    ≤ₛ x₃

  wf-pcw₃ : ∀ {w v r₁ m} {as ss rs : Item w v *}
    (f : ∀ {a} -> a ∈ as)
    (p : (suc ∘ length) (as \\ ss) ≤ suc m)
    (q : Unique (r₁ ∷ (rs ++ ss))) ->
    (suc ∘ length) (as \\ (r₁ ∷ (rs ++ ss))) ≤ m
  wf-pcw₃ {r₁ = r₁} {m} {as} {ss} {rs} f (≤ₛ p) q =
    let x₁ = pcw₁ as ss rs in
    let x₂ = ≤-trans x₁ p in
    let x₃ = pcw₀ {bs = rs ++ ss} (f {r₁}) q in
    in₂ (_≤ m) (sym x₃) x₂

module ε {T : Set} (decidₜ : (a b : T) -> a ≡ b ??) where

  .ε₁ : ∀ {a b} {x : T} -> a ++ (x ∷ b) ≡ ε -> Void
  ε₁ {ε} ()
  ε₁ {x ∷ a} ()

  .ε-0 : (as bs : T *) -> length (as ++ bs) ≡ length as + length bs
  ε-0 ε bs = refl
  ε-0 (x ∷ as) bs = app suc (ε-0 as bs)

  .ε-1 : (as bs : T *) -> as ≡ bs -> length as ≡ length bs
  ε-1 as as refl = refl

  .ε₂ : ∀ {a b} {x : T} -> a ++ (x ∷ b) ≡ b -> Void
  ε₂ {as} {bs} {x} p = +-imp (trans (trans (sym (ε-1 _ _ p)) (sym (ε-0 as _))) (+-comm {b = length as}))

  .ε₆ : ∀ a b {x y z : T} -> (x ∷ a) ++ (y ∷ b) ≡ (z ∷ b) -> Void
  ε₆ as bs p =
    let x₁ = unsuc (ε-1 _ _ p) in
    let x₂ = trans (sym x₁) (sym (ε-0 as (_ ∷ bs))) in
    let x₃ = trans x₂ (+-comm {suc (length bs)}) in
    +-imp x₃

  .ε₃ : ∀ {a b} {x y : T} -> (x ≡ y -> Void) -> a ++ (y ∷ b) ≡ (x ∷ b) -> Void
  ε₃ {ε} p refl = void (p refl)
  ε₃ {a ∷ as} {b} {x} {y} p q with decidₜ a x
  ε₃ {x ∷ as} {b} {x} {y} p q | yes refl = ε₂ (uncons _ _ q)
  ε₃ {a ∷ as} {b} {x} {y} p q | no x₁ = x₁ (uncons₂ a x q)

  .ε₄ : ∀ {t u w} {x y : T} -> t ++ (y ∷ u) ≡ x ∷ w -> x ≠ y -> Σ λ v -> v ++ (y ∷ u) ≡ w
  ε₄ {ε} {u} {v} p x₁ = void (x₁ (uncons₂ _ _ (sym p)))
  ε₄ {x ∷ t} {u} {v} p x₁ with uncons _ _ p
  ε₄ {x ∷ t} {u} {.(t ++ (_ ∷ u))} p x₁ | refl = σ t refl

  .ε₅ : ∀ {t u w} {x : T} -> t ++ (x ∷ u) ≡ x ∷ w -> w ≠ u -> Σ λ v -> v ++ (x ∷ u) ≡ w
  ε₅ {ε} p x = void (x (uncons _ _ (sym p)))
  ε₅ {t ∷ ts} p x with uncons _ _ p
  ε₅ {t ∷ ts} p x | refl = σ ts refl

++-+ : ∀ {T} -> (as bs : T *) -> length (as ++ bs) ≡ length as + length bs
++-+ ε bs = refl
++-+ (x ∷ as) bs = app suc (++-+ as bs)

length-≡ : ∀ {T} (as bs : T *) -> as ≡ bs -> length as ≡ length bs
length-≡ as as refl = refl

suc-+ : ∀ a b -> suc a + b ≡ b -> Void
suc-+ a zero ()
suc-+ a (suc b) p =
  let x₁ = unsuc p in
  let x₂ = trans (sym x₁) (+-comm {suc b} {a}) in
  let x₃ = trans x₂ (app suc (+-comm {a})) in
  suc-+ a b (sym x₃)

constrained-eq : ∀ {T} {as bs : T *} ->
  (Σ λ cs -> cs ++ as ≡ bs) ->
  (Σ λ cs -> cs ++ bs ≡ as) ->
  as ≡ bs
constrained-eq {as} {bs} (σ ε p₀) (σ q₁ q₀) = p₀
constrained-eq {as} {bs} (σ (x ∷ p₁) p₀) (σ ε q₀) = sym q₀
constrained-eq {as} {bs} (σ (x ∷ p₁) p₀) (σ (x₁ ∷ q₁) q₀)=
  let x₁ = ++-+ (x₁ ∷ q₁) _ in
  let x₂ = length-≡ _ bs q₀ in
  let x₃ = trans (sym x₂) (sym x₁) in
  let y₁ = ++-+ (x  ∷ p₁) _ in
  let y₂ = length-≡ _ _ p₀ in
  let y₃ = trans (sym y₂) (sym y₁) in
  let z₁ = app (suc (length q₁) +_) y₃ in
  let z₂ = trans (sym z₁) x₃ in
  let z₃ = sym (trans (sym z₂) (sym (+-assoc (suc (length q₁)) (suc (length p₁)) (length bs)))) in
  void (suc-+ (length q₁ + suc (length p₁)) (length bs) z₃)

Dec : Set -> Set
Dec T = (a b : T) -> a ≡ b ??

eq-× : ∀ {A B} -> Dec A -> Dec B -> Dec (A × B)
eq-× f g (a , a₁) (b , b₁) with f a b , g a₁ b₁
eq-× f g (a , a₁) (a , a₁) | yes refl , yes refl = yes refl
eq-× f g (a , a₁) (b , b₁) | yes x , no x₁ = no (λ {refl → x₁ refl})
eq-× f g (a , a₁) (b , b₁) | no x , g₁ = no λ {refl → x refl}

eq-×₃ : ∀ {A B C} -> Dec A -> Dec B -> Dec C -> Dec (A × B × C)
eq-×₃ f g h = eq-× (eq-× f g) h

eq-×₄ : ∀ {A B C D} -> Dec A -> Dec B -> Dec C -> Dec D -> Dec (A × B × C × D)
eq-×₄ f g h i = eq-×₃ (eq-× f g) h i

eq-* : ∀ {A} -> Dec A -> Dec (A *)
eq-* f ε ε = yes refl
eq-* f ε (b ∷ bs) = no λ ()
eq-* f (a ∷ as) ε = no λ ()
eq-* f (a ∷ as) (b ∷ bs) with f a b
eq-* f (a ∷ as) (a ∷ bs) | yes refl with eq-* f as bs
eq-* f (a ∷ as) (a ∷ bs) | yes refl | yes refl = yes refl
eq-* f (a ∷ as) (a ∷ bs) | yes refl | no x = no λ {refl → x refl}
eq-* f (a ∷ as) (b ∷ bs) | no x = no λ {refl → x refl}

eq-∣ : ∀ {A B} -> Dec A -> Dec B -> Dec (A ∣ B)
eq-∣ f g (r x) (r y) with g x y
eq-∣ f g (r x) (r y) | yes refl = yes refl
eq-∣ f g (r x) (r y) | no x₁ = no λ {refl → x₁ refl}
eq-∣ f g (r x) (l y) = no (λ ())
eq-∣ f g (l x) (r y) = no (λ ())
eq-∣ f g (l x) (l y) with f x y
eq-∣ f g (l x) (l y) | yes refl = yes refl
eq-∣ f g (l x) (l y) | no x₁ = no λ {refl → x₁ refl}
