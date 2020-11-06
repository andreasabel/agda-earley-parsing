open import base
open import earley

data T₀ : Set where
  s₀ : T₀
  a₀ : T₀

data N₀ : Set where
  S₀ : N₀
  A₀ : N₀

G₀ : Grammar N₀ T₀
G₀ = record
    { start = S₀
    ; rules = (A₀ ↦ r a₀ ∷ ε) ∷ (S₀ ↦ r s₀ ∷ l S₀ ∷ r s₀ ∷ ε) ∷ (S₀ ↦ l A₀ ∷ ε) ∷ ε
    ; valid = λ { S₀ → in₁ in₀ ; A₀ → in₀}
    ; decidₙ = λ { S₀ S₀ → yes refl ; S₀ A₀ → no (λ ()) ; A₀ S₀ → no (λ ()) ; A₀ A₀ → yes refl }
    ; decidₜ = λ { s₀ s₀ → yes refl ; s₀ a₀ → no (λ ()) ; a₀ s₀ → no (λ ()) ; a₀ a₀ → yes refl }
    }

t₀ : T₀ *
t₀ = s₀ ∷ a₀ ∷ s₀ ∷ ε

data ESet (N T : Set) : ℕ -> Set where
  eset₀ : ESet N T zero

  esetₙ : {m : ℕ} ->
    (e : ESet N T m) ->
    (s : (N ⟶ ((N ∣ T)* × (N ∣ T)* × ℕ))*) ->
    (c : N *) ->
    ESet N T (suc m)



insert : ∀ {N T m} ->
  (eq : _) ->
  (eq₂ : _) ->
  N ⟶ ((N ∣ T)* × (N ∣ T)* × ℕ) ->
  ESet N T (suc m) ->
  ESet N T (suc m)
insert eq eq₂ r₁@(X , (α ,       β , m)) (esetₙ e s c) with elem eq r₁ s
insert eq eq₂ r₁@(X , (α ,       β , m)) (esetₙ e s c) | yes x = esetₙ e s c
insert eq eq₂ r₁@(X , (α ,       ε , m)) (esetₙ e s c) | no x = esetₙ e (r₁ ∷ s) (X ∷ c)
insert eq eq₂ r₁@(X , (α , r a ∷ β , m)) (esetₙ e s c) | no x = esetₙ e (r₁ ∷ s) c
insert eq eq₂ r₁@(X , (α , l Y ∷ β , m)) (esetₙ e s c) | no x with elem eq₂ Y c
insert eq eq₂ r₁@(X , (α , l Y ∷ β , m)) (esetₙ e s c) | no x | yes x₁ = insert eq eq₂ (X , (α , β , m)) (esetₙ e (r₁ ∷ s) c)
insert eq eq₂ r₁@(X , (α , l Y ∷ β , m)) (esetₙ e s c) | no x | no x₁ = esetₙ e (r₁ ∷ s) c

-- data WSet {N T : Set} (G : Grammar N T) : ℕ -> T * -> Set where
--   start :
--     (v : T *) ->
--     (rs : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--     (∀ {X j α} -> rs ∋ ((X , j) ↦ α) -> j ≤ zero) ->
--     WSet G zero v
--
--   step : {a : T} {v : T *} {n : ℕ} ->
--     (w : WSet G n (a ∷ v)) ->
--     (rs : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--     (∀ {X j α} -> rs ∋ ((X , j) ↦ α) -> j ≤ suc n) ->
--     WSet G (suc n) v
--
-- Sₙ : {N T : Set} {G : Grammar N T} {v : T *} {n : ℕ} ->
--   WSet G n v ->
--   ((N × ℕ) ⟶ (N ∣ T *)) *
-- Sₙ (start v rs x) = rs
-- Sₙ (step w rs x) = rs
--
-- Sₛ : {N T : Set} {G : Grammar N T} {v : T *} {n : ℕ} ->
--   WSet G n v ->
--   ((N × ℕ) ⟶ (N ∣ T *)) * *
-- Sₛ (start v rs x) = rs ∷ ε
-- Sₛ (step w rs x) = rs ∷ Sₛ w
--
-- Vₙ : {N T : Set} {G : Grammar N T} {v : T *} {n : ℕ} ->
--   (w : WSet G n v) ->
--   ({X : N} {j : ℕ} {α : N ∣ T *} -> Sₙ w ∋ ((X , j) ↦ α) -> j ≤ n)
-- Vₙ (start v rs x) = x
-- Vₙ (step w rs x) = x
--
-- Wₙ : {N T : Set} {G : Grammar N T} {v : T *} {n : ℕ} ->
--   (w : WSet G n v) ->
--   (rs : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--   ({X : N} {j : ℕ} {α : N ∣ T *} -> rs ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   WSet G n v
-- Wₙ (start v rs x) rs₁ x₁ = start v rs₁ x₁
-- Wₙ (step w rs x) rs₁ x₁ = step w rs₁ x₁
--
-- scanner-w₀ : {N T : Set} (G : Grammar N T) ->
--   T ->
--   ((N × ℕ) ⟶ (N ∣ T *)) * ->
--   ((N × ℕ) ⟶ (N ∣ T *)) *
-- scanner-w₀ G a ε = ε
-- scanner-w₀ G a (((X , j) ↦ ε) ∷ rs) = scanner-w₀ G a rs
-- scanner-w₀ G a (((X , j) ↦ l Y ∷ α) ∷ rs) = scanner-w₀ G a rs
-- scanner-w₀ G a (((X , j) ↦ r b ∷ α) ∷ rs) with Grammar.decidₜ G a b
-- ...                                         | yes refl = ((X , j) ↦ α) ∷ (scanner-w₀ G a rs)
-- ...                                         | no x = scanner-w₀ G a rs
--
-- v-scanner-w₀ :
--   {N T : Set} {n : ℕ} ->
--   (G : Grammar N T) ->
--   (a : T) ->
--   (rs : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--   ({X : N} {j : ℕ} {α : N ∣ T *} -> rs ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   ({X : N} {j : ℕ} {α : N ∣ T *} -> scanner-w₀ G a rs ∋ ((X , j) ↦ α) -> j ≤ suc n)
-- v-scanner-w₀ G a ε f ()
-- v-scanner-w₀ G a (((X , k) ↦ ε) ∷ rs) f p = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
-- v-scanner-w₀ G a (((X , k) ↦ l Y ∷ α) ∷ rs) f p = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
-- v-scanner-w₀ G a (((X , k) ↦ r b ∷ α) ∷ rs) f p with Grammar.decidₜ G a b
-- v-scanner-w₀ G a (((X , k) ↦ r a ∷ α) ∷ rs) f in-head     | yes refl = ≤-suc (f in-head)
-- v-scanner-w₀ G a (((X , k) ↦ r a ∷ α) ∷ rs) f (in-tail p) | yes refl = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
-- ...                                                       | no urefl = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
--
-- scanner-w : {N T : Set} {n : ℕ} (G : Grammar N T) ->
--   (a : T) (v : T *) ->
--   WSet G n (a ∷ v) ->
--   WSet G (suc n) v
-- scanner-w G a v w = step w (scanner-w₀ G a (Sₙ w)) (v-scanner-w₀ G a (Sₙ w) (Vₙ w))
--
-- lookup-? : {N T : Set} -> N -> ((N × ℕ) ⟶ (N ∣ T *)) * -> ((a b : N) -> a ≡ b ??) -> ((N × ℕ) ⟶ (N ∣ T *)) *
-- lookup-? X ε eq = ε
-- lookup-? X (((Y , j) ↦ ε) ∷ rs) eq = lookup-? X rs eq
-- lookup-? X (((Y , j) ↦ r a ∷ α) ∷ rs) eq = lookup-? X rs eq
-- lookup-? X (((Y , j) ↦ l Z ∷ α) ∷ rs) eq with eq X Z
-- lookup-? X (((Y , j) ↦ l X ∷ α) ∷ rs) eq | yes refl = ((Y , j) ↦ α) ∷ lookup-? X rs eq
-- lookup-? X (((Y , j) ↦ l Z ∷ α) ∷ rs) eq | no x = lookup-? X rs eq
--
-- lookup-?-s : {N T : Set} {n : ℕ} ->
--   (X : N) ->
--   (rs : ((N × ℕ) ⟶ (N ∣ T *)) * ) ->
--   (eq : (a b : N) -> a ≡ b ??) ->
--   (∀ {Y j α} -> rs ∋ ((Y , j) ↦ α) -> j ≤ n) ->
--   (∀ {Y j α} -> lookup-? X rs eq ∋ ((Y , j) ↦ α) -> j ≤ n)
-- lookup-?-s X ε eq f ()
-- lookup-?-s X (((Z , k) ↦ ε) ∷ rs) eq f p = lookup-?-s X rs eq (λ z → f (in-tail z)) p
-- lookup-?-s X (((Z , k) ↦ r a ∷ β) ∷ rs) eq f p = lookup-?-s X rs eq (λ z → f (in-tail z)) p
-- lookup-?-s X (((Z , k) ↦ l W ∷ β) ∷ rs) eq f p with eq X W
-- lookup-?-s X (((Z , k) ↦ l X ∷ β) ∷ rs) eq f in-head | yes refl = f in-head
-- lookup-?-s X (((Z , k) ↦ l X ∷ β) ∷ rs) eq f (in-tail p) | yes refl = lookup-?-s X rs eq (λ z → f (in-tail z)) p
-- lookup-?-s X (((Z , k) ↦ l W ∷ β) ∷ rs) eq f p | no x = lookup-?-s X rs eq (λ z → f (in-tail z)) p
--
-- complete-w₀ : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
--   (X : N) ->
--   (j : ℕ) ->
--   j ≤ n ->
--   WSet G n v ->
--   ((N × ℕ) ⟶ (N ∣ T *)) *
-- complete-w₀ G {n = n} X zero    p w = lookup-? X (Sₙ w) (Grammar.decidₙ G)
-- complete-w₀ G X (suc j) () (start v rs x)
-- complete-w₀ G X (suc j) (≤ₛ p) (step w rs x) = complete-w₀ G X j p w
--
-- complete-w₀-s : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
--   (X : N) ->
--   (w : WSet G n v) ->
--   (k : ℕ) (p : k ≤ n) ->
--   (∀ {Y j α} -> complete-w₀ G X k p w ∋ ((Y , j) ↦ α) -> j ≤ n)
-- complete-w₀-s G X w zero p q = lookup-?-s X (Sₙ w) (Grammar.decidₙ G) (Vₙ w) q
-- complete-w₀-s G X (start v rs x) (suc k) () q
-- complete-w₀-s G X (step w rs x) (suc k) (≤ₛ p) q = ≤-suc (complete-w₀-s G X w k p q)
--
-- predict-w₀-f : {A B : Set} (n : ℕ) -> A ⟶ B -> (A × ℕ) ⟶ B
-- predict-w₀-f n (Y ↦ α) = (Y , n) ↦ α
--
-- predict-w₀ : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
--   (X : N) ->
--   WSet G n v ->
--   ((N × ℕ) ⟶ (N ∣ T *)) *
-- predict-w₀ G {n = n} X w =
--   let x₁ = lookup X (Grammar.rules G) (Grammar.decidₙ G) in
--   map (predict-w₀-f n) x₁
--
-- predict-w₀-s : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
--   (X : N) ->
--   (w : WSet G n v) ->
--   ((j : ℕ) (Y : N) (α : N ∣ T *) -> predict-w₀ G X w ∋ ((Y , j) ↦ α) -> j ≤ n)
-- predict-w₀-s G X w j Y α p with lookup X (Grammar.rules G) (Grammar.decidₙ G)
-- predict-w₀-s G X w j Y α p | ls = local₀ ls p
--   where
--     local₀ : {N T : Set} {Y : N} {α : N ∣ T *} {n : ℕ}
--       (ls : (N ⟶ (N ∣ T *)) *) ->
--       map (predict-w₀-f n) ls ∋ ((Y , j) ↦ α) ->
--       j ≤ n
--     local₀ ε ()
--     local₀ ((x ↦ x₁) ∷ ls) in-head = ≤-self j
--     local₀ ((x ↦ x₁) ∷ ls) (in-tail p) = local₀ ls p
--
-- pred-comp-w₀ : {N T : Set} {n : ℕ} {v : T *} ->
--   (G : Grammar N T) ->
--   (w : WSet G n v) ->
--   (X : N) (j : ℕ) (α : N ∣ T *) ->
--   j ≤ n ->
--   ((N × ℕ) ⟶ (N ∣ T *)) *
-- pred-comp-w₀ G w X j ε f = complete-w₀ G X j f w
-- pred-comp-w₀ G w X j (r a ∷ α) f = ε
-- pred-comp-w₀ G w X j (l Y ∷ α) f = predict-w₀ G Y w
--
-- pred-comp-w₀-s : {N T : Set} {n : ℕ} {v : T *} (G : Grammar N T) ->
--   (w : WSet G n v) ->
--   (X : N) (j : ℕ) (α : N ∣ T *) ->
--   (f : j ≤ n) ->
--   (∀ {Y k β} -> pred-comp-w₀ G w X j α f ∋ ((Y , k) ↦ β) -> k ≤ n)
-- pred-comp-w₀-s G w Y k ε f p = complete-w₀-s G Y w k f p
-- pred-comp-w₀-s G w Y k (r a ∷ β) f ()
-- pred-comp-w₀-s G w Y k (l Z ∷ β) f {W} {o} {γ} p = predict-w₀-s G Z w o W γ p
--
-- eq-sentence : {N T : Set} (G : Grammar N T) ->
--   (a b : N ∣ T *) ->
--   a ≡ b ??
-- eq-sentence G ε ε = yes refl
-- eq-sentence G        ε  (x   ∷ β) = no (λ ())
-- eq-sentence G (x   ∷ α)        ε  = no (λ ())
-- eq-sentence G (r a ∷ α) (r b ∷ β) with Grammar.decidₜ G a b
-- eq-sentence G (r a ∷ α) (r a ∷ β) | yes refl with eq-sentence G α β
-- eq-sentence G (r a ∷ α) (r a ∷ α) | yes refl | yes refl = yes refl
-- eq-sentence G (r a ∷ α) (r a ∷ β) | yes refl | no x = no (λ {refl → x refl})
-- eq-sentence G (r a ∷ α) (r b ∷ β) | no x = no (λ {refl → x refl})
-- eq-sentence G (r a ∷ α) (l B ∷ β) = no (λ ())
-- eq-sentence G (l A ∷ α) (r b ∷ β) = no (λ ())
-- eq-sentence G (l A ∷ α) (l B ∷ β) with Grammar.decidₙ G A B
-- eq-sentence G (l A ∷ α) (l A ∷ β) | yes refl with eq-sentence G α β
-- eq-sentence G (l A ∷ α) (l A ∷ α) | yes refl | yes refl = yes refl
-- eq-sentence G (l A ∷ α) (l A ∷ β) | yes refl | no x = no (λ {refl → x refl})
-- eq-sentence G (l A ∷ α) (l B ∷ β) | no x = no (λ {refl → x refl})
--
-- eq-rules : {N T : Set} (G : Grammar N T) -> (a b : (N × ℕ) ⟶ (N ∣ T *)) -> a ≡ b ??
-- eq-rules G ((X , j) ↦ α) ((Y , k) ↦ β) with eq-ℕ j k
-- eq-rules G ((X , j) ↦ α) ((Y , j) ↦ β) | yes refl with Grammar.decidₙ G X Y
-- eq-rules G ((X , j) ↦ α) ((X , j) ↦ β) | yes refl | yes refl with eq-sentence G α β
-- eq-rules G ((X , j) ↦ α) ((X , j) ↦ α) | yes refl | yes refl | yes refl = yes refl
-- eq-rules G ((X , j) ↦ α) ((X , j) ↦ β) | yes refl | yes refl | no x = no (λ {refl → x refl})
-- eq-rules G ((X , j) ↦ α) ((Y , j) ↦ β) | yes refl | no x = no (λ {refl → x refl})
-- eq-rules G ((X , j) ↦ α) ((Y , k) ↦ β) | no x = no (λ {refl → x refl})
--
-- pred-++ : ∀ {A B n} (xs ys : ((A × ℕ) ⟶ B) *) ->
--   (f : forall {X j α} -> xs ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   (g : forall {X j α} -> ys ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   (∀ {X j α} -> (xs ++ ys) ∋ ((X , j) ↦ α) -> j ≤ n)
-- pred-++ ε ys f g p = g p
-- pred-++ (x ∷ xs) ys f g in-head = f in-head
-- pred-++ (x ∷ xs) ys f g (in-tail p) = pred-++ xs ys (λ z → f (in-tail z)) g p
--
-- pred-\\ : ∀ {N T n} (G : Grammar N T) (xs ys : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--   (f : forall {X j α} -> xs ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   (∀ {X j α} -> (list-diff (eq-rules G) xs ys) ∋ ((X , j) ↦ α) -> j ≤ n)
-- pred-\\ G ε ys f p = f p
-- pred-\\ G (x ∷ xs) ys f p           with elem (eq-rules G) x ys
-- pred-\\ G (x ∷ xs) ys f p           | yes x₃ = pred-\\ G xs ys (λ z → f (in-tail z)) p
-- pred-\\ G (x ∷ xs) ys f in-head     | no x₃ = f in-head
-- pred-\\ G (x ∷ xs) ys f (in-tail p) | no x₃ = pred-\\ G xs ys (λ z → f (in-tail z)) p
--
-- pred-comp-w₁ : {N T : Set} {n : ℕ} {v : T *} ->
--   (m : ℕ) ->
--   (G : Grammar N T) ->
--   (w : WSet G n v) ->
--   (rs : ((N × ℕ) ⟶ (N ∣ T *)) *) ->
--   (∀ {X j α} -> rs ∋ ((X , j) ↦ α) -> j ≤ n ) ->
--   (((N × ℕ) ⟶ (N ∣ T *)) *) × WSet G n v
-- pred-comp-w₁ {N} {T} {n} zero G w rs f = rs , w
-- pred-comp-w₁ {N} {T} {n} (suc m) G w ε f = ε , w
-- pred-comp-w₁ {N} {T} {n} (suc m) G w (r₁@((X , j) ↦ α) ∷ rs) f =
--   pred-comp-w₁ m G (Wₙ w (r₁ ∷ (Sₙ w)) f') (rs ++ x₂) (pred-++ rs x₂ (λ z → f (in-tail z)) g')
--   where
--     _\\_ = list-diff (eq-rules G)
--     x₁ = pred-comp-w₀ G w X j α (f in-head)
--     x₂ = (x₁ \\ (r₁ ∷ rs)) \\ Sₙ w
--
--     f' : ∀ {X j α} -> (r₁ ∷ Sₙ w) ∋ ((X , j) ↦ α) -> j ≤ n
--     f' in-head = f in-head
--     f' (in-tail p) = Vₙ w p
--
--     g' : ∀ {X j α} -> x₂ ∋ ((X , j) ↦ α) -> j ≤ n
--     g' p = pred-\\ G (x₁ \\ (r₁ ∷ rs)) (Sₙ w) (pred-\\ G x₁ (r₁ ∷ rs) (pred-comp-w₀-s G w X j α (f in-head))) p
--
-- pred-comp-w₁-s : ∀ {N T n v} -> (G : Grammar N T) (w : WSet G n v) (m : ℕ) (rs : _) ->
--   (f : ∀  {X j α} -> rs ∋ ((X , j) ↦ α) -> j ≤ n) ->
--   (length rs + count-G G) ≤ m ->
--   fst (pred-comp-w₁ m G w rs f) ≡ ε
-- pred-comp-w₁-s G w zero ε f p = refl
-- pred-comp-w₁-s G w zero (x ∷ rs) f ()
-- pred-comp-w₁-s G w (suc m) ε f p = refl
-- pred-comp-w₁-s {n = n} G w (suc m) (r₁@((X , j) ↦ α) ∷ rs) f (≤ₛ p) =
--   let xₙ = pred-comp-w₁-s G (Wₙ w (r₁ ∷ Sₙ w) f') m (rs ++ x₂) (pred-++ rs x₂ (λ z → f (in-tail z)) g') {!!} in {!!}
--   where
--     _\\_ = list-diff (eq-rules G)
--     x₁ = pred-comp-w₀ G w X j α (f in-head)
--     x₂ = (x₁ \\ (r₁ ∷ rs)) \\ Sₙ w
--
--     f' : ∀ {X j α} -> (r₁ ∷ Sₙ w) ∋ ((X , j) ↦ α) -> j ≤ n
--     f' in-head = f in-head
--     f' (in-tail p) = Vₙ w p
--
--     g' : ∀ {X j α} -> x₂ ∋ ((X , j) ↦ α) -> j ≤ n
--     g' p = pred-\\ G (x₁ \\ (r₁ ∷ rs)) (Sₙ w) (pred-\\ G x₁ (r₁ ∷ rs) (pred-comp-w₀-s G w X j α (f in-head))) p
--
--
-- pred-comp-w : ∀ {N T n v} ->
--   (G : Grammar N T) ->
--   WSet G n v ->
--   WSet G n v
-- pred-comp-w G w = snd (pred-comp-w₁ m G (Wₙ w ε λ ()) (Sₙ w) (Vₙ w))
--   where
--     m = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
--
-- step-w : ∀ {N T n a v} ->
--   (G : Grammar N T) ->
--   WSet G n (a ∷ v) ->
--   WSet G (suc n) v
-- step-w {a = a} {v = v} G w = scanner-w G a v (pred-comp-w G w)
--
-- parse : ∀ {N T n v} ->
--   (G : Grammar N T) ->
--    WSet G n v ->
--    WSet G (length v + n) ε
-- parse {v = ε} G w = pred-comp-w G w
-- parse {n = n} {v = x ∷ v} G w = f +ₛ (parse G (step-w G w))
--   where
--     f : ∀ {v j k} -> j ≡ k -> WSet G j v -> WSet G k v
--     f refl w = w
