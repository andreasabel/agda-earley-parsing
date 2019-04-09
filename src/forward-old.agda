open import base
open import earley
open import forward

v-scanner-w₀ :
  {N T : Set} {n : ℕ} ->
  (G : Grammar N T) ->
  (a : T) ->
  (rs : Item N T *) ->
  (∀ {X j α β} -> rs ∋ (X , j , α , β) -> j ≤ n) ->
  (∀ {X j α β} -> scanner-w₀ G a rs ∋ (X , j , α , β) -> j ≤ suc n)
v-scanner-w₀ G a ε f ()
v-scanner-w₀ G a ((X , k , α , ε) ∷ rs) f p = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
v-scanner-w₀ G a ((X , k , α , l Y ∷ β) ∷ rs) f p = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
v-scanner-w₀ G a ((X , k , α , r b ∷ β) ∷ rs) f p with Grammar.decidₜ G a b
v-scanner-w₀ G a ((X , k , α , r a ∷ β) ∷ rs) f in-head     | yes refl = ≤-suc (f in-head)
v-scanner-w₀ G a ((X , k , α , r a ∷ β) ∷ rs) f (in-tail p) | yes refl = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p
...                                                         | no urefl = v-scanner-w₀ G a rs (λ z → f (in-tail z)) p

lookup-?-s : {N T : Set} {n : ℕ} ->
  (X : N) ->
  (rs : Item N T * ) ->
  (eq : (a b : N) -> a ≡ b ??) ->
  (∀ {Y j α β} -> rs ∋ (Y , j , α , β) -> j ≤ n) ->
  (∀ {Y j α β} -> lookup-? X rs eq ∋ (Y , j , α , β) -> j ≤ n)
lookup-?-s X ε eq f ()
lookup-?-s X ((Z , k , α , ε) ∷ rs) eq f p = lookup-?-s X rs eq (λ z → f (in-tail z)) p
lookup-?-s X ((Z , k , α , r a ∷ β) ∷ rs) eq f p = lookup-?-s X rs eq (λ z → f (in-tail z)) p
lookup-?-s X ((Z , k , α , l W ∷ β) ∷ rs) eq f p with eq X W
lookup-?-s X ((Z , k , α , l X ∷ β) ∷ rs) eq f in-head | yes refl = f in-head
lookup-?-s X ((Z , k , α , l X ∷ β) ∷ rs) eq f (in-tail p) | yes refl = lookup-?-s X rs eq (λ z → f (in-tail z)) p
lookup-?-s X ((Z , k , α , l W ∷ β) ∷ rs) eq f p | no x = lookup-?-s X rs eq (λ z → f (in-tail z)) p

complete-w₀-s : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
  (X : N) ->
  (w : WSet G n v) ->
  (k : ℕ) ->
  (∀ {Y j α β} -> complete-w₀ G X k w ∋ (Y , j , α , β) -> j ≤ n)
complete-w₀-s G X w zero = lookup-?-s X (Sₙ w) (Grammar.decidₙ G) {!!}
complete-w₀-s G X (start v rs) (suc k) ()
complete-w₀-s G X (step w rs) (suc k) p = ≤-suc (complete-w₀-s G X w k p)

predict-w₀-s : {N T : Set} (G : Grammar N T) {v : T *} {n : ℕ} ->
  (X : N) ->
  (w : WSet G n v) ->
  (∀ {Y j α β} -> predict-w₀ G X w ∋ (Y , j , α , β) -> j ≤ n) 
predict-w₀-s G X w {j = j} p with lookup X (Grammar.rules G) (Grammar.decidₙ G)
predict-w₀-s G X w {j = j} p | ls = local₀ ls p
  where
    local₀ : {N T : Set} {Y : N} {α β : (N ∣ T)*} {n : ℕ}
      (ls : (N ⟶ (N ∣ T)* ) *) ->
      map (predict-w₀-f n) ls ∋ (Y , j , α , β) ->
      j ≤ n
    local₀ ε ()
    local₀ ((x , x₁) ∷ ls) in-head = ≤-self j
    local₀ ((x , x₁) ∷ ls) (in-tail p) = local₀ ls p

pred-comp-w₀-s : {N T : Set} {n : ℕ} {v : T *} (G : Grammar N T) ->
  (w : WSet G n v) ->
  (X : N) (j : ℕ) (γ : (N ∣ T)*) ->
  (f : j ≤ n) ->
  (∀ {Y k α β} -> pred-comp-w₀ G w X j γ f ∋ (Y , k , α , β) -> k ≤ n)
pred-comp-w₀-s G w Y k ε f p = complete-w₀-s G Y w k f p
pred-comp-w₀-s G w Y k (r a ∷ β) f ()
pred-comp-w₀-s G w Y k (l Z ∷ β) f p = predict-w₀-s G Z w p

pred-comp-w₁-s : ∀ {N T n v} -> (G : Grammar N T) (w : WSet G n v) (m : ℕ) (rs : _) ->
  (f : ∀  {X j α β} -> rs ∋ (X , j , α , β) -> j ≤ n) ->
  (length rs + count-G G) ≤ m ->
  fst (pred-comp-w₁ m G w rs f) ≡ ε
pred-comp-w₁-s G w zero ε f p = refl
pred-comp-w₁-s G w zero (x ∷ rs) f ()
pred-comp-w₁-s G w (suc m) ε f p = refl
pred-comp-w₁-s {n = n} G w (suc m) (r₁@(X , j , α , β) ∷ rs) f (≤ₛ p) =
  let xₙ = pred-comp-w₁-s G (Wₙ w (r₁ ∷ Sₙ w) f') m (rs ++ x₂) (pred-++ rs x₂ (λ z → f (in-tail z)) g') {!!} in {!!}
  where
    _\\_ = list-diff (eq-item G)
    x₁ = pred-comp-w₀ G w X j α (f in-head)
    x₂ = (x₁ \\ (r₁ ∷ rs)) \\ Sₙ w

    f' : ∀ {X j α β} -> (r₁ ∷ Sₙ w) ∋ (X , j , α , β) -> j ≤ n
    f' in-head = f in-head
    f' (in-tail p) = Vₙ w p

    g' : ∀ {X j α β} -> x₂ ∋ (X , j , α , β) -> j ≤ n
    g' p = pred-\\ (eq-item G) (x₁ \\ (r₁ ∷ rs)) (Sₙ w) (pred-\\ (eq-item G) x₁ (r₁ ∷ rs) (pred-comp-w₀-s G w X j α (f in-head))) p
