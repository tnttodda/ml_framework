open import ToddPrelude

ℂ : Set
ℂ = ℕ → 𝕓

head : ℂ → 𝕓
head α = α zero

tail : ℂ → ℂ
tail α = λ n → α (succ n)

_::_ : {X : ℕ → Set} → X 0 → ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
(x :: α) 0 = x
(x :: α) (succ n) = α n

ℂ₀ ℂ₁ : ℂ
ℂ₀ n = ₀
ℂ₁ n = ₁

_>ℂ_ : ℂ → ℂ → ℕ → 𝔹
(a >ℂ b) n = if (head a) =𝕓 (head b) then (next n) else ((head a) =𝕓 ₁) where
  next : ℕ → 𝔹
  next zero = ff
  next (succ n) = ((tail a) >ℂ (tail b)) n

_<ℂ_ : ℂ → ℂ → ℕ → 𝔹
(a <ℂ b) n = if (head a) =𝕓 (head b) then (next n) else ((head b) =𝕓 ₁) where
  next : ℕ → 𝔹
  next zero = ff
  next (succ n) = ((tail a) <ℂ (tail b)) n

_=ℂ_ : ℂ → ℂ → ℕ → 𝔹
(a =ℂ b) zero = (head a) =𝕓 (head b)
(a =ℂ b) (succ n) = if (head a) =𝕓 (head b) then ((tail a) =ℂ (tail b)) n else ff

maxℂ : ℂ → ℂ → ℂ
maxℂ a b = λ n → if (a >ℂ b) n then a n else b n

{-# TERMINATING #-}

_+ℂ_ : ℂ → ℂ → ℕ → ℂ
(c₁ +ℂ c₂) n = (c₁ +'ℂ c₂) zero where
  _+'ℂ_ : ℂ → ℂ → ℕ → ℂ
  (a +'ℂ b) m = next (head a) (head b) where
    continue : ℂ
    continue = if m <ℕ n then ((tail a) +'ℂ (tail b)) (succ m) else (tail a) 
    next : 𝕓 → 𝕓 → ℂ
    next ₀ ₀ = ₀ :: continue
    next ₁ ₁ = ℂ₁
    next _ _ = ₁ :: continue



