open import ToddPrelude

ℂ : Set
ℂ = ℕ → 𝕓

head : ℂ → 𝕓
head α = α zero

tail : ℂ → ℂ
tail α = λ n → α (succ n)

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
(a =ℂ b) n = if (head a) =𝕓 (head b) then (next n) else ff where
  next : ℕ → 𝔹
  next zero = tt
  next (succ n) = ((tail a) =ℂ (tail b)) n

maxℂ : ℂ → ℂ → ℂ
maxℂ a b = λ n → if (a >ℂ b) n then a n else b n

