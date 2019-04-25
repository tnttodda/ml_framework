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
(a <ℂ b) zero = if (head a) =𝕓 (head b) then ff else ((head b) =𝕓 ₁)
(a <ℂ b) (succ n) = if (head a) =𝕓 (head b) then (((tail a) <ℂ (tail b)) n) else ((head b) =𝕓 ₁)

_=ℂ_ : ℂ → ℂ → ℕ → 𝔹
(a =ℂ b) zero = (head a) =𝕓 (head b)
(a =ℂ b) (succ n) = if (head a) =𝕓 (head b) then ((tail a) =ℂ (tail b)) n else ff

maxℂ : ℂ → ℂ → ℂ
maxℂ a b = λ n → if (a >ℂ b) n then a n else b n

_+ℂ_ : ℂ → ℂ → ℕ → ℂ
(c₁ +ℂ c₂) max n = if (c₁ zero =𝕓 ₁) && (c₂ zero =𝕓 ₁) then ₁ else (calc max ₀) where
  +carry : 𝕓 → 𝕓 → 𝕓 → 𝕓 × 𝕓
  +carry ₁ ₁ ₁ = ₁ , ₁
  +carry ₁ ₁ ₀ = ₀ , ₁
  +carry ₁ ₀ ₁ = ₀ , ₁
  +carry ₀ ₁ ₁ = ₀ , ₁
  +carry ₀ ₀ ₀ = ₀ , ₀
  +carry _ _ _ = ₁ , ₀
  calc : ℕ → 𝕓 → 𝕓
  calc zero c = π₁ (+carry (c₁ n) (c₂ n) c)
  calc (succ m) c = if (succ m) =ℕ n then (π₁ (+carry (c₁ n) (c₂ n) c))
                                else calc m (π₂ (+carry (c₁ (succ m)) (c₂ (succ m)) c))

C1 C2 : ℂ
C1 = ₁ :: (₀ :: (₁ :: ℂ₁))
C2 = ₀ :: (₀ :: (₁ :: ℂ₁))
