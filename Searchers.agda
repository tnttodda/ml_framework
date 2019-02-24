open import ToddPrelude
open import CantorNumbers

record CompactSpace {X : Set} (Σ : (X → 𝔹) → X) : Set₁ where
  field
    def2 : (p : X → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt) → (p (Σ p)) ≡ tt

ℰ : (d : Set) → Set
ℰ d = (d → 𝔹) → d

Π : (d : Set) → Set
Π d = (d → 𝔹) → 𝔹

forsome forevery : {d : Set} → ℰ d → Π d
forsome s p = p (s p)
forevery s p = ! forsome s (λ x → ! p x)

ℰℕ : ℕ → ℰ ℕ
ℰℕ zero p = zero
ℰℕ (succ n) p = if (p n) then (n) else (ℰℕ n p)

head' : {X : ℕ → Set} → ((n : ℕ) → X n) → X zero
head' α = α zero
tail' : {X : ℕ → Set} → ((n : ℕ) → X n) → ((n : ℕ) → X (succ n))
tail' α n = α (succ n)

-- ℕisCompact : (n : ℕ) → CompactSpace (ℰℕ n)
-- CompactSpace.def2 (ℕisCompact n) p (w ⇒ x) = {!!} where 
--  x₀ : 𝔹
--  x₀ = p w
--  pr : ∀ n → (ℰℕ n p) ≡ w
--  pr zero = {!!}
--  pr (succ n) = {!!}

ℰ𝔹 : ℰ 𝔹
ℰ𝔹 p = if (p tt) then (tt) else (ff)

ℰ𝕓 : ℰ 𝕓
ℰ𝕓 p = if (p ₁) then (₁) else (₀)

ℰ× : {d d' : Set} → ℰ d → ℰ d' → ℰ (d × d')
ℰ× {d} {d'} e e' p = x , x' where
  x : d
  x = e (λ x → p (x , e' (λ x' → p (x , x'))))
  x' : d'
  x' = e' (λ x' → p (x , x'))

{-# TERMINATING #-}
ℰℕ→ : {d : Set} → (ℕ → ℰ d) → ℰ (ℕ → d)
ℰℕ→ {d} e p n = e n (λ x → q n x (ℰℕ→ (λ i → e (n +ℕ succ i)) (q n x))) where
  q : ℕ → d → (ℕ → d) → 𝔹
  q n x a = p (λ i → if (i <ℕ n) then (ℰℕ→ e p i)
                     else (if (i =ℕ n) then (x) else a (i −ℕ succ n)))

ℰℂ : ℰ ℂ
ℰℂ = ℰℕ→ (λ i → ℰ𝕓)
