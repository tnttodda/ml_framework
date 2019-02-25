open import ToddPrelude
open import CantorNumbers
open import RealNumbers

ℰ : (d : Set) → Set
ℰ d = (d → 𝔹) → d

record CompactSpace {X : Set} (Σ : ℰ X) : Set where
  field
    def2 : (p : X → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt) → (p (Σ p)) ≡ tt

Π : (d : Set) → Set
Π d = (d → 𝔹) → 𝔹

forsome forevery : {d : Set} → ℰ d → Π d
forsome s p = p (s p)
forevery s p = ! forsome s (λ x → ! p x)

ℰℕ : ℕ → ℰ ℕ
ℰℕ zero p = zero
ℰℕ (succ n) p = if (p n) then (n) else (ℰℕ n p)

ℕComp : ∀ n → (p : ℕ → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt) → (p (ℰℕ n p)) ≡ tt
ℕComp zero p (zero ⇒ x) = x
ℕComp zero p (succ w ⇒ x) = ⋆⟪TODO⟫⋆ -- This case is absurd; perhaps will be fixed with subsets
ℕComp (succ n) p w = ∨-elim (𝔹LEM (p n)) (case tt) (case ff) where
  x₀ : ℕ
  x₀ = if (p n) then n else (ℰℕ n p)
  lem : {b : 𝔹} → (p n ≡ b) → p (if b then n else ℰℕ n p) ≡ tt → p x₀ ≡ tt
  lem pr₁ pr₂ = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then n else (ℰℕ n p)) pr₁)) pr₂
  case : (b : 𝔹) → (p n ≡ b) → p x₀ ≡ tt
  case tt pr = lem pr pr
  case ff pr = lem pr (ℕComp n p w)

postulate ℕisCompact : ∀ n → CompactSpace (ℰℕ n)

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

ℰℝ : ℕ → ℰ ℝ
ℰℝ n = ℰ× (ℰℕ n) ℰℂ
