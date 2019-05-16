open import ToddPrelude
-- open import RealNumbers
open import Searchers
-- open import Lossers
open import CantorNumbers
-- open import Regressors

ℝ : Set
ℝ = ℂ

ℝ₀ : ℝ
ℝ₀ = ℂ₀

Φℝ : ℝ → ℝ → ℝ
Φℝ = Φℂ

_=ℝ_ : ℝ → ℝ → ℕ → 𝔹
_=ℝ_ = _=ℂ_

_<ℝ_ : ℝ → ℝ → Set
(a <ℝ b) = ∃ (λ n → (a <ℂ b) n ≡ tt)

perfection : ∀ r n ε → (ℝ₀ <ℂ ε) n ≡ tt → (Φℝ r r <ℂ ε) n ≡ tt
perfection r zero ε x = lem1b (r 0) &&! &&r x where
  lem1b : ∀ b → ((φ𝕓 b b) =𝕓 ₀) ≡ tt
  lem1b ₀ = refl
  lem1b ₁ = refl    
perfection r (succ n) ε x = ∨-elim (𝔹LEM ((Φℝ r r <ℂ ε) n)) (λ z → ||! (inr z))
                                          (λ z → ||! (inl ((lem1b (r (succ n)) &&! &&r (&&l (||lt x (MT (perfection r n ε) z)))) &&!
                                          lem2 r n ε (&&r (||lt x (MT (perfection r n ε) z)))))) where
  lem1a : ∀ b → (φ𝕓 b b) ≡ ₀
  lem1a ₀ = refl
  lem1a ₁ = refl
  lem1b : ∀ b → ((φ𝕓 b b) =𝕓 ₀) ≡ tt
  lem1b ₀ = refl
  lem1b ₁ = refl       
  lem2 : ∀ r n ε → (ℝ₀ =ℝ ε) n ≡ tt → (Φℝ r r =ℝ ε) n ≡ tt
  lem2 r₁ zero ε₁ x₁ = trans≡ (cong≡ (λ ■ → ■ =𝕓 head ε₁) (lem1a (r₁ zero))) x₁ where
  lem2 r₁ (succ n₁) ε₁ x₁ = trans≡ (cong≡ (λ ■ → ■ =𝕓 ε₁ (succ n₁)) (lem1a (r₁ (succ n₁)))) (&&l x₁) &&! lem2 r₁ n₁ ε₁ (&&r x₁)

γ : (X Y : Set) → Set
γ X Y = Y → (X → Y) → X

RegressionConvergence : {X Y : Set} (→ℝ : Y → ℝ) (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} →ℝ k f = ∀ ε → (ε₀ : ℝ₀ <ℝ ε)
                                                              → ∃ (λ (reg : γ X Y) → (Φℝ (→ℝ (f k)) (→ℝ (f (reg (f k) f))) <ℝ ε))

theorem : {X Y : Set} (S : Searchable X) (→ℝ : Y → ℝ) → ∀ k f → RegressionConvergence →ℝ k f
theorem {X} {Y} S →ℝ k f ε ε₀ = reg ⇒ (n ⇒ Searchable.def2 S p x₀pr) where
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  n : ℕ
  n = Π₀ ε₀
  reg : γ X Y
  reg = λ y m → ℰₓ (λ x → (Φℝ (→ℝ y) (→ℝ (m x)) <ℂ ε) n)
  p : X → 𝔹
  p = λ x → (Φℝ (→ℝ (f k)) (→ℝ (f x)) <ℂ ε) n
  x₀pr = k ⇒ perfection (→ℝ (f k)) (Π₀ ε₀) ε (Π₁ ε₀)

continuous : (F : ℝ → ℝ) → Set
continuous F = ∀ ε → (ℝ₀ <ℝ ε) → ∃ (λ δ → ((ℝ₀ <ℝ δ) ∧ (∀ (r₁ r₂ : ℝ) → ((Φℝ r₁ r₂ <ℝ δ) → (Φℝ (F r₁) (F r₂) <ℝ ε)))))

RegressionConvergenceNoise : {X Y : Set} (→ℝ : Y → ℝ) (ψ : Y → Y) (k : X) (f : X → Y) → Set
RegressionConvergenceNoise {X} {Y} →ℝ ψ k f = ∀ ε → (ε₀ : (ℝ₀ <ℝ ε))
                                              → ∃ (λ (reg : γ X Y) → Φℝ (Φℝ (→ℝ (ψ (f k))) (→ℝ (f k))) ((Φℝ (→ℝ (ψ (f k))) (→ℝ (f (reg (f k) f))))) <ℝ ε)

theorem-noise : {X Y : Set} (S : Searchable X) (→ℝ : Y → ℝ)
                      → ∀ k f → ∀ (ψ : Y → Y) → continuous (λ y → Φℝ (→ℝ (ψ (f k))) y)
                      → RegressionConvergenceNoise →ℝ ψ k f
theorem-noise {X} {Y} S →ℝ k f ψ C ε ε₀ = reg ⇒ ∧r (Π₁ (C ε ε₀)) (→ℝ oracle) (→ℝ regδ) Rconvδ where
  R : RegressionConvergence {X} {Y} →ℝ  k f
  R = theorem S →ℝ k f
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  δ : ℝ
  δ = Π₀ (C ε ε₀)
  δ₀ : (ℝ₀ <ℝ δ)
  δ₀ = ∧l (Π₁ (C ε ε₀))
  reg : γ X Y
  reg = Π₀ (R δ δ₀)
  oracle regδ noisy : Y
  oracle = f k
  regδ = f (reg oracle f)
  noisy = ψ oracle
  Rconvδ : ((Φℝ (→ℝ oracle) (→ℝ regδ)) <ℝ δ)
  Rconvδ = Π₁ (R δ δ₀)
