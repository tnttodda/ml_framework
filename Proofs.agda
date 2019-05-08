open import ToddPrelude
open import RealNumbers
open import Searchers
open import Lossers
-- open import Regressors

open RealNumber {ℝ} 𝕣

γ : (X Y : Set) → Set
γ X Y = Y → (X → Y) → X

RegressionConvergence : {X Y : Set} (→ℝ : Y → ℝ) (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} →ℝ k f = ∀ ε → (ε₀ : (ℝ₀ <ℝ ε) ≡ tt)
                                                              → ∃ (λ (reg : γ X Y) → (Φℝ (→ℝ (f k)) (→ℝ (f (reg (f k) f))) <ℝ ε) ≡ tt)

theorem : {X Y : Set} (S : Searchable X) (→ℝ : Y → ℝ) → ∀ k f → RegressionConvergence →ℝ k f
theorem {X} {Y} S →ℝ k f ε ε₀ = reg ⇒ (Searchable.def2 S p x₀pr) where
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  reg : γ X Y
  reg = λ y m → ℰₓ (λ x → (Φℝ (→ℝ y) (→ℝ (m x)) <ℝ ε))
  p : X → 𝔹
  p = λ x → Φℝ (→ℝ (f k)) (→ℝ (f x)) <ℝ ε
  x₀pr : ∃ (λ x → p x ≡ tt)
  x₀pr = k ⇒ trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.ref ℝLoss (→ℝ (f k)))) ε₀

continuous : (F : ℝ → ℝ) → Set
continuous F = ∀ ε → (ℝ₀ <ℝ ε) ≡ tt → ∃ (λ δ → (((ℝ₀ <ℝ δ) ≡ tt) ∧ (∀ (r₁ r₂ : ℝ) → ((Φℝ r₁ r₂ <ℝ δ) ≡ tt → (Φℝ (F r₁) (F r₂) <ℝ ε) ≡ tt))))

RegressionConvergenceNoise : {X Y : Set} (→ℝ : Y → ℝ) (ψ : Y → Y) (k : X) (f : X → Y) → Set
RegressionConvergenceNoise {X} {Y} →ℝ ψ k f = ∀ ε → (ε₀ : (ℝ₀ <ℝ ε) ≡ tt)
                                                                             → ∃ (λ (reg : γ X Y) → (Φℝ (→ℝ (ψ (f k))) (→ℝ (f (reg (f k) f))) <ℝ (ε +ℝ (Φℝ (→ℝ (ψ (f k))) (→ℝ (f k))))) ≡ tt)

theorem-noise : {X Y : Set} (S : Searchable X) (→ℝ : Y → ℝ)
                      → ∀ k f → ∀ (ψ : Y → Y) → continuous (λ y → Φℝ (→ℝ (ψ (f k))) y)
                      → RegressionConvergenceNoise →ℝ ψ k f
theorem-noise {X} {Y} S →ℝ k f ψ C ε ε₀ = reg ⇒ (Φℝrule noise-diff) where
  R : RegressionConvergence {X} {Y} →ℝ  k f
  R = theorem S →ℝ k f
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  δ : ℝ
  δ = Π₀ (C ε ε₀)
  δ₀ : (ℝ₀ <ℝ δ) ≡ tt
  δ₀ = ∧l (Π₁ (C ε ε₀))
  reg : γ X Y
  reg = Π₀ (R δ δ₀)
  oracle regδ noisy : Y
  oracle = f k
  regδ = f (reg oracle f)
  noisy = ψ oracle
  Rconvδ : ((Φℝ (→ℝ oracle) (→ℝ regδ)) <ℝ δ) ≡ tt
  Rconvδ = Π₁ (R δ δ₀)
  noise-diff : (Φℝ (Φℝ (→ℝ noisy) (→ℝ oracle)) (Φℝ (→ℝ noisy) (→ℝ regδ)) <ℝ ε) ≡ tt
  noise-diff = ∧r (Π₁ (C ε ε₀)) (→ℝ oracle) (→ℝ regδ) Rconvδ
