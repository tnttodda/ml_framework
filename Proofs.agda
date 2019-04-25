open import ToddPrelude
open import RealNumbers
open import Searchers
open import Lossers
-- open import Regressors

open RealNumber {ℝ} 𝕣

γ : (X Y : Set) → Set
γ X Y = Y → (X → Y) → X

buildReg : {X Y : Set} (ℰ : (X → 𝔹) → X) → (Φ : Y → Y → ℝ) → ℝ → γ X Y
buildReg ℰ Φ ε = λ y m → ℰ (λ x → (Φ (m x) y <ℝ ε))

RegressionConvergence : {X Y : Set} (L : LossSpace Y) (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} L k f = ∀ ε → (ε₀ : (ℝ₀ <ℝ ε) ≡ tt)
                                                              → ∃ (λ (reg : γ X Y) → ((LossSpace.Φ L) (f k) (f (reg (f k) f)) <ℝ ε) ≡ tt)
                                                              
theorem : {X Y : Set} (S : Searchable X) (L : LossSpace Y) → ∀ k f → RegressionConvergence L k f
theorem {X} {Y} S L k f ε ε₀ = buildReg ℰₓ Φ ε ⇒ firstly thirdly where
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  Φ : Y → Y → ℝ
  Φ = LossSpace.Φ L
  p : X → 𝔹
  p = λ x → Φ (f x) (f k) <ℝ ε
  k' : X
  k' = ℰₓ p
  firstly : (p k' ≡ tt) → (Φ (f k) (f k') <ℝ ε) ≡ tt
  firstly r = trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.sym L (f k) (f k'))) r
  secondly : ∃ (λ x → p x ≡ tt)
  secondly = k ⇒ trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.ref L (f k))) ε₀
  thirdly : p k' ≡ tt
  thirdly = Searchable.def2 S p (Π₀ secondly) (Π₁ secondly)

continuous : {Y Z : Set} (Φ₁ : Y → Y → ℝ) (Φ₂ : Z → Z → ℝ) (F : Y → Z) → Set
continuous {Y} {Z} Φ₁ Φ₂ F = ∀ ε → (ℝ₀ <ℝ ε) ≡ tt
                                                → ∃ (λ δ → (((ℝ₀ <ℝ δ) ≡ tt) ∧ (∀ (y₁ y₂ : Y) → ((Φ₁ y₁ y₂ <ℝ δ) ≡ tt → (Φ₂ (F y₁) (F y₂) <ℝ ε) ≡ tt))))

RegressionConvergenceNoise : {X Y : Set} (Φ : Y → Y → ℝ) (ψ : Y → Y) (k : X) (f : X → Y) → Set
RegressionConvergenceNoise {X} {Y} Φ ψ k f = ∀ ε → (ε₀ : (ℝ₀ <ℝ ε) ≡ tt)
                                                                             → ∃ (λ (reg : γ X Y) → (Φ (ψ (f k)) (f (reg (f k) f)) <ℝ (ε +ℝ (Φ (ψ (f k)) (f k)))) ≡ tt)

theorem-noise : {X Y : Set}  (S : Searchable X) (L : LossSpace Y)
                      → ∀ k f → ∀ (ψ : Y → Y) → continuous {Y} {ℝ} (LossSpace.Φ L) Φℝ (λ y → (LossSpace.Φ L) (ψ (f k)) y)
                      → RegressionConvergenceNoise (LossSpace.Φ L) ψ k f
theorem-noise {X} {Y} S L k f ψ C ε ε₀ = reg ⇒ (Φℝrule noise-diff) where
  R : RegressionConvergence {X} {Y} L k f
  R = theorem S L k f
  ℰₓ : (X → 𝔹) → X
  ℰₓ = Searchable.ε S
  Φ : Y → Y → ℝ
  Φ = LossSpace.Φ L
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
  Rconvδ : ((Φ oracle regδ) <ℝ δ) ≡ tt
  Rconvδ = Π₁ (R δ δ₀)
  noise-diff : (Φℝ (Φ noisy oracle) (Φ noisy regδ) <ℝ ε) ≡ tt
  noise-diff = ∧r (Π₁ (C ε ε₀)) oracle regδ Rconvδ
