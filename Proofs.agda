open import ToddPrelude
open import RealNumbers
open import Searchers
-- open import Lossers
-- open import Regressors

postulate ℝ : Set
postulate 𝕣 : RealNumber ℝ
open RealNumber {ℝ} 𝕣

record LossSpace {Y : Set} (Φ : Y → Y → ℝ) : Set where
  field
    pos : ∀ y₁ y₂ → ((ℝ₀ <ℝ (Φ y₁ y₂)) ≡ tt) ∨ ((ℝ₀ =ℝ (Φ y₁ y₂)) ≡ tt)
    ref : ∀ y₁ → (Φ y₁ y₁ ≡ ℝ₀)
    sym : ∀ y₁ y₂ → (Φ y₁ y₂) ≡ (Φ y₂ y₁)

γ : (X Y : Set) → Set
γ X Y = ℝ → Y → (X → Y) → X
buildReg : {X Y : Set} (ℰ : (X → 𝔹) → X) → (Φ : Y → Y → ℝ) → γ X Y
buildReg ℰ Φ = λ ε y m → ℰ (λ x → (Φ (m x) y <ℝ ε))

RegressionConvergence : {X Y : Set} (Φ : Y → Y → ℝ) (reg : Y → (X → Y) → X) (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} Φ reg k f = ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (f k) (f (reg (f k) f)) <ℝ ε) ≡ tt

solis-wets-noise : {X Y : Set} (Φ : Y → Y → ℝ) (ψ : Y → Y) (reg : Y → (X → Y) → X) (k : X) (f : X → Y) → Set
solis-wets-noise {X} {Y} Φ ψ reg k f = ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (ψ (f k)) (f (reg (f k) f)) <ℝ (ε +ℝ (Φ (ψ (f k)) (f k)))) ≡ tt

theorem : {X Y : Set} (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ)
             → CompactSpace ℰ → LossSpace Φ
             → (k : X) (f : X → Y)
             → ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (f k) (f (buildReg ℰ Φ ε (f k) f)) <ℝ ε) ≡ tt
theorem {X} {Y} ℰ Φ S L k f ε ε₀ = firstly thirdly  where
  p : X → 𝔹
  p = λ x → Φ (f x) (f k) <ℝ ε
  k' : X
  k' = ℰ p
  firstly : (p k' ≡ tt) → (Φ (f k) (f k') <ℝ ε) ≡ tt
  firstly r = trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.sym L (f k) (f k'))) r
  secondly : ∃ (λ x → p x ≡ tt)
  secondly = k ⇒ trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.ref L (f k))) (ℝ₀-bottom ε ε₀)
  thirdly : p k' ≡ tt
  thirdly = CompactSpace.def2 S p secondly

continuous : {Y : Set} (Φ : Y → Y → ℝ) (f : Y → ℝ) (k : Y) → Set
continuous Φ f k = ∀ ε → (ℝ₀ =ℝ ε) ≡ ff → ∃ (λ δ → ∀ x → (((ℝ₀ =ℝ δ) ≡ ff) ∧ ((Φ k x <ℝ δ) ≡ tt → (Φℝ (f k) (f x) <ℝ ε) ≡ tt)))

theorem-noise : {X Y : Set} (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ) (ψ : Y → Y)
                      → CompactSpace ℰ → LossSpace Φ
                      → (reg : Y → (X → Y) → X)
                      → (k : X) (f : X → Y)
                      → continuous Φ (λ y → Φ (ψ (f k)) y) (f k)
                      → RegressionConvergence Φ reg k f
                      → solis-wets-noise Φ ψ reg k f
theorem-noise {X} {Y} ℰ Φ ψ S L reg k f cont R ε ε₀ = Φℝrule noise-diff where
  noisy regressed normal : Y
  normal = f k
  regressed = f (reg normal f)
  noisy = ψ normal
  δ : ℝ
  δ = Π₀ (cont ε ε₀)
  δworks : ((ℝ₀ =ℝ δ) ≡ ff) ∧ ((Φ normal regressed <ℝ δ) ≡ tt → (Φℝ (Φ noisy normal) (Φ noisy regressed) <ℝ ε) ≡ tt)
  δworks = Π₁ (cont ε ε₀) regressed
  δreg : (Φ normal regressed <ℝ δ) ≡ tt
  δreg = R δ (∧l δworks)
  noise-diff : (Φℝ (Φ noisy normal) (Φ noisy regressed) <ℝ ε) ≡ tt
  noise-diff = ∧r δworks δreg
