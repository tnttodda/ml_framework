open import ToddPrelude
open import RealNumbers
open import Searchers
-- open import Lossers
-- open import Regressors

record LossSpace {Y : Set} (Φ : Y → Y → ℝ) : Set₁ where
  field
    pos : ∀ y₁ y₂ → ((ℝ₀ <ℝ (Φ y₁ y₂)) ≡ tt) ∨ ((ℝ₀ =ℝ (Φ y₁ y₂)) ≡ tt)
    ref : ∀ y₁ → (Φ y₁ y₁ ≡ ℝ₀)
    sym : ∀ y₁ y₂ → (Φ y₁ y₂) ≡ (Φ y₂ y₁)

γ : (X Y : Set) → Set
γ X Y = ℝ → Y → (X → Y) → X
buildReg : {X Y : Set} (ℰ : (X → 𝔹) → X) → (Φ : Y → Y → ℝ) → γ X Y
buildReg ℰ Φ = λ ε y m → ℰ (λ x → (Φ (m x) y <ℝ ε))

RegressionConvergence : {X Y : Set} (ε : ℝ) (Φ : Y → Y → ℝ) (reg : Y → (X → Y) → X)
                                       (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} ε Φ reg k f = (Φ (f k) (f (reg (f k) f)) <ℝ ε) ≡ tt

solis-wets-noise : {X Y : Set} (ε : ℝ) (Φ : Y → Y → ℝ) (ψ : Y → Y) (reg : Y → (X → Y) → X)
                          (k : X) (f : X → Y) → Set
solis-wets-noise {X} {Y} ε Φ ψ reg k f = (Φ (ψ (f k)) (f (reg (f k) f)) <ℝ (ε +ℝ (Φ (ψ (f k)) (f k)))) ≡ tt

postulate Φℝ : ℝ → ℝ → ℝ
postulate Φℝrule : ∀ a b ε → (Φℝ a b <ℝ ε) ≡ tt → (a <ℝ (ε +ℝ b)) ≡ tt  

continuous : {Y : Set} (Φ₁ : Y → Y → ℝ) (f : Y → ℝ)
                  → (ε : ℝ) → (ℝ₀ =ℝ ε) ≡ ff → (k x : Y) → Set
continuous Φ₁ f ε ε₀ k x = ∃ (λ δ → (((Φ₁ k x <ℝ δ) ≡ tt) ∧ ((ℝ₀ =ℝ δ) ≡ ff))) → ((Φℝ (f k) (f x) <ℝ ε) ≡ tt)

theorem-noise : {X Y : Set} (ε : ℝ) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff)
                      → (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ) (ψ : Y → Y)
                      → Searchable X → LossSpace Φ
                      → (reg : ℝ → Y → (X → Y) → X)
                      → (k : X) (f : X → Y)
                      → continuous Φ (λ y → Φ (ψ (f k)) y) ε ε₀ (f (reg ε (f k) f)) (f k)
                      → RegressionConvergence ε Φ (reg ε) k f
                      → solis-wets-noise ε Φ ψ (reg ε) k f
theorem-noise {X} {Y} ε ε₀ ℰ₁ Φ ψ S L reg k f cont R = conclusion where
  noisy : Y 
  noisy = ψ (f k)
  regressed : Y
  regressed = f (reg ε (f k) f)
  normal : Y
  normal = f k
  fact : (Φ regressed normal <ℝ ε) ≡ tt
  fact = trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.sym L regressed normal)) R
  conjecture : (Φℝ (Φ noisy regressed) (Φ noisy normal) <ℝ ε) ≡ tt
  conjecture = cont (ε ⇒ (fact & ε₀))
  conclusion : (Φ noisy regressed <ℝ (ε +ℝ Φ noisy normal)) ≡ tt
  conclusion = Φℝrule (Φ noisy regressed) (Φ noisy normal) ε conjecture

theorem : {X Y : Set} (ε : ℝ) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff)
             → (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ)
             → CompactSpace ℰ → LossSpace Φ
             → (k : X) (f : X → Y)
             → RegressionConvergence ε Φ (buildReg ℰ Φ ε) k f
theorem {X} {Y} ε ε₀ ℰ Φ C L k f = firstly thirdly where
  p : X → 𝔹
  p = λ x → Φ (f x) (f k) <ℝ ε
  k' : X
  k' = ℰ p
  firstly : (p k' ≡ tt) → (Φ (f k) (f k') <ℝ ε) ≡ tt
  firstly r = trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.sym L (f k) (f k'))) r
  secondly : ∃ (λ x → p x ≡ tt)
  secondly = k ⇒ trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.ref L (f k))) (ℝ₀-bottom ε ε₀)
  thirdly : p k' ≡ tt
  thirdly = CompactSpace.def2 C p secondly

-- γℕℕconverges : ∀ n → (ε : ℝ̂) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → RegressionConvergence ε Φℕ (γℕ,ℕ n ε)
-- γℕℕconverges n ε ε₀ = λ k f → theorem ε ε₀ (ℰℕ n) Φℕ {!!} ℕisLoss k f
