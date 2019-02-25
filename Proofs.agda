open import ToddPrelude
open import RealNumbers
open import Searchers
open import Lossers
open import Regressors

solis-wets : {X Y : Set} (ε : ℝ̂) (Φ : Y → Y → ℝ) (reg : Y → (X → Y) → X) → Set
solis-wets {X} {Y} ε Φ reg = (k : X) (f : X → Y) → (Φ (f k) (f (reg (f k) f)) <ℝ ε) ≡ tt

theorem : {X Y : Set} (ε : ℝ̂) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff)
             → (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ)
             → CompactSpace ℰ → LossSpace Φ
             → solis-wets ε Φ (buildReg ℰ Φ ε)
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

γℕℕconverges : ∀ n → (ε : ℝ̂) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → solis-wets ε Φℕ (γℕ,ℕ n ε)
γℕℕconverges n ε ε₀ = λ k f → theorem ε ε₀ (ℰℕ n) Φℕ {!!} ℕisLoss k f
