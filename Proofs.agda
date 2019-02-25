open import ToddPrelude
open import RealNumbers
open import Searchers
open import Lossers

solis-wets : {X Y : Set} (n : ℕ) (ε : ℝ) (Φ : Y → Y → ℝ) (reg : Y → (X → Y) → X) → Set
solis-wets {X} {Y} n ε Φ reg = (k : X) (f : X → Y) → (Φ (f k) (f (reg (f k) f)) <ℝ ε) n ≡ tt

theorem : {X Y : Set} (n : ℕ) (ε : ℝ) (ε₀ : (ℝ₀ =ℝ ε) n ≡ ff)
             → (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ)
             → CompactSpace ℰ → LossSpace Φ
             → solis-wets n ε Φ (λ y m → ℰ (λ x → (Φ (m x) y <ℝ ε) n))
theorem {X} {Y} n ε ε₀ ℰ Φ C L k f = firstly thirdly where
  p : X → 𝔹
  p = λ x → (Φ (f x) (f k) <ℝ ε) n
  k' : X
  k' = ℰ p
  firstly : (p k' ≡ tt) → ((Φ (f k) (f k') <ℝ ε) n ≡ tt)
  firstly r = trans≡ (cong≡ (λ ■ → (■ <ℝ ε) n) (LossSpace.sym L (f k) (f k'))) r
  secondly : ∃ (λ x → p x ≡ tt)
  secondly = k ⇒ trans≡ (cong≡ (λ ■ → (■ <ℝ ε) n) (LossSpace.ref L (f k))) (ℝ₀-bottom n ε ε₀)
  thirdly : p k' ≡ tt
  thirdly = CompactSpace.def2 C p secondly
