open import ToddPrelude
open import CantorNumbers
open import RealNumbers
open import Searchers
open import Lossers

γ : (X Y : Set) → Set
γ X Y = ℝ̂ → Y → (X → Y) → X

buildReg : {X Y : Set} (ℰ : (X → 𝔹) → X) → (Φ : Y → Y → ℝ) → γ X Y
buildReg ℰ Φ = λ ε y m → ℰ (λ x → (Φ (m x) y <ℝ ε))

γℕ,ℕ : ℕ → γ ℕ ℕ
γℕ,ℕ n = buildReg (ℰℕ n) Φℕ

γℕ×ℕ,ℕ→ℕ : ℕ → γ (ℕ × ℕ) (ℕ → ℕ)
γℕ×ℕ,ℕ→ℕ n = buildReg (ℰ× (ℰℕ n) (ℰℕ n)) (Φℕ→ℕ n)

γℂ,ℂ→ℂ : ℕ → γ ℂ (ℂ → ℂ)
γℂ,ℂ→ℂ n = buildReg ℰℂ (Φℂ→ℂ n)

test1a : ℕ
test1a = γℕ,ℕ 1000 (ℝ₁ , 5) 28 (λ x → x +ℕ 3)

test1b : ℕ
test1b = γℕ,ℕ 1000 ((3 , ℂ₀) , 5) 28 (λ x → x +ℕ 3)

test2 : ℕ × ℕ
test2 = γℕ×ℕ,ℕ→ℕ 6 (ℝ₁ , 0) (λ x → (3 *ℕ x) +ℕ 2) (λ m x → (π₁ m *ℕ x) +ℕ π₂ m)
