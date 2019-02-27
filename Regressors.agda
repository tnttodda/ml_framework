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

γℕ,ℕ→ℕ : ℕ → γ ℕ (ℕ → ℕ)
γℕ,ℕ→ℕ n = buildReg (ℰℕ n) (Φℕ→ℕ n)

γℕ×ℕ,ℕ : ℕ → γ (ℕ × ℕ) ℕ
γℕ×ℕ,ℕ n = buildReg (ℰ× (ℰℕ n) (ℰℕ n)) Φℕ

γℕ×ℕ,ℕ→ℕ : ℕ → γ (ℕ × ℕ) (ℕ → ℕ)
γℕ×ℕ,ℕ→ℕ n = buildReg (ℰ× (ℰℕ n) (ℰℕ n)) (Φℕ→ℕ n)

γℂ,ℂ : γ ℂ ℂ
γℂ,ℂ = buildReg ℰℂ Φℂ

γℂ,ℂ→ℂ : ℕ → γ ℂ (ℂ → ℂ)
γℂ,ℂ→ℂ n = buildReg ℰℂ (Φℂ→ℂ n)

test1a : ℕ -- Should return 25
test1a = γℕ,ℕ 10000 (ℝ₁ , 0) 28 (λ x → x +ℕ 3)

test1b : ℕ -- Should return ≈25
test1b = γℕ,ℕ 100000 ((3 , ℂ₀) , 0) 28 (λ x → x +ℕ 3)

test1c : ℕ -- Should return 16
test1c = γℕ,ℕ 100000 (ℝ₁ , 0) 128 (λ x → x *ℕ 8) 

test1d : ℕ -- Should return 8
test1d = γℕ,ℕ→ℕ 200 (ℝ₁ , 0) (λ x → x *ℕ 8) (λ m x → x *ℕ m) 

test2a : ℕ × ℕ -- Should return 8 , _
test2a = γℕ×ℕ,ℕ 5000 (ℝ₁ , 0) 8 (λ x → π₂ x)

test2b : ℕ × ℕ -- Should return 8 , 0
test2b = γℕ×ℕ,ℕ 15 (ℝ₁ , 0) 8 (λ x → π₁ x +ℕ π₂ x) 

test2c : ℕ × ℕ -- Should return _ , 7
test2c = γℕ×ℕ,ℕ→ℕ 25 (ℝ₁ , 0) (λ x → (7 *ℕ x) +ℕ 7) (λ m x → (π₂ m *ℕ x) +ℕ π₂ m)

test2d : ℕ × ℕ -- Should return 3 , 4
test2d = γℕ×ℕ,ℕ→ℕ 6 (ℝ₁ , 0) (λ x → (3 *ℕ x) +ℕ 4) (λ m x → (π₁ m *ℕ x) +ℕ π₂ m)

nought-point-125 : ℂ -- 0.125
nought-point-125 n = if (n <ℕ 4) then ₀ else ₁

test3a : ℂ -- Should return 10100____....
test3a = γℂ,ℂ ((zero , nought-point-125) , 4) (λ x → ₁)
               (λ c n → if ((n =ℕ 0) ∣∣ (n =ℕ 2)) then (if c n =𝕓 ₁ then ₁ else ₀) else (if c n =𝕓 ₀ then ₁ else ₀))
