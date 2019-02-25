open import ToddPrelude
open import CantorNumbers
open import RealNumbers
open import Searchers

record LossSpace {Y : Set} (Φ : Y → Y → ℝ) : Set₁ where
  field
    pos : ∀ y₁ y₂ ε → ((ℝ₀ <ℝ (Φ y₁ y₂ , ε)) ≡ tt) ∨ ((ℝ₀ =ℝ (Φ y₁ y₂ , ε)) ≡ tt)
    ref : ∀ y₁ → (Φ y₁ y₁ ≡ ℝ₀)
    sym : ∀ y₁ y₂ → (Φ y₁ y₂) ≡ (Φ y₂ y₁)

Φℕ : ℕ → ℕ → ℝ
Φℕ n m = maxℕ (n −ℕ m) (m −ℕ n) , ℂ₀

ℕisLoss : LossSpace Φℕ
LossSpace.pos ℕisLoss zero zero ε = inr (lem ε) where
  lem : ∀ ε → (ℝ₀ =ℝ (Φℕ zero zero , ε)) ≡ tt
  lem zero = refl
  lem (succ ε) = lem ε
LossSpace.pos ℕisLoss zero (succ y₂) ε = inl refl
LossSpace.pos ℕisLoss (succ y₁) zero ε = inl refl
LossSpace.pos ℕisLoss (succ y₁) (succ y₂) ε = LossSpace.pos ℕisLoss y₁ y₂ ε
LossSpace.ref ℕisLoss zero = refl
LossSpace.ref ℕisLoss (succ y₁) = cong≡ (λ ■ → ■ , ℂ₀) (lem y₁) where
  lem : ∀ y₁ → maxℕ (y₁ −ℕ y₁) (y₁ −ℕ y₁) ≡ zero
  lem zero = refl
  lem (succ y₁) = lem y₁
LossSpace.sym ℕisLoss zero zero = refl
LossSpace.sym ℕisLoss zero (succ y₂) = refl
LossSpace.sym ℕisLoss y₁ y₂ = cong≡ (λ ■ → ■ , ℂ₀) (lem y₁ y₂) where
  lem : ∀ y₁ y₂ → maxℕ (y₁ −ℕ y₂) (y₂ −ℕ y₁) ≡ maxℕ (y₂ −ℕ y₁) (y₁ −ℕ y₂)
  lem zero zero = refl
  lem zero (succ y₂) = refl
  lem (succ y₁) zero = refl
  lem (succ y₁) (succ y₂) = lem y₁ y₂

Φ𝔹 : 𝔹 → 𝔹 → ℝ
Φ𝔹 ff ff = ℝ₀
Φ𝔹 tt tt = ℝ₀
Φ𝔹 _ _ = ℝ₁

φ𝕓 : 𝕓 → 𝕓 → 𝕓
φ𝕓 ₀ ₀ = ₀
φ𝕓 ₁ ₁ = ₀
φ𝕓 _ _ = ₁

Φ𝕓 : 𝕓 → 𝕓 → ℝ
Φ𝕓 a b = zero , λ n → φ𝕓 a b

𝕓isLoss : LossSpace Φ𝕓
LossSpace.pos 𝕓isLoss ₀ ₀ ε = inr (lem ε) where
  lem : ∀ ε → (ℝ₀ =ℝ (Φ𝕓 ₀ ₀ , ε)) ≡ tt
  lem zero = refl
  lem (succ ε) = lem ε
LossSpace.pos 𝕓isLoss ₀ ₁ ε = inl refl
LossSpace.pos 𝕓isLoss ₁ ₀ ε = inl refl
LossSpace.pos 𝕓isLoss ₁ ₁ ε = inr (lem ε) where
  lem : ∀ ε → (ℝ₀ =ℝ (Φ𝕓 ₁ ₁ , ε)) ≡ tt
  lem zero = refl
  lem (succ ε) = lem ε  
LossSpace.ref 𝕓isLoss ₀ = refl
LossSpace.ref 𝕓isLoss ₁ = refl
LossSpace.sym 𝕓isLoss ₀ ₀ = refl
LossSpace.sym 𝕓isLoss ₀ ₁ = refl
LossSpace.sym 𝕓isLoss ₁ ₀ = refl
LossSpace.sym 𝕓isLoss ₁ ₁ = refl

Φℂ : ℂ → ℂ → ℝ
Φℂ a b = 0 , λ n → φ𝕓 (a n) (b n)

postulate ℂisLoss : LossSpace Φℂ

isNormAt : (ℂ → ℂ) → ℂ → ℕ → 𝔹
isNormAt f c n = forevery ℰℂ (λ c' → maxℂ (f c) (f c') n =𝕓 (f c) n)

isNorm : (ℂ → ℂ) → ℂ → ℕ → 𝔹
isNorm f c zero = isNormAt f c zero
isNorm f c (succ e) = isNormAt f c (succ e) && isNorm f c e 

supNorm : (ℂ → ℂ) → ℕ → ℂ
supNorm f e n = ℰℂ (λ c → isNorm f c e) n

Φℂ→ℂ : ℕ → (ℂ → ℂ) → (ℂ → ℂ) → ℝ
Φℂ→ℂ n f g = zero , maxℂ (supNorm f n) (supNorm g n)

Φℕ→ℕ : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ
Φℕ→ℕ zero f g = (f zero −ℕ g zero) , ℂ₀
Φℕ→ℕ (succ n) f g = ((f n −ℕ g n) +ℕ π₁ (Φℕ→ℕ n f g)) , ℂ₀

