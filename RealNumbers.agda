open import ToddPrelude
open import CantorNumbers
open import Searchers

record RealNumber (ℝ : Set) : Set where
  field
    ℝ₀ : ℝ
    _<ℝ_ : ℝ → ℝ → 𝔹
    _=ℝ_ : ℝ → ℝ → 𝔹
    _+ℝ_ : ℝ → ℝ → ℝ
    ℝ₀-bottom : (r : ℝ) → (ℝ₀ =ℝ r) ≡ ff → (ℝ₀ <ℝ r) ≡ tt
    Φℝ : ℝ → ℝ → ℝ
    Φℝrule : ∀ {a b ε} → (Φℝ a b <ℝ ε) ≡ tt → (b <ℝ (ε +ℝ a)) ≡ tt
  _≤ℝ_ : ℝ → ℝ → 𝔹
  r ≤ℝ s = _<ℝ_ r s || _=ℝ_ r s
  _>ℝ_ : ℝ → ℝ → 𝔹
  r >ℝ s = ! (r ≤ℝ s)

ℂReal : ℕ → RealNumber ℂ
RealNumber.ℝ₀ (ℂReal _) = ℂ₀
RealNumber._<ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ <ℂ c₂) n
RealNumber._=ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ =ℂ c₂) n
RealNumber._+ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ +ℂ c₂) n
RealNumber.ℝ₀-bottom (ℂReal n) = {!!}
RealNumber.Φℝ (ℂReal n) = {!Φℂ!}
RealNumber.Φℝrule (ℂReal n) = {!!}
