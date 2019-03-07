open import ToddPrelude
open import CantorNumbers

postulate
  ℝ : Set
  ℝ₀ ℝ₁ : ℝ
  _<ℝ_ : ℝ → ℝ → 𝔹
  _=ℝ_ : ℝ → ℝ → 𝔹
  ℝ₀-bottom : (r : ℝ) → (ℝ₀ =ℝ r) ≡ ff → (ℝ₀ <ℝ r) ≡ tt
  _+ℝ_ : ℝ → ℝ → ℝ

_||_ : 𝔹 → 𝔹 → 𝔹
ff || ff = ff
ff || tt = tt
tt || ff = tt
tt || tt = tt

_≤ℝ_ : ℝ → ℝ → 𝔹
(r ≤ℝ s) = (r =ℝ s) || (r <ℝ s)
