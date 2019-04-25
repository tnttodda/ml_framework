open import ToddPrelude
open import CantorNumbers
open import Searchers

postulate ℝ : Set

record RealNumber (ℝ : Set) : Set where
  field
    ℝ₀ ℝ₁ : ℝ
    _<ℝ_ : ℝ → ℝ → 𝔹
    _=ℝ_ : ℝ → ℝ → 𝔹
    _+ℝ_ : ℝ → ℝ → ℝ
    Φℝ : ℝ → ℝ → ℝ
    Φℝrule : ∀ {a b ε} → (Φℝ a b <ℝ ε) ≡ tt → (b <ℝ (ε +ℝ a)) ≡ tt -- doesnt hold in cantor

    sym= : ∀ {r₁ r₂} → (r₁ =ℝ r₂) ≡ tt → (r₂ =ℝ r₁) ≡ tt
    trans= : ∀ {r₁ r₂ r₃} → (r₁ =ℝ r₂) ≡ tt → (r₂ =ℝ r₃) ≡ tt → (r₁ =ℝ r₃) ≡ tt
    _÷ℝ_ : ℝ → ℝ → ℝ
    <÷ : ∀ {r₁ r₂} → (ℝ₀ <ℝ r₁) ≡ tt → (ℝ₀ <ℝ r₂) ≡ tt → (ℝ₀ <ℝ (r₁ ÷ℝ r₂)) ≡ tt
    ÷1 : ∀ {r} → (r ÷ℝ ℝ₁) ≡ r
    _≡ℝ_ : ∀ {r₁ r₂} → r₁ ≡ r₂ → (r₁ =ℝ r₂) ≡ tt
    +0 : ∀ r → (r +ℝ ℝ₀) ≡ r
    <0 : (ℝ₀ <ℝ ℝ₁) ≡ tt
    <1 : (ℝ₁ <ℝ (ℝ₁ +ℝ ℝ₁))≡ tt -- doesnt hold in cantor
    trans< : ∀ {a b c} → (a <ℝ b) ≡ tt → (b <ℝ c) ≡ tt → (a <ℝ c) ≡ tt
    +assoc : ∀ {a b c} → (a +ℝ (b +ℝ c)) ≡ ((a +ℝ b) +ℝ c)
    +< : ∀ {a b c} → (a <ℝ b) ≡ tt → ((a +ℝ c) <ℝ (b +ℝ c)) ≡ tt -- doesnt hold in cantor
    <+ : ∀ {a b c} → (a <ℝ b) ≡ tt → ((a <ℝ c) ≡ tt) ∨ ((a =ℝ c) ≡ tt) → (a <ℝ (b +ℝ c)) ≡ tt
    ≤+ : ∀ {a b c} → ((a <ℝ b) ≡ tt) ∨ ((a =ℝ b) ≡ tt) → ((a <ℝ c) ≡ tt) ∨ ((a =ℝ c) ≡ tt) →  ((a <ℝ (b +ℝ c)) ≡ tt) ∨ ((a =ℝ (b +ℝ c)) ≡ tt) 
  _≤ℝ_ : ℝ → ℝ → Set
  r ≤ℝ s = ((r <ℝ s) ≡ tt) ∨ ((r =ℝ s) ≡ tt)
--  _>ℝ_ : ℝ → ℝ → 𝔹
--  r >ℝ s = ! (r ≤ℝ s)

postulate 𝕣 : RealNumber ℝ

φ𝕓 : 𝕓 → 𝕓 → 𝕓
φ𝕓 ₀ ₀ = ₀
φ𝕓 ₁ ₁ = ₀
φ𝕓 _ _ = ₁

{-
ℂReal : ℕ → RealNumber ℂ
RealNumber.ℝ₀ (ℂReal _) = ℂ₀
RealNumber._<ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ <ℂ c₂) n
RealNumber._=ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ =ℂ c₂) n
RealNumber._+ℝ_ (ℂReal n) = λ c₁ c₂ → (c₁ +ℂ c₂) n
RealNumber.Φℝ (ℂReal n) = λ c₁ c₂ n → φ𝕓 (c₁ n) (c₂ n)
RealNumber.
-}
