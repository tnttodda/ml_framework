open import ToddPrelude
open import CantorNumbers

ℝ : Set
ℝ = ℕ × ℂ

postulate ℝ-change : {n : ℕ} → (succ n , ℂ₀) ≡ (n , ℂ₁)

ℝ₀ ℝ₁ : ℝ
ℝ₀ = zero , ℂ₀
ℝ₁ = succ zero , ℂ₀

_<ℝ_ : ℝ → ℝ → ℕ → 𝔹
((n , r) <ℝ (m , s)) ε = if (n =ℕ m) then (r <ℂ s) ε else (n <ℕ m)

_=ℝ_ : ℝ → ℝ → ℕ → 𝔹
((n , r) =ℝ (m , s)) ε = if (n =ℕ m) then (r =ℂ s) ε else (ff)

_||_ : 𝔹 → 𝔹 → 𝔹
ff || ff = ff
ff || tt = tt
tt || ff = tt
tt || tt = tt

_≤ℝ_ : ℝ → ℝ → ℕ → 𝔹
(r ≤ℝ s) ε = ((r =ℝ s) ε) || ((r <ℝ s) ε)

postulate lemma : (c : ℂ) → (ε : ℕ) → (ℂ₀ =ℂ c) ε ≡ ff → (ℂ₀ <ℂ c) ε ≡ tt

ℝ₀-bottom : (ε : ℕ) → (r : ℝ) → (ℝ₀ =ℝ r) ε ≡ ff → (ℝ₀ <ℝ r) ε ≡ tt
ℝ₀-bottom ε (zero , r) pr = lemma r ε pr
ℝ₀-bottom ε (succ m , r) pr = refl

record RealNumbers (𝕣 : Set) : Set₁ where
  field
    𝕣₀ 𝕣₁ : 𝕣
    _<𝕣_ _=𝕣_ : 𝕣 → 𝕣 → 𝔹
    𝕣₀-bottom : (r : 𝕣) → (𝕣₀ =𝕣 r) ≡ ff → (𝕣₀ <𝕣 r) ≡ tt

ℝis𝕣 : ℕ → RealNumbers ℝ
RealNumbers.𝕣₀ (ℝis𝕣 ε) = ℝ₀
RealNumbers.𝕣₁ (ℝis𝕣 ε) = ℝ₁
RealNumbers._<𝕣_ (ℝis𝕣 ε) = λ a b → (a <ℝ b) ε
RealNumbers._=𝕣_ (ℝis𝕣 ε) = λ a b → (a =ℝ b) ε
RealNumbers.𝕣₀-bottom (ℝis𝕣 ε) = ℝ₀-bottom ε
