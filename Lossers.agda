open import ToddPrelude
open import RealNumbers
open import CantorNumbers
open import Searchers

open RealNumber {ℝ} 𝕣

record LossSpace (Y : Set) : Set where
  field
    Φ : Y → Y → ℝ
    pos : ∀ y₁ y₂ → ℝ₀ ≤ℝ (Φ y₁ y₂)
    ref : ∀ y₁ → (Φ y₁ y₁ ≡ ℝ₀)
    sym : ∀ y₁ y₂ → (Φ y₁ y₂) ≡ (Φ y₂ y₁)

ℕ→ℝ : ℕ → ℝ
ℕ→ℝ zero = ℝ₀
ℕ→ℝ (succ n) = ℝ₁ +ℝ (ℕ→ℝ n)

ℕ→ℝFact : ∀ n → (zero <ℕ n) ≡ tt → (ℝ₀ <ℝ ℕ→ℝ n) ≡ tt
ℕ→ℝFact zero ()
ℕ→ℝFact (succ zero) _ = trans≡ (cong≡ (λ ■ → ℝ₀ <ℝ ■) (+0 ℝ₁)) <0
ℕ→ℝFact (succ (succ n)) _ = <+ <0 (inl (ℕ→ℝFact (succ n) refl))

ℕLoss : LossSpace ℕ
LossSpace.Φ ℕLoss n₁ n₂ = ℕ→ℝ (maxℕ (n₁ −ℕ n₂) (n₂ −ℕ n₁))
LossSpace.pos ℕLoss zero zero = inr (_≡ℝ_ refl)
LossSpace.pos ℕLoss zero (succ n₂) = inl (ℕ→ℝFact (maxℕ zero (succ n₂)) refl)
LossSpace.pos ℕLoss (succ n₁) zero = inl (ℕ→ℝFact (maxℕ (succ n₁) zero) refl)
LossSpace.pos ℕLoss (succ n₁) (succ n₂) = LossSpace.pos ℕLoss n₁ n₂
LossSpace.ref ℕLoss n = cong≡ ℕ→ℝ (trans≡ (maxFact (n −ℕ n)) (minusFact n)) where
  minusFact : ∀ x → (x −ℕ x) ≡ zero
  minusFact zero = refl
  minusFact (succ x) = minusFact x
  maxFact : ∀ x → maxℕ x x ≡ x
  maxFact zero = refl
  maxFact (succ x) = cong≡ succ (maxFact x)
LossSpace.sym ℕLoss n₁ n₂ = cong≡ ℕ→ℝ (maxFact (n₁ −ℕ n₂) (n₂ −ℕ n₁)) where
  maxFact : ∀ x y → maxℕ x y ≡ maxℕ y x
  maxFact zero zero = refl
  maxFact zero (succ y) = refl
  maxFact (succ x) zero = refl
  maxFact (succ x) (succ y) = cong≡ succ (maxFact x y)

conv : 𝕓 → ℕ → ℝ
conv ₀ n = ℝ₀
conv ₁ n = ℝ₁ ÷ℝ (ℕ→ℝ (n +ℕ 1))

ℕℂ→ℝ : ℕ → (ℂ → ℝ)
ℕℂ→ℝ zero c = conv (c 0) 0
ℕℂ→ℝ (succ n) c = (conv (c (succ n)) (succ n)) +ℝ (ℕℂ→ℝ n c)

Φℂ𝕟 : ℂ → ℂ → ℂ
Φℂ𝕟 c₁ c₂ n = φ𝕓 (c₁ n) (c₂ n)

symm : ∀ b₁ b₂ → φ𝕓 b₁ b₂ ≡ φ𝕓 b₂ b₁
symm ₀ ₀ = refl
symm ₀ ₁ = refl
symm ₁ ₀ = refl
symm ₁ ₁ = refl
reff : ∀ b₁ {b₂} → b₁ ≡ b₂ → φ𝕓 b₁ b₂ ≡ ₀
reff ₀ refl = refl
reff ₁ refl = refl
conv3 : ∀ n → conv ₀ n ≡ ℝ₀
conv3 n = refl
conv4 : ∀ n → (ℝ₀ <ℝ conv ₁ n) ≡ tt
conv4 zero = trans≡ (cong≡ (λ ■ → ℝ₀ <ℝ (ℝ₁ ÷ℝ ■)) (+0 ℝ₁)) (trans≡ (cong≡ (λ ■ → ℝ₀ <ℝ ■) ÷1) <0)
conv4 (succ n) = (<÷ <0 (<+ <0 (inl (ℕ→ℝFact (n +ℕ 1) (<zero n))))) where
  <zero : ∀ n → (zero <ℕ (n +ℕ 1)) ≡ tt
  <zero zero = refl
  <zero (succ n) = refl

ℂLoss : ℕ → LossSpace ℂ
LossSpace.Φ (ℂLoss n) c₁ c₂ = ℕℂ→ℝ n (Φℂ𝕟 c₁ c₂)
LossSpace.pos (ℂLoss zero) c₁ c₂ = ∨-elim (𝕓LEM (φ𝕓 (c₁ 0) (c₂ 0)))
                                                           (λ z → inr (sym= (trans= (_≡ℝ_ (cong≡ (λ ■ → conv ■ 0) z)) (_≡ℝ_ (conv3 0)))))
                                                           (λ z → inl (trans≡ (cong≡ (λ ■ → ℝ₀ <ℝ conv ■ 0) z) (conv4 0)))
LossSpace.pos (ℂLoss (succ n)) c₁ c₂ = (≤+ (∨-elim (𝕓LEM ((Φℂ𝕟 c₁ c₂ (succ n))))
                                                                 (λ z → inr (sym= (trans= (_≡ℝ_ (cong≡ (λ ■ → conv ■ (succ n)) z)) (_≡ℝ_ (conv3 n)))))
                                                                 (λ z → inl (trans≡ (cong≡ (λ ■ → ℝ₀ <ℝ conv ■ (succ n)) z) (conv4 (succ n)))))
                                                                 (LossSpace.pos (ℂLoss n) c₁ c₂))
LossSpace.ref (ℂLoss zero) c₁ = trans≡ (cong≡ (λ ■ → conv ■ 0) (reff (c₁ 0) refl)) (conv3 0)
LossSpace.ref (ℂLoss (succ n)) c₁ = trans≡ (cong≡ (λ ■ → (conv (Φℂ𝕟 c₁ c₁ (succ n)) (succ n)) +ℝ ■) (LossSpace.ref (ℂLoss n) c₁))
                                                          (trans≡ (cong≡ (λ ■ → ■ +ℝ ℝ₀) (trans≡ (cong≡ (λ ■ → conv ■ (succ n)) (reff (c₁ (succ n)) refl)) (conv3 n))) (+0 ℝ₀))
LossSpace.sym (ℂLoss zero) c₁ c₂ = cong≡ (λ ■ → conv ■ 0) (symm (c₁ 0) (c₂ 0))
LossSpace.sym (ℂLoss (succ n)) c₁ c₂ = trans≡ (cong≡ (λ ■ → conv (Φℂ𝕟 c₁ c₂ (succ n)) (succ n) +ℝ ■) (LossSpace.sym (ℂLoss n) c₁ c₂))
                                                                 (cong≡ (λ ■ → ■ +ℝ (ℕℂ→ℝ n (Φℂ𝕟 c₂ c₁))) (cong≡ (λ ■ → conv ■ (succ n)) (symm (c₁ (succ n)) (c₂ (succ n)))))
