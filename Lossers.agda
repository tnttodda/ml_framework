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

𝕓LEM : (b : 𝕓) → (b ≡ ₁) ∨ (b ≡ ₀)
𝕓LEM ₁ = inl refl
𝕓LEM ₀ = inr refl

ℂisLoss : LossSpace Φℂ
LossSpace.pos ℂisLoss y₁ y₂ zero =  ⋆⟪TODO⟫⋆ where
  lem2 : (c : ℂ) → c zero ≡ ₁ → ((ℂ₀ <ℂ c) zero) ≡ tt
  lem2 c x =  ⋆⟪TODO⟫⋆
  lem'' : {c c' : ℂ} → (b b' : 𝕓) → (head c ≡ b) → (head c' ≡ b') → ((c' =ℂ c) zero) ≡ (b' =𝕓 b)
  lem'' =  ⋆⟪TODO⟫⋆
  lem' : (c c' : ℂ) → ((c' =ℂ c) zero) ≡ ((head c') =𝕓 (head c))
  lem' c c' = refl
  lem : (c : ℂ) → c zero ≡ ₀ → ((ℂ₀ =ℂ c) zero) ≡ tt
  lem c x =  ⋆⟪TODO⟫⋆
LossSpace.pos ℂisLoss y₁ y₂ (succ ε) =  ⋆⟪TODO⟫⋆ 
LossSpace.ref ℂisLoss y₁ = cong≡ (λ ■ → 0 , ■) (FunExt lem) where
  𝕓ref : ∀ b → (φ𝕓 b b) ≡ ₀ 
  𝕓ref ₀ = refl
  𝕓ref ₁ = refl
  lem : ∀ k → (λ n → φ𝕓 (y₁ n) (y₁ n)) k ≡ ℂ₀ k
  lem k = trans≡ (𝕓ref (y₁ k)) (sym≡ (𝕓ref (ℂ₀ k)))
LossSpace.sym ℂisLoss =  ⋆⟪TODO⟫⋆

isNormAtℂ : (ℂ → ℂ) → ℂ → ℕ → 𝔹
isNormAtℂ f c n = forevery ℰℂ (λ c' → maxℂ (f c) (f c') n =𝕓 (f c) n)

isNormℂ : (ℂ → ℂ) → ℂ → ℕ → 𝔹
isNormℂ f c zero = isNormAtℂ f c zero
isNormℂ f c (succ e) = isNormAtℂ f c (succ e) && isNormℂ f c e 

supNormℂ : (ℂ → ℂ) → ℕ → ℂ
supNormℂ f e n = ℰℂ (λ c → isNormℂ f c e) n

Φℂ→ℂ : ℕ → (ℂ → ℂ) → (ℂ → ℂ) → ℝ
Φℂ→ℂ n f g = Φℂ (supNormℂ f n) (supNormℂ g n)

supNormℕ : ℕ → (ℕ → ℕ) → ℕ
supNormℕ size f = (ℰℕ size) (λ n → forevery (ℰℕ size) (λ n' → maxℕ (f n) (f n') =ℕ f n))

Φℕ→ℕ' : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ
Φℕ→ℕ' zero f g = π₁ (Φℕ (f zero) (g zero)) , ℂ₀
Φℕ→ℕ' (succ n) f g = (π₁ (Φℕ (f n) (g n)) +ℕ π₁ (Φℕ→ℕ' n f g)) , ℂ₀

Φℕ→ℕ : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ
Φℕ→ℕ n = Φℕ→ℕ' (div n 3)
