open import ToddPrelude
open import RealNumbers
open import Searchers
-- open import Lossers
-- open import Regressors

record LossSpace {Y : Set} (Φ : Y → Y → ℝ) : Set₁ where
  field
    pos : ∀ y₁ y₂ → ((ℝ₀ <ℝ (Φ y₁ y₂)) ≡ tt) ∨ ((ℝ₀ =ℝ (Φ y₁ y₂)) ≡ tt)
    ref : ∀ y₁ → (Φ y₁ y₁ ≡ ℝ₀)
    sym : ∀ y₁ y₂ → (Φ y₁ y₂) ≡ (Φ y₂ y₁)

γ : (X Y : Set) → Set
γ X Y = ℝ → Y → (X → Y) → X
buildReg : {X Y : Set} (ℰ : (X → 𝔹) → X) → (Φ : Y → Y → ℝ) → γ X Y
buildReg ℰ Φ = λ ε y m → ℰ (λ x → (Φ (m x) y <ℝ ε))

RegressionConvergence : {X Y : Set} (Φ : Y → Y → ℝ) (reg : Y → (X → Y) → X) (k : X) (f : X → Y) → Set
RegressionConvergence {X} {Y} Φ reg k f = ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (f k) (f (reg (f k) f)) <ℝ ε) ≡ tt

solis-wets-noise : {X Y : Set} (Φ : Y → Y → ℝ) (ψ : Y → Y) (reg : Y → (X → Y) → X) (k : X) (f : X → Y) → Set
solis-wets-noise {X} {Y} Φ ψ reg k f = ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (ψ (f k)) (f (reg (f k) f)) <ℝ (ε +ℝ (Φ (ψ (f k)) (f k)))) ≡ tt

theorem : {X Y : Set} (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ)
             → CompactSpace ℰ → LossSpace Φ
             → (k : X) (f : X → Y)
             → ∀ ε → (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → (Φ (f k) (f (buildReg ℰ Φ ε (f k) f)) <ℝ ε) ≡ tt
theorem {X} {Y} ℰ Φ S L k f ε ε₀ = firstly thirdly  where
  p : X → 𝔹
  p = λ x → Φ (f x) (f k) <ℝ ε
  k' : X
  k' = ℰ p
  firstly : (p k' ≡ tt) → (Φ (f k) (f k') <ℝ ε) ≡ tt
  firstly r = trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.sym L (f k) (f k'))) r
  secondly : ∃ (λ x → p x ≡ tt)
  secondly = k ⇒ trans≡ (cong≡ (λ ■ → ■ <ℝ ε) (LossSpace.ref L (f k))) (ℝ₀-bottom ε ε₀)
  thirdly : p k' ≡ tt
  thirdly = CompactSpace.def2 S p secondly

postulate Φℝ : ℝ → ℝ → ℝ
postulate Φℝrule : ∀ {a b ε} → (Φℝ a b <ℝ ε) ≡ tt → (b <ℝ (ε +ℝ a)) ≡ tt
postulate ℝSearchable : Searchable ℝ

∧l : {A B : Set} → A ∧ B → A
∧l (a & _) = a
∧r : {A B : Set} → A ∧ B → B
∧r (_ & b) = b

_⇨_ : 𝔹 → 𝔹 → 𝔹
tt ⇨ ff = ff
_ ⇨ _ = tt

𝔹rule1 : {b₂ : 𝔹} → (b₁ : 𝔹) → ((! b₁) && b₂) ≡ tt → b₁ ≡ ff
𝔹rule1 tt ()
𝔹rule1 ff _ = refl
𝔹rule2 : (b₁ b₂ : 𝔹) → (b₁ ⇨ b₂) ≡ tt → b₁ ≡ tt → b₂ ≡ tt
𝔹rule2 ff ff _ x₁ = x₁
𝔹rule2 _ tt _ _ = refl
𝔹rule2 tt ff () x₁
𝔹rule3 : {b₁ b₂ : 𝔹} → (b₁ && b₂) ≡ tt → b₂ ≡ tt
𝔹rule3 {_} {tt} _ = refl
𝔹rule3 {ff} {ff} x = x
𝔹rule3 {tt} {ff} ()

continuityCondition : {Y : Set} (Φ : Y → Y → ℝ) (f : Y → ℝ) (ε : ℝ) → (k x : Y) → (δ : ℝ) → 𝔹
continuityCondition Φ f ε k x δ = ((! (ℝ₀ =ℝ δ)) && ((Φ k x <ℝ δ) ⇨ (Φℝ (f k) (f x) <ℝ ε)))

continuous : {Y : Set} (Φ : Y → Y → ℝ) (f : Y → ℝ) (k : Y) → Set
continuous Φ f k = ∀ ε → (ℝ₀ =ℝ ε) ≡ ff → ∃ (λ δ → ∀ x → continuityCondition Φ f ε k x δ ≡ tt)

Π₀ : {X : Set} {A : X → Set} → (∃ \(x : X) → A x) → X
Π₀(x ⇒ _) = x

Π₁ : {X : Set} {A : X → Set} → (z : ∃ \(x : X) → A x) → A(Π₀ z)
Π₁(_ ⇒ a) = a

theorem-noise : {X Y : Set} (ℰ : (X → 𝔹) → X) (Φ : Y → Y → ℝ) (ψ : Y → Y)
                      → CompactSpace ℰ → LossSpace Φ
                      → (reg : Y → (X → Y) → X)
                      → (k : X) (f : X → Y)
                      → continuous Φ (λ y → Φ (ψ (f k)) y) (f k)
                      → RegressionConvergence Φ reg k f
                      → solis-wets-noise Φ ψ reg k f
theorem-noise {X} {Y} ℰ Φ ψ S L reg k f cont R ε ε₀ = conjecture where
  noisy regressed normal : Y
  normal = f k
  regressed = f (reg normal f)
  noisy = ψ normal
  δ : ℝ
  δ = Π₀ (cont ε ε₀)
  δworks : continuityCondition Φ (λ y → Φ (ψ (f k)) y) ε normal regressed δ ≡ tt
  δworks = (Π₁ (cont ε ε₀)) regressed
  fact : (Φ normal regressed <ℝ δ) ≡ tt
  fact = R δ (𝔹rule1 (ℝ₀ =ℝ δ) δworks)
  δ₁ : (Φ normal regressed <ℝ δ) ≡ tt → (Φℝ (Φ noisy normal) (Φ noisy regressed) <ℝ ε) ≡ tt
  δ₁ = 𝔹rule2 (Φ normal regressed <ℝ δ) (Φℝ (Φ noisy normal) (Φ noisy regressed) <ℝ ε) (𝔹rule3 δworks)
  conjecture :  (Φ noisy regressed <ℝ (ε +ℝ Φ noisy normal)) ≡ tt
  conjecture = Φℝrule (δ₁ fact)

-- γℕℕconverges : ∀ n → (ε : ℝ̂) (ε₀ : (ℝ₀ =ℝ ε) ≡ ff) → RegressionConvergence ε Φℕ (γℕ,ℕ n ε)
-- γℕℕconverges n ε ε₀ = λ k f → theorem ε ε₀ (ℰℕ n) Φℕ {!!} ℕisLoss k f
