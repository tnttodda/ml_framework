open import ToddPrelude
open import CantorNumbers

postulate ℝ : Set
postulate ℝ₀ : ℝ
postulate _<ℝ_ : ℝ → ℝ → 𝔹
postulate _=ℝ_ : ℝ → ℝ → 𝔹
postulate ℝ₀-bottom : (r : ℝ) → (ℝ₀ =ℝ r) ≡ ff → (ℝ₀ <ℝ r) ≡ tt
postulate Φ : {A : Set} → A → A → ℝ

record Hausdorff (S : Set) : Set where 
  field
    _≠_ : S → S → 𝔹
    irr : ∀ x → (x ≠ x) ≡ ff
    sym : ∀ x y → (x ≠ y) ≡ tt → (y ≠ x) ≡ tt
    com : ∀ x y z → (x ≠ z) ≡ tt → ((x ≠ y) ≡ tt) ∨ ((y ≠ z) ≡ tt)
    Ω : S → S → S
    def1 : ∀ x y → (x ≠ y) ≡ tt → ∃ (λ ε → (ε <ℝ Φ x y) ≡ tt)
    def2 : ∀ x y → (x ≠ y) ≡ tt → ∃ (λ s → (Ω x y ≡ s) ∧ (((x ≠ s) ≡ tt) ∧ ((y ≠ s) ≡ tt)))

postulate Φ₀ : {A : Set} → (x : A) → (ℝ₀ =ℝ (Φ x x)) ≡ tt
postulate Φ₁ : {A : Set} → (x y : A) → (ℝ₀ =ℝ (Φ x y)) ≡ tt → x ≡ y
postulate Φ₂ : {A : Set} → (y₁ y₂ : A) →  ((ℝ₀ <ℝ (Φ y₁ y₂)) ≡ tt) ∨ ((ℝ₀ =ℝ (Φ y₁ y₂)) ≡ tt)
postulate fact : {A : Set} (S : Hausdorff A) → (x y : A) → (x ≡ y) → (Hausdorff._≠_ S x y) ≡ ff

lemma : {A : Set} (S : Hausdorff A) → (x y : A) → (Hausdorff._≠_ S x y) ≡ tt → (ℝ₀ =ℝ Φ x y) ≡ ff  
lemma S x y x₁ = ∨-elim (𝔹LEM (ℝ₀ =ℝ Φ x y)) (λ z → EFQ x₁ (fact S x y (Φ₁ x y z))) (λ z → z)

ℕH : Hausdorff ℕ
Hausdorff._≠_ ℕH = λ x y → ! (x =ℕ y)
Hausdorff.irr ℕH x = cong≡ (λ ■ → ! ■) (op x) where
  op : ∀ x → (x =ℕ x) ≡ tt
  op zero = refl
  op (succ x) = op x
Hausdorff.sym ℕH x y pr = trans≡ (cong≡ (λ ■ → ! ■) (op y x)) pr where
  op : ∀ x y → (x =ℕ y) ≡ (y =ℕ x)
  op zero zero = refl
  op zero (succ _) = refl
  op (succ _) zero = refl
  op (succ x) (succ y) = op x y
Hausdorff.com ℕH x y z pr = ∨-elim (𝔹LEM (Hausdorff._≠_ ℕH x y)) inl
                                              (λ pr₁ → ∨-elim (𝔹LEM (Hausdorff._≠_ ℕH y z)) inr
                                              (λ pr₂ → EFQ pr (cong≡ (λ ■ → ! ■)
                                              (rule x y z (rule2 (x =ℕ y) pr₁) (rule2 (y =ℕ z) pr₂))))) where
  rule2 : ∀ b → (! b) ≡ ff → b ≡ tt
  rule2 ff ()
  rule2 tt refl = refl
  rule : ∀ x y z → (x =ℕ y) ≡ tt → (y =ℕ z) ≡ tt → (x =ℕ z) ≡ tt
  rule zero zero _ _ x₃ = x₃
  rule zero (succ _) _ () _
  rule (succ _) zero _ () _
  rule _ (succ _) zero _ ()
  rule (succ x) (succ y) (succ z) x₂ x₃ = rule x y z x₂ x₃
Hausdorff.Ω ℕH x y = Φℕ x y where
  Φℕ : ℕ → ℕ → ℕ
  Φℕ n m = maxℕ (n −ℕ m) (m −ℕ n)
Hausdorff.def1 ℕH x y pr = ℝ₀ ⇒ (ℝ₀-bottom (Φ x y) (lemma {!!} x y pr))
Hausdorff.def2 ℕH x y x₁ = {!!}

postulate fact2 : ∀ x → (head x =𝕓 head x) ≡ tt

ℂH : ℕ → Hausdorff ℂ
Hausdorff._≠_ (ℂH n) = λ x y → ! (x =ℂ y) n
Hausdorff.irr (ℂH n) x = cong≡ (λ ■ → ! ■) (op x n) where
  op : ∀ x n → (x =ℂ x) n ≡ tt
  op x zero = fact2 x
  op x (succ n) = trans≡ (cong≡ (λ ■ → (if ■ then (tail x =ℂ tail x) n else ff)) (fact2 x)) (op (tail x) n)
Hausdorff.sym (ℂH n) x y pr = {!!}
Hausdorff.com (ℂH n) x y z pr = {!!}
Hausdorff.Ω (ℂH n) = {!!}
Hausdorff.def1 (ℂH n) = {!!}
Hausdorff.def2 (ℂH n) = {!!}
