open import ToddPrelude
open import CantorNumbers
open import RealNumbers

ℰ : Set → Set
ℰ d = (d → 𝔹) → d

record CompactSpace {D : Set} (Σ : (D → 𝔹) → D) : Set where
  field
    def2 : (p : D → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt) → p (Σ p) ≡ tt

record Searchable (D : Set) : Set where -- K ⊆ D
  field
    ε : ℰ D
    def2 : (p : D → 𝔹) → (x : D) → p x ≡ tt → (p (ε p)) ≡ tt

data 𝟙 : Set where
  ⋆ : 𝟙

𝟙Searchable : Searchable 𝟙
Searchable.ε 𝟙Searchable p = ⋆
Searchable.def2 𝟙Searchable p ⋆ pr = pr

𝔹Searchable : Searchable 𝔹
Searchable.ε 𝔹Searchable p = if (p tt) then (tt) else (ff)
Searchable.def2 𝔹Searchable p ff pr = ∨-elim (𝔹LEM (p tt)) left-side right-side where
  left-side : p tt ≡ tt → p (if p tt then tt else ff) ≡ tt
  left-side t = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) t)) t
  right-side : p tt ≡ ff → p (if p tt then tt else ff) ≡ tt
  right-side f = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) f)) pr
Searchable.def2 𝔹Searchable p tt pr = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) pr)) pr

∨Searchable : {A B : Set} → Searchable A → Searchable B → Searchable (A ∨ B)
Aside : {A B : Set} → Searchable A → Searchable B → (p : (A ∨ B) → 𝔹) → A ∨ B
Aside ℰA ℰB p = inl (Searchable.ε ℰA (λ a → p (inl a)))
Bside : {A B : Set} → Searchable A → Searchable B → (p : (A ∨ B) → 𝔹) → A ∨ B
Bside ℰA ℰB p = inr (Searchable.ε ℰB (λ b → p (inr b)))
A∨B : {A B : Set} → Searchable A → Searchable B → (p : (A ∨ B) → 𝔹) → 𝔹 → A ∨ B
A∨B ℰA ℰB p tt = Aside ℰA ℰB p
A∨B ℰA ℰB p ff = Bside ℰA ℰB p
Searchable.ε (∨Searchable {A} {B} ℰA ℰB) p = A∨B ℰA ℰB p (p (Aside ℰA ℰB p))
Searchable.def2 (∨Searchable ℰA ℰB) p (inl a) pr = prove (p (Aside ℰA ℰB p)) refl where
  prove : (b : 𝔹) → p (Aside ℰA ℰB p) ≡ b → p (A∨B ℰA ℰB p (p (Aside ℰA ℰB p))) ≡ tt
  prove tt pr₁ = trans≡ sub pr₁ where
    sub : (p (A∨B ℰA ℰB p (p (Aside ℰA ℰB p))) ≡ p (A∨B ℰA ℰB p tt)) 
    sub = cong≡ (λ ■ → p (A∨B ℰA ℰB p ■)) pr₁
  prove ff pr₁ = EFQ (Searchable.def2 ℰA (λ a → p (inl a)) a pr) pr₁
Searchable.def2 (∨Searchable ℰA ℰB) p (inr b) pr = prove (p (Aside ℰA ℰB p)) refl where
  prove : (b : 𝔹) → p (Aside ℰA ℰB p) ≡ b → p (A∨B ℰA ℰB p (p (Aside ℰA ℰB p))) ≡ tt
  prove ff pr₁ = trans≡ sub (Searchable.def2 ℰB (λ b → p (inr b)) b pr) where
    sub : (p (A∨B ℰA ℰB p (p (Aside ℰA ℰB p))) ≡ p (A∨B ℰA ℰB p ff)) 
    sub = cong≡ (λ ■ → p (A∨B ℰA ℰB p ■)) pr₁
  prove tt pr₁ = trans≡ (cong≡ (λ ■ → p (A∨B ℰA ℰB p ■)) pr₁) pr₁

Π : (d : Set) → Set
Π d = (d → 𝔹) → 𝔹

forsome forevery : {d : Set} → ℰ d → Π d
forsome s p = p (s p)
forevery s p = ! forsome s (λ x → ! p x)

ℰℕ : ℕ → ℰ ℕ
ℰℕ zero p = zero
ℰℕ (succ n) p = if (p n) then (n) else (ℰℕ n p)

ℕComp : ∀ n → (p : ℕ → 𝔹) → (x₀ : ℕ) → (p x₀ ≡ tt) →
               ((x₀ ≡ zero) ∨ ((x₀ <ℕ n) ≡ tt)) → (p (ℰℕ n p)) ≡ tt
ℕComp zero p zero pr lt = pr
ℕComp zero p (succ x₀) pr (inl ())
ℕComp zero p (succ x₀) pr (inr ())
ℕComp (succ n) p zero pr (inl refl) = {!!}
ℕComp (succ n) p zero pr (inr refl) = {!!}
ℕComp (succ n) p (succ x₀) pr (inl ())
ℕComp (succ n) p (succ x₀) pr (inr x) = {!!}

-- where
--  left : p n ≡ tt → p (if p n then n else ℰℕ n p) ≡ tt
--  left x = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then n else ℰℕ n p) x)) x
--  right : p n ≡ ff → p (if p n then n else ℰℕ n p) ≡ tt
-- right x = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then n else ℰℕ n p) x)) {!!}

ℰ𝔹 : ℰ 𝔹
ℰ𝔹 p = if (p tt) then (tt) else (ff)

ℰ𝕓 : ℰ 𝕓
ℰ𝕓 p = if (p ₁) then (₁) else (₀)

ℰ× : {d d' : Set} → ℰ d → ℰ d' → ℰ (d × d')
ℰ× {d} {d'} e e' p = x2 , x'2 where
  x2 : d
  x2 = e (λ x → forsome e' (λ x' → p (x , x')))
  x'2 : d'
  x'2 = e' (λ x' → p (x2 , x'))

{-# TERMINATING #-}
ℰℕ→ : {d : Set} → (ℕ → ℰ d) → ℰ (ℕ → d)
ℰℕ→ {d} e p n = e n (λ x → q n x (ℰℕ→ (λ i → e (n +ℕ succ i)) (q n x))) where
  q : ℕ → d → (ℕ → d) → 𝔹
  q n x a = p (λ i → if (i <ℕ n) then (ℰℕ→ e p i)
                     else (if (i =ℕ n) then (x) else a (i −ℕ succ n)))

ℰℂ : ℰ ℂ
ℰℂ = ℰℕ→ (λ i → ℰ𝕓)

ℰℝ : ℕ → ℰ ℝ
ℰℝ n = ℰ× (ℰℕ n) ℰℂ
