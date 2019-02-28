open import ToddPrelude
open import CantorNumbers
open import RealNumbers

ℰ : Set → Set
ℰ d = (d → 𝔹) → d

record Searchable (D : Set) : Set where -- K ⊆ D
  field
    ε : ℰ D
    def2 : (p : D → 𝔹) → (x : D) → p x ≡ tt → (p (ε p)) ≡ tt

data 𝟙 : Set where
  ⋆ : 𝟙

𝟙Searchable : Searchable 𝟙
Searchable.ε 𝟙Searchable p = ⋆
Searchable.def2 𝟙Searchable p ⋆ pr = pr

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

_≤_ : ℕ → ℕ → Set
k ≤ n = ∃ (λ e → (e +ℕ k) ≡ n)

ℰℕ' : ∀ n k → k ≤ n → ℰ (k ≤ n)
ℰℕ' zero zero x p = zero ⇒ refl
ℰℕ' zero (succ k) (zero ⇒ ()) p
ℰℕ' zero (succ k) (succ e ⇒ ()) p
ℰℕ' (succ n) zero x p = succ n ⇒ cong≡ (λ ■ → succ ■) (pr n) where
  pr : ∀ n → (n +ℕ zero) ≡ n
  pr zero = refl
  pr (succ n) = cong≡ (λ ■ → succ ■) (pr n)
ℰℕ' (succ n) (succ k) x p = if p (n ⇒ {!!}) then {!!} else {!!}

postulate ℕSub : ∀ n → (p : ℕ → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt) → ((ℰℕ n p) <ℕ n) ≡ tt

ℕComp : ∀ n → (p : ℕ → 𝔹) → ∃ (λ x₀ → p x₀ ≡ tt ) → (p (ℰℕ n p)) ≡ tt
ℕComp zero p (zero ⇒ x) = x
ℕComp zero p (succ w ⇒ x) = {!!}
ℕComp (succ n) p w = ∨-elim (𝔹LEM (p n)) (case tt) (case ff) where
  x₀ : ℕ
  x₀ = if (p n) then n else (ℰℕ n p)
  lem5 : {b : 𝔹} → (p n ≡ b) → p (if b then n else ℰℕ n p) ≡ tt → p x₀ ≡ tt
  lem5 pr₁ pr₂ = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then n else (ℰℕ n p)) pr₁)) pr₂
  case : (b : 𝔹) → (p n ≡ b) → p x₀ ≡ tt
  case tt pr = lem5 pr pr
  case ff pr = lem5 pr (ℕComp n p w)

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

div-helper : ℕ → ℕ → ℕ → ℕ → ℕ
div-helper k m  zero    j      = k
div-helper k m (succ n)  zero   = div-helper (succ k) m n m
div-helper k m (succ n) (succ j) = div-helper k m n j

div : ℕ → ℕ → ℕ 
div n zero = zero
div zero (succ m) = zero
div n (succ m) = div-helper 0 m n m 
