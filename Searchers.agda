open import ToddPrelude
open import CantorNumbers

ℰ : Set → Set
ℰ d = (d → 𝔹) → d
Π : (d : Set) → Set
Π d = (d → 𝔹) → 𝔹
forsome forevery : {d : Set} → ℰ d → Π d
forsome s p = p (s p)
forevery s p = ! forsome s (λ x → ! p x)

record Searchable (D : Set) : Set where -- K ⊆ D
  field
    ε : ℰ D
    def2 : (p : D → 𝔹) → (x : D) → p x ≡ tt → (p (ε p)) ≡ tt

data 𝟙 : Set where
  ⋆ : 𝟙

𝟙Searchable' : Searchable 𝟙
Searchable.ε 𝟙Searchable' p = ⋆
Searchable.def2 𝟙Searchable' p ⋆ pr = pr

𝔹Searchable' : Searchable 𝔹
Searchable.ε 𝔹Searchable' p = if (p tt) then (tt) else (ff)
Searchable.def2 𝔹Searchable' p ff pr = ∨-elim (𝔹LEM (p tt)) left-side right-side where
  left-side : p tt ≡ tt → p (if p tt then tt else ff) ≡ tt
  left-side t = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) t)) t
  right-side : p tt ≡ ff → p (if p tt then tt else ff) ≡ tt
  right-side f = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) f)) pr
Searchable.def2 𝔹Searchable' p tt pr = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then tt else ff) pr)) pr

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin n
  fsucc  : {n : ℕ} (i : Fin n) → Fin (succ n)

raise : ∀ {n} → Fin n → Fin (succ n)
raise fzero = fzero
raise (fsucc x) = fsucc (raise x)

top : ∀ n → Fin n
top zero = fzero
top (succ n) = fsucc (top n)

_=Fin_ : ∀ {n} → Fin n → Fin n → 𝔹
fzero =Fin fzero = tt
fsucc f₁ =Fin fsucc f₂ = f₁ =Fin f₂
_ =Fin _ = ff

lower : ∀ {n} → Fin (succ n) → Fin n
lower {succ n} (fsucc f) = fsucc (lower {n} f)
lower  _ = fzero

raiselower : ∀ n → (f : Fin n) → (lower (raise f) ≡ f)
raiselower zero fzero = refl
raiselower (succ n) fzero = refl
raiselower (succ n) (fsucc f) = cong≡ (λ ■ → fsucc ■) (raiselower n f)

lowerraise : ∀ n → (f : Fin (succ n)) →  (top (succ n) =Fin f) ≡ ff → (raise (lower f) ≡ f)
lowerraise zero fzero _ = refl
lowerraise zero (fsucc fzero) ()
lowerraise (succ n) fzero _ = refl
lowerraise (succ n) (fsucc f) pr = cong≡ (λ ■ → fsucc ■) (lowerraise n f pr)

=Fin-implies-≡ : ∀ {n} → (f₁ f₂ : Fin n) → (f₁ =Fin f₂) ≡ tt → f₁ ≡ f₂
=Fin-implies-≡ fzero fzero refl = refl
=Fin-implies-≡ fzero (fsucc _) ()
=Fin-implies-≡ (fsucc _) fzero ()
=Fin-implies-≡ (fsucc f₁) (fsucc f₂) pr = cong≡ (λ ■ → fsucc ■) (=Fin-implies-≡ f₁ f₂ pr)

finSearchable' : ∀ n → Searchable (Fin n) → Searchable (Fin (succ n))
Searchable.ε (finSearchable' zero ℰF) p = if p (fsucc fzero) then fsucc fzero else raise fzero
Searchable.ε (finSearchable' (succ n) ℰF) p = if (p topElement) then (topElement) else raise (Searchable.ε ℰF (λ x → p (raise x))) where
  topElement : Fin (succ (succ n))
  topElement = top (succ (succ n))
Searchable.def2 (finSearchable' zero ℰF) p fzero pr = ∨-elim (𝔹LEM (p (fsucc fzero))) left right where
  left : p (fsucc fzero) ≡ tt → p (if p (fsucc fzero) then fsucc fzero else fzero) ≡ tt
  left pr₁ = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr₁))) pr₁
  right : p (fsucc fzero) ≡ ff → p (if p (fsucc fzero) then fsucc fzero else fzero) ≡ tt
  right pr₁ = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr₁)) pr
Searchable.def2 (finSearchable' zero ℰF) p (fsucc fzero) pr = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr))) pr
Searchable.def2 (finSearchable' (succ n) ℰF) p x₀ pr = ∨-elim (𝔹LEM (p topElement)) left right where
  topElement : Fin (succ (succ n))
  topElement = top (succ (succ n))
  left : p topElement ≡ tt → p (if p topElement then topElement else raise ((Searchable.ε ℰF (λ x → p (raise x))))) ≡ tt
  left pr₁ = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then topElement else raise (Searchable.ε ℰF (λ x → p (raise x)))) pr₁))) pr₁
  right : p topElement ≡ ff → p (if p topElement then topElement else raise ((Searchable.ε ℰF (λ x → p (raise x))))) ≡ tt
  right pr₁ = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then topElement else raise (Searchable.ε ℰF (λ x → p (raise x)))) pr₁))) IH where
    IH : p (raise (Searchable.ε ℰF (λ x → p (raise x)))) ≡ tt
    IH = ∨-elim (𝔹LEM (topElement =Fin x₀)) IHleft IHright where
      IHleft : (topElement =Fin x₀) ≡ tt → p (raise (Searchable.ε ℰF (λ x → p (raise x)))) ≡ tt 
      IHleft pr₃ = EFQ (trans≡ (cong≡ (λ ■ → p ■) (=Fin-implies-≡ topElement x₀ pr₃)) pr) pr₁
      IHright : (topElement =Fin x₀) ≡ ff → p (raise (Searchable.ε ℰF (λ x → p (raise x)))) ≡ tt 
      IHright pr₃ = IHH where
        IHH : p (raise (Searchable.ε ℰF (λ x → p (raise x)))) ≡ tt
        IHH = Searchable.def2 ℰF (λ x → p (raise x)) (lower x₀) (trans≡ (cong≡ (λ ■ → p ■) (lowerraise (succ n) x₀ pr₃)) pr)

finSearchable : ∀ size → Searchable (Fin size)
Searchable.ε (finSearchable zero) p = fzero
Searchable.def2 (finSearchable zero) p fzero pr = pr
finSearchable (succ size) = finSearchable' size (finSearchable size)

FinSetSearchable : {A : Set} → (size : ℕ) (f : Fin size → A) (t : A → Fin size) (ft : ∀ x → f (t x) ≡ x) → Searchable A
Searchable.ε (FinSetSearchable size f _ _) p = f (Searchable.ε (finSearchable size) (λ x → p (f x)))
Searchable.def2 (FinSetSearchable size f t ft) p x₀ pr = Searchable.def2 (finSearchable size) (λ x → p (f x)) (t x₀) (trans≡ (cong≡ (λ ■ → p ■) (ft x₀)) pr)

𝟙Searchable : Searchable 𝟙
𝟙Searchable = FinSetSearchable 0 f t ft where
  f = λ _ → ⋆
  t = λ _ → fzero
  ft : ∀ x → f (t x) ≡ x
  ft ⋆ = refl

𝔹Searchable : Searchable 𝔹
𝔹Searchable = FinSetSearchable 1 f t ft where
  f : Fin 1 → 𝔹
  f fzero = ff
  f (fsucc fzero) = tt
  t : 𝔹 → Fin 1
  t ff = fzero
  t tt = fsucc fzero
  ft : ∀ x → f (t x) ≡ x
  ft ff = refl
  ft tt = refl

𝕓Searchable : Searchable 𝕓
𝕓Searchable = FinSetSearchable 1 f t ft where
  f : Fin 1 → 𝕓
  f fzero = ₀
  f (fsucc fzero) = ₁
  t : 𝕓 → Fin 1
  t ₀ = fzero
  t ₁ = fsucc fzero
  ft : ∀ x → f (t x) ≡ x
  ft ₀ = refl
  ft ₁ = refl

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

×Searchable : {A B : Set} → Searchable A → Searchable B → Searchable (A × B)
Searchable.ε (×Searchable {A} {B} ℰA ℰB) p = a , b where
  a : A
  a = Searchable.ε ℰA (λ x → forsome (Searchable.ε ℰB) (λ x' → p (x , x')))
  b : B
  b = Searchable.ε ℰB (λ x' → p (a , x')) 
Searchable.def2 (×Searchable {A} {B} ℰA ℰB) p (πx₁ , πx₂) pr = proof where
  a : A
  a = Searchable.ε ℰA (λ x → forsome (Searchable.ε ℰB) (λ x' → p (x , x')))
  b : B
  b = Searchable.ε ℰB (λ x' → p (a , x'))
  proof : (λ b → p (a , b)) b ≡ tt
  proof = Searchable.def2 ℰB (λ x → p (a , x)) b (Searchable.def2 ℰA ((λ x → forsome (Searchable.ε ℰB) (λ x' → p (x , x')))) πx₁ (Searchable.def2 ℰB (λ x' → p (πx₁ , x')) πx₂ pr))

ℰℕ : ℕ → ℰ ℕ
ℰℕ zero p = zero
ℰℕ (succ n) p = if (p (succ n)) then (succ n) else (ℰℕ n p)

{-# TERMINATING #-}
ℰℕ→ : {d : Set} → (ℕ → ℰ d) → ℰ (ℕ → d)
ℰℕ→ {d} e p n = e n (λ x → q n x (ℰℕ→ (λ i → e (n +ℕ succ i)) (q n x))) where
  q : ℕ → d → (ℕ → d) → 𝔹
  q n x a = p (λ i → if (i <ℕ n) then (ℰℕ→ e p i)
                     else (if (i =ℕ n) then (x) else a (i −ℕ succ n)))

ℰℂ : ℰ ℂ
ℰℂ = ℰℕ→ (λ i → Searchable.ε 𝕓Searchable)
