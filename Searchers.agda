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
ℰℕ (succ n) p = if (p (succ n)) then (succ n) else (ℰℕ n p)

--             def2 : (p : D → 𝔹) → (x : D)  → p x ≡ tt                                 → (p (ε p)) ≡ tt
ℕComp : ∀ n → (p : ℕ → 𝔹) → (x₀ : ℕ) → (p x₀ ≡ tt) → ((x₀ ≤ℕ n) ≡ tt) → (p (ℰℕ n p)) ≡ tt
ℕComp zero p zero pr lt = pr
ℕComp zero p (succ x₀) pr ()
ℕComp (succ n) p x₀ pr lt = ∨-elim (𝔹LEM (p (succ n))) left right where
  left : p (succ n) ≡ tt → p (if p (succ n) then (succ n) else ℰℕ n p) ≡ tt
  left x = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then (succ n) else ℰℕ n p) x)) x
  right : p (succ n) ≡ ff → p (if p (succ n) then (succ n) else ℰℕ n p) ≡ tt
  right x = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then (succ n) else ℰℕ n p) x)) (ℕComp n p x₀ pr (super x₀ n (therefore x₀ (succ n) pr x) lt)) where
    therefore : ∀ a b → p a ≡ tt → p b ≡ ff → (a =ℕ b) ≡ ff
    therefore a b x₁ x₂ = ∨-elim (𝔹LEM (a =ℕ b)) (λ x₃ → EFQ (trans≡ (sym≡ (cong≡ p (equals a b x₃))) x₁) x₂) (λ z → z) where
      equals : ∀ a b → (a =ℕ b) ≡ tt → a ≡ b
      equals zero zero x₃ = refl
      equals zero (succ _) ()
      equals (succ _) zero ()
      equals (succ a) (succ b) x₃ = cong≡ (λ ■ → succ ■) (equals a b x₃)
    super : ∀ a b → (a =ℕ succ b) ≡ ff → (a ≤ℕ succ b) ≡ tt → (a ≤ℕ b) ≡ tt
    super zero zero x₁ x₂ = refl
    super zero (succ b) x₁ x₂ = refl
    super (succ a) zero x₁ x₂ = EFQ (mini a x₂) x₁ where
      mini : ∀ a → (succ a ≤ℕ succ zero) ≡ tt → (a =ℕ zero) ≡ tt
      mini zero _ = refl
      mini (succ _) ()
    super (succ a) (succ b) x₁ x₂ = super a b x₁ x₂

ℰ𝕓 : ℰ 𝕓
ℰ𝕓 p = if (p ₁) then (₁) else (₀)

ℰ× : {d d' : Set} → ℰ d → ℰ d' → ℰ (d × d')
ℰ× {d} {d'} e e' p = x2 , x'2 where
  x2 : d
  x2 = e (λ x → forsome e' (λ x' → p (x , x')))
  x'2 : d'
  x'2 = e' (λ x' → p (x2 , x'))

fst : {A B : Set} → A × B → A
fst (a , _) = a
snd : {A B : Set} → A × B → B
snd (_ , b) = b

-- (p : D → 𝔹) → (x : D) → p x ≡ tt → (p (ε p)) ≡ tt

×Searchable : {A B : Set} → Searchable A → Searchable B → Searchable (A × B)
Searchable.ε (×Searchable {A} {B} ℰA ℰB) p = a , b where
  a : A
  a = Searchable.ε ℰA (λ x → forsome (Searchable.ε ℰB) (λ x' → p (x , x')))
  b : B
  b = Searchable.ε ℰB (λ x' → p (a , x')) 
Searchable.def2 (×Searchable {A} {B} ℰA ℰB) p x₀ pr = h where
  surely : (ab : A × B) → p ab ≡ tt → p (fst ab , snd ab) ≡ tt
  surely (_ , _) x₂ = x₂
  a : A
  a = Searchable.ε ℰA (λ x → forsome (Searchable.ε ℰB) (λ x' → p (x , x')))
  b : B
  b = Searchable.ε ℰB (λ x' → p (a , x'))
  h1 : (λ a → p (a , snd x₀)) (Searchable.ε ℰA (λ a → p (a , snd x₀))) ≡ tt
  h1 = Searchable.def2 ℰA (λ x → p (x , snd x₀)) (fst x₀) (surely x₀ pr)
  h2 : p (a , snd x₀) ≡ tt
  h2 = ⋆⟪TODO⟫⋆
  h : p (a , b) ≡ tt
  h = ⋆⟪TODO⟫⋆

{-# TERMINATING #-}
ℰℕ→ : {d : Set} → (ℕ → ℰ d) → ℰ (ℕ → d)
ℰℕ→ {d} e p n = e n (λ x → q n x (ℰℕ→ (λ i → e (n +ℕ succ i)) (q n x))) where
  q : ℕ → d → (ℕ → d) → 𝔹
  q n x a = p (λ i → if (i <ℕ n) then (ℰℕ→ e p i)
                     else (if (i =ℕ n) then (x) else a (i −ℕ succ n)))

ℰℂ : ℰ ℂ
ℰℂ = ℰℕ→ (λ i → ℰ𝕓)

-- ℰℝ : ℕ → ℰ ℝ
-- ℰℝ n = ℰ× (ℰℕ n) ℰℂ

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

funSearchable : ∀ n → Searchable (Fin n) → Searchable (Fin (succ n))
Searchable.ε (funSearchable zero ℰF) p = if p (fsucc fzero) then fsucc fzero else raise fzero
Searchable.ε (funSearchable (succ n) ℰF) p = if (p topElement) then (topElement) else raise (Searchable.ε ℰF (λ x → p (raise x))) where
  topElement : Fin (succ (succ n))
  topElement = top (succ (succ n))
Searchable.def2 (funSearchable zero ℰF) p fzero pr = ∨-elim (𝔹LEM (p (fsucc fzero))) left right where
  left : p (fsucc fzero) ≡ tt → p (if p (fsucc fzero) then fsucc fzero else fzero) ≡ tt
  left pr₁ = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr₁))) pr₁
  right : p (fsucc fzero) ≡ ff → p (if p (fsucc fzero) then fsucc fzero else fzero) ≡ tt
  right pr₁ = trans≡ (cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr₁)) pr
Searchable.def2 (funSearchable zero ℰF) p (fsucc fzero) pr = trans≡ ((cong≡ (λ ■ → p ■) (cong≡ (λ ■ → if ■ then fsucc fzero else fzero) pr))) pr
Searchable.def2 (funSearchable (succ n) ℰF) p x₀ pr = ∨-elim (𝔹LEM (p topElement)) left right where
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


-- trans≡ (cong≡ (λ ■ → p ■) conjecture) pr where
--        conjecture : raise (Searchable.ε ℰF (λ x → p (raise x))) ≡ x₀
--        conjecture = {!!}
