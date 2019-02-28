open import Agda.Primitive
 using (Level; _⊔_; lzero; lsuc)

postulate ⋆⟪TODO⟫⋆ : {A : Set} → A

data 𝔹 : Set where
  ff tt : 𝔹
{-# BUILTIN BOOL 𝔹  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}

_=𝔹_ : 𝔹 → 𝔹 → 𝔹
tt =𝔹 tt = tt
ff =𝔹 ff = tt
_ =𝔹 _ = ff

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f

!_ : 𝔹 → 𝔹
! tt = ff
! ff = tt

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && tt = tt
_ && _ = ff

_∣∣_ : 𝔹 → 𝔹 → 𝔹
ff ∣∣ ff = ff
_ ∣∣ _ = tt

data 𝕓 : Set where
  ₀ ₁ : 𝕓

_=𝕓_ : 𝕓 → 𝕓 → 𝔹
₀ =𝕓 ₀ = tt
₁ =𝕓 ₁ = tt
_ =𝕓 _ = ff

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_=ℕ_ : ℕ → ℕ → 𝔹
zero =ℕ zero = tt
(succ n) =ℕ (succ m) = n =ℕ m
_ =ℕ _ = ff
{-# BUILTIN NATEQUALS _=ℕ_ #-}

_<ℕ_ : ℕ → ℕ → 𝔹
_ <ℕ zero = ff
zero <ℕ succ m = tt
(succ n) <ℕ (succ m) = n <ℕ m
{-# BUILTIN NATLESS _<ℕ_ #-}

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ m = m
(succ n) +ℕ m = succ (n +ℕ m)
{-# BUILTIN NATPLUS _+ℕ_ #-}

_≤ℕ_ : ℕ → ℕ → 𝔹
n ≤ℕ m = (n =ℕ m) ∣∣ (n <ℕ m)

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ m = zero
succ n *ℕ m = m +ℕ (n *ℕ m)
{-# BUILTIN NATTIMES _*ℕ_ #-}

_−ℕ_ : ℕ → ℕ → ℕ
zero −ℕ m = zero
n −ℕ zero = n
(succ n) −ℕ (succ m) = n −ℕ m
{-# BUILTIN NATMINUS _−ℕ_ #-}

maxℕ : ℕ → ℕ → ℕ
maxℕ zero m = m
maxℕ n zero = n
maxℕ (succ n) (succ m) = succ (maxℕ n m)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym≡ : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym≡ refl = refl

trans≡ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans≡ refl refl = refl

cong≡ : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong≡ f refl = refl
  
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

π₁ : {A B : Set} → A × B → A
π₁ (a , b) = a

π₂ : {A B : Set} → A × B → B
π₂ (a , b) = b

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  _&_ : A → B → A ∧ B

∨-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
∨-elim (inl a) c _ = c a
∨-elim (inr b) _ c = c b

𝔹LEM : (b : 𝔹) → (b ≡ tt) ∨ (b ≡ ff)
𝔹LEM ff = inr refl
𝔹LEM tt = inl refl

_⊕_ : 𝔹 → 𝔹 → Set
a ⊕ b = ((a ≡ tt) ∧ (b ≡ ff)) ∨ ((a ≡ ff) ∧ (b ≡ tt))

data ∃ {X : Set} (P : X → Set) : Set where
  _⇒_ : (w : X) → P w → ∃ (λ x → P x)

postulate FunExt : {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

EFQ : {A : Set} → ∀ {a} → a ≡ tt → a ≡ ff → A
EFQ {A} {ff} () x₁
EFQ {A} {tt} x ()
