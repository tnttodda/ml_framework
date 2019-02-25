postulate ⋆⟪TODO⟫⋆ : {A : Set} → A

data 𝔹 : Set where
  ff tt : 𝔹

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f

!_ : 𝔹 → 𝔹
! tt = ff
! ff = tt

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && tt = tt
_ && _ = ff

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

_<ℕ_ : ℕ → ℕ → 𝔹
zero <ℕ m = !(m =ℕ zero)
(succ n) <ℕ zero = ff
(succ n) <ℕ (succ m) = n <ℕ m

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ m = m
(succ n) +ℕ m = n +ℕ (succ m)

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ m = zero
succ n *ℕ m = m +ℕ (n *ℕ m)

_−ℕ_ : ℕ → ℕ → ℕ
zero −ℕ m = zero
n −ℕ zero = n
(succ n) −ℕ (succ m) = n −ℕ m

maxℕ : ℕ → ℕ → ℕ
maxℕ zero m = m
maxℕ n zero = n
maxℕ (succ n) (succ m) = maxℕ n m

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
  
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

π₁ : {A B : Set} → A × B → A
π₁ = _×_.fst

π₂ : {A B : Set} → A × B → B
π₂ = _×_.snd

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

data Vec {a} (A : Set a) : ℕ → Set a where
  ⟦⟧  : Vec A zero
  _∺_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (succ n)

data Fin : ℕ → Set where
  zro : {n : ℕ} → Fin (succ n)
  suc : {n : ℕ} (i : Fin n) → Fin (succ n)

data _[_]=_ {A : Set} : {n : ℕ} → Vec A n → Fin n → A → Set where
  here  : ∀ {n}       {x}   {xs : Vec A n} → (x ∺ xs) [ zro ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n} (xs[i]=x : xs [ i ]= x) → (y ∺ xs) [ suc i ]= x

Subset : ℕ → Set
Subset = Vec 𝔹

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= tt

_⊆_ : ∀ {n} → Subset n → Subset n → Set
s₁ ⊆ s₂ = ∀ {x} → x ∈ s₁ → x ∈ s₁
