open import Agda.Primitive
 using (Level; _⊔_; lzero; lsuc)

-- Bools, Bits, Nats, Lists, Equality, Product, Sum, Existential, EFQ

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

_||_ : 𝔹 → 𝔹 → 𝔹
ff || ff = ff
_ || _ = tt

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
n ≤ℕ m = (n =ℕ m) || (n <ℕ m)

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

if≡tt : {A : Set} {a₁ a₂ : A} {b : 𝔹} → (b ≡ tt) → (if b then a₁ else a₂) ≡ a₁
if≡tt refl = refl

if≡ff : {A : Set} {a₁ a₂ : A} (b : 𝔹) → (b ≡ ff) → (if b then a₁ else a₂) ≡ a₂
if≡ff _ refl = refl
  
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

π₁ : {A B : Set} → A × B → A
π₁ (a , b) = a

π₂ : {A B : Set} → A × B → B
π₂ (a , b) = b

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

∨-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
∨-elim (inl a) c _ = c a
∨-elim (inr b) _ c = c b

𝔹LEM : (b : 𝔹) → (b ≡ tt) ∨ (b ≡ ff)
𝔹LEM ff = inr refl
𝔹LEM tt = inl refl

𝕓LEM : (b : 𝕓) → (b ≡ ₀) ∨ (b ≡ ₁)
𝕓LEM ₀ = inl refl
𝕓LEM ₁ = inr refl

data _∧_ (A B : Set) : Set where
  _&_ : A → B → A ∧ B

∧l : {A B : Set} → A ∧ B → A
∧l (a & _) = a
∧r : {A B : Set} → A ∧ B → B
∧r (_ & b) = b

_⊕_ : 𝔹 → 𝔹 → Set
a ⊕ b = ((a ≡ tt) ∧ (b ≡ ff)) ∨ ((a ≡ ff) ∧ (b ≡ tt))

data ∃ {X : Set} (P : X → Set) : Set where
  _⇒_ : (w : X) → P w → ∃ (λ x → P x)

Π₀ : {X : Set} {A : X → Set} → (∃ \(x : X) → A x) → X
Π₀(x ⇒ _) = x
Π₁ : {X : Set} {A : X → Set} → (z : ∃ \(x : X) → A x) → A(Π₀ z)
Π₁(_ ⇒ a) = a

EFQ : {A : Set} → ∀ {a} → a ≡ tt → a ≡ ff → A
EFQ {A} {ff} () x₁
EFQ {A} {tt} x ()

φ𝕓 : 𝕓 → 𝕓 → 𝕓
φ𝕓 ₀ ₀ = ₀
φ𝕓 ₁ ₁ = ₀
φ𝕓 _ _ = ₁

contra : ∀ a → (a ≡ tt → tt ≡ ff) → a ≡ ff
contra a x = ∨-elim (𝔹LEM a) (λ x₁ → trans≡ x₁ (x x₁)) (λ x₁ → x₁)

_&&!_ : ∀ {a b} → a ≡ tt → b ≡ tt → (a && b) ≡ tt
refl &&! refl = refl

&&? : ∀ {a b} → (a ≡ ff) ∨ (b ≡ ff) → (a && b) ≡ ff
&&? {ff} {b} x = refl
&&? {tt} {ff} x = refl
&&? {tt} {tt} (inl ())
&&? {tt} {tt} (inr ())

||! : ∀ {a b} → (a ≡ tt) ∨ (b ≡ tt) → (a || b) ≡ tt
||! {.tt} {b} (inl refl) = refl
||! {ff} {ff} (inr ())
||! {tt} {ff} (inr x) = refl
||! {ff} {tt} (inr refl) = refl
||! {tt} {tt} (inr x) = refl

if-elim : ∀ a {b c} → (a ≡ tt → b ≡ tt) → (a ≡ ff → c ≡ tt) → (if a then b else c) ≡ tt
if-elim ff x₀ x₁ = x₁ refl
if-elim tt x₀ x₁ = x₀ refl

||? : ∀ {a b} → (a ≡ ff) → (b ≡ ff) → (a || b) ≡ ff
||? refl refl = refl

&&l : ∀ {a b} → (a && b) ≡ tt → a ≡ tt
&&l {tt} _ = refl
&&l {ff} ()

&&r : ∀ {b a} → (a && b) ≡ tt → b ≡ tt
&&r {tt} _ = refl
&&r {ff} {ff} ()
&&r {ff} {tt} ()

||l : ∀ {a b} → (a || b) ≡ ff → (a ≡ ff)
||l {ff} _ = refl
||l {tt} ()

||r : ∀ {b a} → (a || b) ≡ ff → (b ≡ ff)
||r {ff} _ = refl
||r {tt} {ff} ()
||r {tt} {tt} ()

&&rl : ∀ {a b} → (a && b) ≡ ff → b ≡ tt → a ≡ ff
&&rl {ff} _ _ = refl
&&rl {_} {ff} _ ()
&&rl {tt} {tt} () _

&&rf : ∀ {a b} → (a && b) ≡ ff → a ≡ tt → b ≡ ff
&&rf {_} {ff} _ _ = refl
&&rf {ff} _ () 
&&rf {tt} {tt} () _

||rt : ∀ {a b} → (a || b) ≡ tt → a ≡ ff → b ≡ tt
||rt {_} {tt} _ _ = refl
||rt {ff} {ff} () _
||rt {tt} {ff} _ ()

||lt : ∀ {a b} → (a || b) ≡ tt → b ≡ ff → a ≡ tt
||lt {tt} _ _ = refl
||lt {ff} {tt} _ ()
||lt {ff} {ff} () _

MT : ∀ {a b} → (a ≡ tt → b ≡ tt) → b ≡ ff → a ≡ ff 
MT {ff} {ff} x₁ x₂ = refl
MT {ff} {tt} x₁ x₂ = refl
MT {tt} {ff} x₁ refl = sym≡ (x₁ refl)
MT {tt} {tt} x₁ ()
