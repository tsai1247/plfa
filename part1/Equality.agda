module plfa.part1.Equality where

data _≡_  { A  :  Set }  ( x  :  A )  :  A  →  Set  where
  refl  :  x  ≡  x
infix  4  _≡_

sym : ∀{A : Set} {x y : A}
    → x ≡ y → y ≡ x

sym refl = refl

trans : ∀{A : Set} {x y z : A}
    → x ≡ y → y ≡ z
    → x ≡ z

trans refl refl = refl

cong : ∀{A B : Set} (f : A → B) {x y : A}
    → x ≡ y
    → f x ≡ f y
cong f refl = refl

cong₂ : ∀{A B C : Set} (f : A → B → C )  {u x : A} {v y : B} 
  → u ≡ x → v ≡ y 
  → f u v ≡ f x y 
cong₂ f refl refl = refl

cong-app : ∀{A B : Set} {f g : A → B} 
  → f ≡ g → ∀(x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀{A : Set} {x y : A} (P : A → Set)
    → x ≡ y
    → P x → P y
subst P refl px = px


module ≡-Reasoning {A : Set} where

  infix  1 begin_ 
  infixr 2 _≡⟨⟩_  _≡⟨_⟩_ 
  infix  3 _∎

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y 
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀(x : A) {y : A} → x ≡ y → x ≡ y 
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀(x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z 
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀(x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : ∀{A : Set} {x y z : A}
    → x ≡ y → y ≡ z
    → x ≡ z

trans′ {A} {x} {y} {z} xey yez = 
    begin
        x
    ≡⟨ xey ⟩
        y
    ≡⟨ yez ⟩
        z
    ∎
    
--  trans x≡y (trans y≡z refl)

{- 
    begin 
    (
        x ≡⟨ x≡y ⟩ 
        (
            y ≡⟨ y≡z ⟩
            (
                z ∎
            )
        )
    )
-}

-- trans : 因為循環論證，因此無法使用 ≡-Reasoning 來證明 trans

data ℕ  :  Set  where
  zero  :  ℕ
  suc   :  ℕ  →  ℕ

_+_  :  ℕ  →  ℕ  →  ℕ 
zero     +  n   =   n 
( suc  m )  +  n   =   suc  ( m  +  n )

infix  5  _+_

postulate
  +-identity  :  ∀  ( m  :  ℕ )  →  m  +  zero  ≡  m
  +-suc  :  ∀  ( m  n  :  ℕ )  →  m  +  suc  n  ≡  suc  ( m  +  n )

+-comm  :  ∀  ( m  n  :  ℕ )  →  m  +  n  ≡  n  +  m 
+-comm  m  zero  = 
  begin 
    m  +  zero 
  ≡⟨  +-identity  m  ⟩ 
    m 
  ≡⟨⟩ 
    zero  +  m 
  ∎ 
+-comm  m  ( suc  n )  = 
  begin 
    m  +  suc  n 
  ≡⟨  +-suc  m  n  ⟩ 
    suc  ( m  +  n) 
  ≡⟨  cong  suc  ( +-comm  m  n )  ⟩ 
    suc  ( n  +  m ) 
  ≡⟨⟩ 
    suc  n  +  m 
  ∎

data _≤_ : (ℕ → ℕ → Set) where
    z≤m : ∀{m : ℕ} → zero ≤ m
    s≤s : ∀{m n : ℕ} → m ≤ n → (suc m) ≤ (suc n)
    eq≤eq : ∀{m n : ℕ} → m ≡ n → m ≤ n

infix  4  _≤_
postulate
    ≤-ident : ∀{m : ℕ} → m ≤ m
    ≤-trans : ∀{m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

module ≤-Reasoning where
  infix  1 begin₁_ 
  infixr 2 _≤⟨⟩_  _≤⟨_⟩_ 
  infix  3 _∎₁

  begin₁_ : ∀{x y : ℕ} → x ≤ y → x ≤ y 
  begin₁ x≤y = x≤y

  _≤⟨⟩_ : ∀(x : ℕ) {y : ℕ} → x ≤ y → x ≤ y 
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀(x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z 
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤₂⟨_⟩_ : ∀(x : ℕ) {y z : ℕ} → x ≤ y → y ≡ z → x ≤ z 
  x ≤₂⟨ x≤y ⟩ y≡z = ≤-trans x≤y (eq≤eq y≡z)

  _≤₃⟨_⟩_ : ∀(x : ℕ) {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z 
  x ≤₃⟨ x≡y ⟩ y≤z = ≤-trans (eq≤eq x≡y) y≤z

  _∎₁ : ∀(x : ℕ) → x ≤ x
  x ∎₁ = ≤-ident

open ≤-Reasoning
{-#  BUILTIN  EQUALITY  _≡_  #-}

+-monoʳ-≤ : ∀(n p q : ℕ) 
    → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = 
    begin₁
        (zero + p)
    ≤⟨ p≤q ⟩
        q
    ∎₁

+-monoʳ-≤ (suc n) p q p≤q = 
    begin₁ 
        (suc n) + p
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
        (suc n) + q
    ∎₁

+-monoˡ-≤ : ∀(m n p : ℕ)
  → m ≤ n → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = 
    begin₁
        p + m
    ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
        p + n
    ∎₁
        

data even : ℕ → Set 
data odd  : ℕ → Set

data even where
  zero : even zero
  suc : ∀{n : ℕ}
    → odd n → even(suc n)

data odd where
  suc : ∀{n : ℕ}
    → even n → odd(suc n)
    
even-comm : ∀ (m n : ℕ) 
  → even (m + n) → even (n + m) 
even-comm m n ev rewrite +-comm n m = ev

+-comm′ : ∀(m n : ℕ) → m + n ≡ n + m 
+-comm′ zero n rewrite +-identity n = refl 
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl


even-comm′ : ∀ (m n : ℕ) 
  → even (m + n) → even (n + m) 
even-comm′ m n ev with m + n | +-comm m n
...                 | .(n + m) | refl = ev
{-
    m + n 區塊套用 +-comm m n 
    改變後與 .(n + m) 中的 n + m 經由 refl 證明相等
    全式最終改為 → even (n + m) → even (n + m) 
-}

even-comm⁻ : ∀ (m n : ℕ) 
  → even (m + n) → even (n + m) 
even-comm⁻ m n = subst even (+-comm m n)

_≐_ : ∀{A : Set} (x y : A) → Set₁ 
_≐_ {A} x y = ∀(P : A → Set) 
    → P x → P y

refl-≐ : ∀{A : Set} {x : A} 
  → x ≐ x 
refl-≐ P Px = Px

trans-≐ : ∀{A : Set} {x y z : A} 
  → x ≐ y → y ≐ z → x ≐ z 
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)
{-
P Px 是指
P: A → Set 的證明
Px: P x 的證明
因此 x≐y 經過 P Px 後 可以得到 P y 的證明
-}

sym-≐ : ∀{A : Set} {x y : A} 
  → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy 
  where 
    Q   :   A → Set 
    Q z = P z → P x 
    Qx  : Q x
    Qx  = refl-≐ P
    Qy  : Q y 
    Qy  = x≐y Q Qx -- 對於所有的Q， Q x 成立時， Q y 成立。這是 x≐y Q Qx的保證
                   -- 因此 Qy 被證明
                   -- Qy 被定義為 Q y ，也就是 P y → P x ，即為所求

≡-implies-≐ : ∀{A : Set} {x y : A} 
    → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀{A : Set} {x y : A} 
  → x ≐ y → x ≡ y

≐-implies-≡ {A} {x} {y} x≐y = Qy
    where
        Q : A → Set
        Q z = x ≡ z
        Qx : Q x
        Qx = refl
        Qy : Q y
        Qy = x≐y Q Qx

open import Level using (Level ; _⊔_ ) renaming (zero to lzero ; suc to lsuc)

{-
lzero : Level
lsuc  : Level → Level

Set₀ ≡ Set lzero
Set₁ ≡ (lsuc lzero)
Set₂ ≡ (lsuc (lsuc lzero))

_⊔_ : Level → Level → Level
-}

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} 
  → x ≡′ y → y ≡′ x 
sym′ refl′ = refl′

_≐′_ : ∀{ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ) 
_≐′_ {ℓ} {A} x y = ∀(P : A → Set ℓ) → P x → P y

_∘_ : ∀{ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)