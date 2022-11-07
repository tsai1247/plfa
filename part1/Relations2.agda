module  plfa.part1.Relations2  where
import  Relation.Binary.PropositionalEquality  as  Eq 
open  Eq  using  ( _≡_ ;  refl ;  cong ) 
open  import  Data.Nat  using  ( ℕ ;  zero ;  suc ;  _+_ ; _*_) 
open  import  Data.Nat.Properties  using  ( +-comm ; *-comm ; +-identityʳ )

data _≤_  :  ℕ  →  ℕ  →  Set  where

  z≤n  :  ∀  { n  :  ℕ } 
      -------- 
    →  zero  ≤  n

  s≤s  :  ∀  { m  n  :  ℕ } 
    →  m  ≤  n 
      ------------- 
    →  suc  m  ≤  suc  n

0≤2 : 0 ≤ 2
0≤2 = z≤n

1≤3 : 1 ≤ 3
1≤3 = s≤s 0≤2

2≤4 : 2 ≤ 4
2≤4 = s≤s 1≤3

0≤any : ∀{n : ℕ}
    → 0 ≤ n
0≤any = z≤n
-- 0 ≤ anything

sucm≤sucn : ∀{m n : ℕ}
    → m ≤ n → suc m ≤ suc n
sucm≤sucn = s≤s
-- if m ≤ n then suc m ≤ suc n

+-identityʳ′  :  ∀  { m  :  ℕ }  →  m  +  zero  ≡  m 
+-identityʳ′ {m = m₁}  =  +-identityʳ m₁
-- 可以用 c-c c-n 看 +-identityʳ′

infix  4  _≤_
-- (1 + 2) ≤ 3 ≡ 1 + 2 ≤ 3

inv-s≤s  :  ∀  { m  n  :  ℕ } 
  →  suc  m  ≤  suc  n 
    ------------- 
  →  m  ≤  n 

inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n  :  ∀  { m  :  ℕ } 
  →  m  ≤  zero 
    -------- 
  →  m  ≡  zero 
inv-z≤n {zero} z≤n = refl

-- Reflexive, Transitive, Anti-symmetric, Total
--              Preorder,  Partial Order, Total Order

{-
給出一個不是偏序的預序的例子: ?
給出一個不是全序的偏序的例子: ?
-}

≤-refl  :  ∀  { n  :  ℕ } 
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans  :  ∀  { m  n  p  :  ℕ } 
  →  m  ≤  n 
  →  n  ≤  p 
    ----- 
  →  m  ≤  p 

≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym  :  ∀  { m  n  :  ℕ } 
  →  m  ≤  n 
  →  n  ≤  m 
    ----- 
  →  m  ≡  n 

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
{-
≤-antisym  z≤n {m = zero} {n = n} s≤s {m = suc n} {n = suc m} = ?
  → {m = zero} {m = suc n} → zero ≡ suc n → (suc n ≟ zero) → ⊥
-}

data Total  ( m  n  :  ℕ )  :  Set  where

  forward  : 
      m  ≤  n 
      --------- 
    →  Total  m  n

  flipped  : 
      n  ≤  m 
      --------- 
    →  Total  m  n

-- Total m n
helper : ∀ {m n : ℕ} → Total m n → Total (suc m) (suc n)
helper (forward x) = forward (s≤s x)
helper (flipped x) = flipped (s≤s x)

≤-total  :  ∀  ( m  n  :  ℕ )  →  Total  m  n 
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n 
...                | forward x = forward (s≤s x)
...                | flipped x = flipped (s≤s x)
-- with (≤-total m n) is forward x, then equals forward (s≤s x)
-- with (≤-total m n) is flipped x, then equals flipped (s≤s x)

{-
a.k.a below: 
≤-total (suc m) (suc n) = helper (≤-total m n)
-}

+-monoʳ-≤  :  ∀  ( n  p  q  :  ℕ ) 
  →  p  ≤  q 
    ------------- 
  →  n  +  p  ≤  n  +  q 

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤  :  ∀  ( m  n  p  :  ℕ ) 
  →  m  ≤  n 
    ------------- 
  →  m  +  p  ≤  n  +  p 

+-monoˡ-≤ m n p m≤n rewrite (+-comm m p) | (+-comm n p) = +-monoʳ-≤ p m n m≤n

+-mono-≤  :  ∀  ( m  n  p  q  :  ℕ ) 
  →  m  ≤  n 
  →  p  ≤  q 
    ------------- 
  →  m  +  p  ≤  n  +  q 

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤  :  ∀  ( n  p  q  :  ℕ ) 
  →  p  ≤  q 
    ------------- 
  →  n  *  p  ≤  n  *  q 

*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀  ( m  n  p  :  ℕ ) 
  →  m  ≤  n 
    ------------- 
  →  m  *  p  ≤  n  *  p 
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤  :  ∀  ( m  n  p  q  :  ℕ ) 
  →  m  ≤  n 
  →  p  ≤  q 
    ------------- 
  →  m  *  p  ≤  n  *  q 

*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix  4  _<_

data _<_  :  ℕ  →  ℕ  →  Set  where

  z<s  :  ∀  { n  :  ℕ } 
      ------------ 
    →  zero  <  suc  n

  s<s  :  ∀  { m  n  :  ℕ } 
    →  m  <  n 
      ------------- 
    →  suc  m  <  suc  n

<-trans : ∀ {m n p : ℕ}
  → m < n → n < p
  → m < p

<-trans {zero} {suc n} {suc p} m<n n<p = z<s
<-trans {suc m} {suc n} {suc p} (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data trichotomy (m n : ℕ) : Set where
  m<n : m < n → trichotomy m n
  m≡n : m ≡ n → trichotomy m n
  m>n : n < m → trichotomy m n

<-trichotomy : ∀ {m n : ℕ}
  → trichotomy m n 
<-trichotomy {zero} {zero} = m≡n refl
<-trichotomy {zero} {suc n} = m<n z<s
<-trichotomy {suc m} {zero} = m>n z<s
<-trichotomy {suc m} {suc n} with <-trichotomy {m} {n} 
...           | m<n x = m<n (s<s x)
...           | m≡n x = m≡n (cong suc x)
...           | m>n x = m>n (s<s x)


+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q → n + p < n + q
+-monoʳ-< zero p q n<q = n<q
+-monoʳ-< (suc n) p q n<q = s<s (+-monoʳ-< n p q n<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n → m + p < n + p
+-monoˡ-< m n p _m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n _m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n → p < q → m + p < n + q
+-mono-< m n p q _m<n p<q = <-trans (+-monoˡ-< m n p
 _m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀ {m n : ℕ}
  → suc m ≤ n → m < n
≤-iff-< {zero} {suc n} ss_m≤n = z<s
≤-iff-< {suc m} {suc n} (s≤s ss_m≤n) = s<s (≤-iff-< {m} {n} ss_m≤n)

<-iff-≤ : ∀ {m n : ℕ}
  → m < n → suc m ≤ n 
<-iff-≤ {zero} {suc n} _m<n = s≤s z≤n
<-iff-≤ {suc m} {suc n} (s<s _m<n) = s≤s (<-iff-≤ _m<n)

n≤sn : ∀ {n : ℕ}
  → n ≤ suc n
n≤sn {zero} = z≤n
n≤sn {suc n} = s≤s n≤sn

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n → n < p
  → m < p

<-trans-revisited _m<n n<p = ≤-iff-< (≤-trans (≤-trans (<-iff-≤ _m<n) n≤sn ) (<-iff-≤ n<p))

data even  :  ℕ  →  Set 
data odd   :  ℕ  →  Set

data  even  where

  zero  : 
      --------- 
      even  zero

  suc   :  ∀  { n  :  ℕ } 
    →  odd  n 
      ------------ 
    →  even  ( suc  n )

data  odd  where

  suc   :  ∀  { n  :  ℕ } 
    →  even  n 
      ----------- 
    →  odd  ( suc  n )

e+e≡e  :  ∀  { m  n  :  ℕ } 
  →  even  m 
  →  even  n 
    ------------ 
  →  even  ( m  +  n )

o+e≡o  :  ∀  { m  n  :  ℕ } 
  →  odd  m 
  →  even  n 
    ----------- 
  →  odd  ( m  +  n )


e+e≡e zero en = en
e+e≡e (suc x) en = suc (o+e≡o x en)
o+e≡o (suc x) en = suc (e+e≡e x en)

o+o≡e : ∀ {m n : ℕ}
  → odd m 
  → odd n
  → even (m + n)
  
e+o≡o : ∀ {m n : ℕ}
  → even m 
  → odd n
  → odd (m + n)

e+o≡o zero on = on
e+o≡o (suc x) on = suc (o+o≡e x on)
o+o≡e (suc x) on = suc (e+o≡o x on)


