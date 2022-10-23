module  plfa.part1.Relations  where
import  Relation.Binary.PropositionalEquality  as  Eq 
open  Eq  using  ( _≡_ ;  refl ;  cong ) 
open  import  Data.Nat  using  ( ℕ ;  zero ;  suc ;  _+_ ; _*_) 
open  import  Data.Nat.Properties  using  ( +-comm ;  +-identityʳ ; *-comm )

data _≤_ : ( ℕ → ℕ → Set ) where
  z≤n : ∀{n : ℕ}
    → 0 ≤ n

  s≤s : ∀{smaller larger : ℕ} 
    → (smaller ≤ larger → suc smaller ≤ suc larger)

infix  4  _≤_

-- why did ∀{m n : ℕ}  use {} rather than ()?

prove_0≤2  : 0 ≤ 2 
prove_0≤2 = z≤n { n = 2 }

prove_1≤3 : 1 ≤ 3
prove_1≤3 = s≤s {smaller = 0} {larger = 2} ( prove_0≤2 )


_ : 2 ≤ 4 
_ = s≤s {smaller = 1} {larger = 3} (prove_1≤3)


-- +-identityʳ′  :  ∀  { m  :  ℕ }  →  m  +  zero  ≡  m 
-- +-identityʳ′  =  +-identityʳ _ 

inv-s≤s : ∀{m n : ℕ}
  → (suc m ≤ suc n → m ≤ n)
inv-s≤s {m = m} {n = n} (s≤s {smaller = m} {larger = n} m≤n ) = m≤n
{-
  ∀{m n : ℕ} 印證了前提條件P必為真， 因此反演推論 Q→P 必定為真
  因此一假設 P→Q 的反演推論為真的條件為：P在其定義域中總是為真
  這也是可以直接從 s≤s 推導至 inv-s≤s 的原因
-}

inv-z≤n : ∀{m : ℕ}
  → (m ≤ zero → m ≡ zero) -- 對 zero ≤ n 而言，能滿足 m ≤ zero 的 m 值只有zero 
inv-z≤n z≤n = refl
{-
自反（Reflexive）：對於所有的n，關係 n ≤ n 成立。
傳遞（Transitive）：對於所有的m、n和p，如果 m ≤ n 和 n ≤ p 成立，那麼 m ≤ p 也成立。
反對稱（Anti-symmetric）：對於所有的 m 和n，如果 m ≤ n 和 n ≤ m 同時成立，那麼 m ≡ n 成立。
完全（Total）：對於所有的 m 和n，m ≤ n或者 n ≤ m 成立。
-}

≤-refl : ∀{n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n } = s≤s {smaller = n} {larger = n} ≤-refl


≤-trans : ∀{m n p : ℕ}
  → m ≤ n → n ≤ p → m ≤ p
-- c-c c-c m
≤-trans (z≤n {n = n}) _ = z≤n -- zero ≤ n → n ≤ p → zero ≤ p
≤-trans {m = suc m} {n = suc n} {p = suc p}
    (s≤s {smaller = m} {larger = n} m≤n) (s≤s {smaller = n} {larger = p} n≤p) 
  = 
    s≤s {smaller = m} {larger = p} (≤-trans {m = m} {n = n} {p = p} m≤n n≤p) 
{-
  當 m = 0 時(zero ≤ n → n ≤ p)， zero ≤ p 由於 z≤n 公理而得證
  當 m = suc m, n = suc n, p = suc p 時，只要 ( m ≤ n ) → ( n ≤ p ) → ( m ≤ p ) 成立，就可以由 s≤s 公理得證：
    ( suc m ≤ suc n ) → ( suc n ≤ suc p ) → ( suc m ≤ suc p )
-}


≤-anti-sym : ∀{m n : ℕ}
  → m ≤ n → n ≤ m → m ≡ n
≤-anti-sym z≤n z≤n = refl
≤-anti-sym {m = suc m} {n = suc n} (s≤s m≤n) (s≤s n≤m) = cong suc ( ≤-anti-sym {m = m} {n = n} m≤n n≤m )

≤-antisym-cases : ∀{m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym-cases z≤n z≤n rewrite ≤-anti-sym z≤n z≤n = refl
≤-antisym-cases (s≤s m≤n) (s≤s n≤m) rewrite ≤-anti-sym (s≤s m≤n) (s≤s n≤m) = refl
-- ≤-antisym-cases {m = zero} {n = n} (z≤n {n = n}) (s≤s {smaller = n} {larger = m} n≤m) = ? (impossible)
{-
≤-antisym-cases (z≤n) (s≤s a≤b) 的情形中，
  前者代表 zero ≤ n 
  後者代表 suc a ≤ suc b ≡ n ≤ zero ，意即存在 suc a = b 且 suc b = zero 的關係，然而 suc b = zero 的 b 並不在 ℕ 定義的範圍中，因此此情形不可能
error message : 
  The case for the constructor s≤s is impossible because unification ended with a conflicting equation
    suc larger ≟ zero
-}



data Total(m n : ℕ) : Set where
  forward :
    m ≤ n → Total m n

  flipped :
    n ≤ m → Total m n

≤-total : ∀(m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n) 
... | flipped n≤m = flipped (s≤s n≤m)
{- with 跟 where 的互換
≤-total (suc m) (suc n) = helper (≤-total m n) where
  helper : Total m n → Total ( suc m ) ( suc n ) 
  helper ( forward m≤n ) = forward ( s≤s m≤n ) 
  helper ( flipped n≤m ) = flipped ( s≤s n≤m )
-}

+-monoʳ-≤ : ∀(n p q : ℕ)
  → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q = λ z → z
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀(m n p : ℕ)
  → m ≤ n → m + p ≤ n + p

+-monoˡ-≤ m n p rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n 

+-mono-≤ : ∀(m n p q : ℕ)
  → m ≤ n → p ≤ q → m + p ≤ n + q

-- m + p < n + p = n + p < n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀(n p q : ℕ)
  → p ≤ q  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n {n = zero}
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)
-- p + n * p ≤ q + n * q

*-monoˡ-≤ : ∀(m n p : ℕ)
  → m ≤ n  → m * p ≤ n * p
*-monoˡ-≤ m n p rewrite *-comm m p | *-comm n p =  *-monoʳ-≤ p m n

*-mono-≤ : ∀(m n p q : ℕ)
  → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

{-

參數的個數不同的問題：
  在引用 +-mono-≤ : ∀(m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q 時，
    +-mono-≤ ? ? ? ? ? ?
    可以得到 m + p ≤ n + q 的結果
    
  在引用 ≤-trans : ∀{m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p 時，
    ≤-trans ? ? 
    可以得到 m ≤ p 的結果

  → 顯性參考必須寫出所有的參數，隱性參考則不用
  → 何時使用顯性參考；何時使用隱性參考較好？
-}

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀{n : ℕ}
    → zero < suc n
  
  s<s : ∀{smaller larger : ℕ}
    → smaller < larger → suc smaller < suc larger

<-trans : ∀{m n p : ℕ}
  → m < n → n < p → m < p
<-trans {m = m} {n = suc n} {p = suc p} z<s (s<s n<p) = z<s
<-trans {m = suc m} {n = suc n} {p = suc p} (s<s m<n) (s<s n<p) = s<s ( <-trans {m = m} {n = n} {p = p} m<n n<p )


infix 4 _>_
data _>_ : ℕ → ℕ → Set where
  s>s : ∀{smaller larger : ℕ}
    → smaller < larger → larger > smaller

_ : 5 > 0
_ = s>s z<s
  
+-monoʳ-< : ∀(n p q : ℕ)
  → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀(m n p : ℕ)
  → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀(m n p q : ℕ)
  → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans {m = m + p} {n = n + p} {p = n + q} (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀(m n : ℕ)
  → suc m ≤ n → m < n
≤-iff-< zero (suc n) m≤n = z<s
≤-iff-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-< m n m≤n) -- suc suc m ≤ suc n


≤-iff-<′ : ∀(m n : ℕ)
  → m < n → suc m ≤ n
≤-iff-<′ zero (suc n) m<n = s≤s z≤n
≤-iff-<′ (suc m) (suc n) (s<s m<n) = s≤s (≤-iff-<′ m n m<n)

<-trans-revisited : ∀{m n p : ℕ}
  → m < n → n < p → m < p

≤-addone : ∀(p : ℕ)
  → p ≤ suc p
≤-addone zero = z≤n
≤-addone (suc p) = s≤s (≤-addone p)

<-trans-revisited {m = m} {n = n} {p = suc p} m<n n<p = ≤-iff-< m (suc p) (≤-trans (≤-trans (≤-iff-<′ m n m<n) (inv-s≤s (≤-iff-<′  n (suc p) n<p))) (≤-addone p) )

data even : ℕ → Set 
data odd  : ℕ → Set

data even where
  zero : even zero
  suc : ∀{n : ℕ}
    → odd n → even(suc n)

data odd where
  suc : ∀{n : ℕ}
    → even n → odd(suc n)

e+e≡e : ∀{m  n : ℕ} 
  → even m → even n 
  → even (m + n)

o+e≡o : ∀{m  n : ℕ} 
  → odd m → even n
  → odd (m + n)


e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)
{-
    e+e≡e (suc om) en
≡⟨⟩
    e+e≡e (suc odd n) (even n₁)
≡⟨⟩
    e+e≡e (odd (suc n)) (even n₁)
→
    even (n + n₁)

-}


o+e≡o (suc em) en = suc (e+e≡e em en)
{-
    o+e≡o (suc em) en
≡⟨⟩
    o+e≡o (suc even n) (even n₁)
≡⟨⟩
    o+e≡o (even (suc n)) (even n₁)
→
    odd (n + n₁)
-}

e+o≡o : ∀{m n : ℕ}
  → even m → odd n
  → odd(m + n)

o+o≡e : ∀{m n : ℕ}
  → odd m → odd n
  → even(m + n)
  
e+o≡o zero on = on
e+o≡o (suc em) on = suc (o+o≡e em on)

o+o≡e (suc em) on = suc (e+o≡o em on)
