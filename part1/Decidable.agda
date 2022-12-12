module  plfa.part1.Decidable  where
import  Relation.Binary.PropositionalEquality  as  Eq 
open  Eq  using (_≡_; refl; cong; cong-app ; sym)
open  Eq.≡-Reasoning 
open  import  Data.Nat  using  ( ℕ ;  zero ;  suc ) 
open  import  Data.Product  using  ( _×_ )  renaming  ( _,_  to  ⟨_,_⟩ ) 
open  import  Data.Sum  using  ( _⊎_ ;  inj₁ ;  inj₂ )
open  import  Relation.Nullary  using  ( ¬_ ) 
open  import  Relation.Nullary.Negation  using  () 
  renaming  ( contradiction  to  ¬¬-intro ) 
open  import  Data.Unit  using  ( ⊤ ;  tt ) 
open  import  Data.Empty  using  ( ⊥ ;  ⊥-elim ) 
open  import  plfa.part1.Relations  using  ( _<_ ;  z<s ;  s<s ) 
open import  plfa.part1.Isomorphism  using  ( _⇔_ )

infix  4  _≤_

data _≤_  :  ℕ  →  ℕ  →  Set  where

  z≤n  :  ∀  { n  :  ℕ } 
      -------- 
    →  zero  ≤  n

  s≤s  :  ∀  { m  n  :  ℕ } 
    →  m  ≤  n 
      ------------- 
    →  suc  m  ≤  suc  n

2≤4  :  2  ≤  4 
2≤4  =  s≤s  ( s≤s  z≤n )

¬4≤2  :  ¬  ( 4  ≤  2 ) 
¬4≤2  ( s≤s  ( s≤s  ()))

data Bool  :  Set  where
  true   :  Bool
  false  :  Bool

infix  4  _≤ᵇ_

_≤ᵇ_  :  ℕ  →  ℕ  →  Bool 
zero  ≤ᵇ  n        =   true 
suc  m  ≤ᵇ  zero    =   false 
suc  m  ≤ᵇ  suc  n   =   m  ≤ᵇ  n

_  :  ( 2  ≤ᵇ  4 )  ≡  true 
_  = 
  begin 
    2  ≤ᵇ  4 
  ≡⟨⟩ 
    1  ≤ᵇ  3 
  ≡⟨⟩ 
    0  ≤ᵇ  2 
  ≡⟨⟩ 
    true 
  ∎

_  :  ( 4  ≤ᵇ  2 )  ≡  false 
_  = 
  begin 
    4  ≤ᵇ  2 
  ≡⟨⟩ 
    3  ≤ᵇ  1 
  ≡⟨⟩ 
    2  ≤ᵇ  0 
  ≡⟨⟩ 
    false 
  ∎

T  :  Bool  →  Set 
T  true    =   ⊤ 
T  false   =   ⊥

≡→T  :  ∀  { b  :  Bool }  →  b  ≡  true  →  T  b 
≡→T  refl   =   tt

≤ᵇ→≤  :  ∀  ( m  n  :  ℕ )  →  T  ( m  ≤ᵇ  n )  →  m  ≤  n 
≤ᵇ→≤  zero     n        tt   =   z≤n 
≤ᵇ→≤  ( suc  m )  zero     () 
≤ᵇ→≤  ( suc  m )  ( suc  n )  t    =   s≤s  ( ≤ᵇ→≤  m  n  t )

≤→≤ᵇ  :  ∀  { m  n  :  ℕ }  →  m  ≤  n  →  T  ( m  ≤ᵇ  n ) 
≤→≤ᵇ  z≤n         =   tt 
≤→≤ᵇ  ( s≤s  m≤n )   =   ≤→≤ᵇ  m≤n

data Dec  ( A  :  Set )  :  Set  where
  yes  :    A  →  Dec  A
  no   :  ¬  A  →  Dec  A

¬s≤z  :  ∀  { m  :  ℕ }  →  ¬  ( suc  m  ≤  zero ) 
¬s≤z  ()

¬s≤s  :  ∀  { m  n  :  ℕ }  →  ¬  ( m  ≤  n )  →  ¬  ( suc  m  ≤  suc  n ) 
¬s≤s  ¬m≤n  ( s≤s  m≤n )  =  ¬m≤n  m≤n

_≤?_  :  ∀  ( m  n  :  ℕ )  →  Dec  ( m  ≤  n ) 
zero    ≤?  n                    =   yes  z≤n 
suc  m  ≤?  zero                 =   no  ¬s≤z 
suc  m  ≤?  suc  n  with  m  ≤?  n 
...                |  yes  m≤n   =   yes  ( s≤s  m≤n ) 
...                |  no  ¬m≤n   =   no  ( ¬s≤s  ¬m≤n)

_  :  2  ≤?  4  ≡  yes  ( s≤s  ( s≤s  z≤n )) 
_  =  refl

_  :  4  ≤?  2  ≡  no  ( ¬s≤s  ( ¬s≤s  ¬s≤z )) 
_  =  refl


¬s<z  :  ∀  { n  :  ℕ }  →  ¬  ( n  <  zero ) 
¬s<z ()

¬s<s  :  ∀  { m  n  :  ℕ }  →  ¬  ( m  <  n )  →  ¬  ( suc  m < suc  n ) 
¬s<s  ¬m<n  ( s<s  m<n )  =  ¬m<n  m<n

_<?_  :  ∀  ( m  n  :  ℕ )  →  Dec  ( m  <  n )
zero <? (suc n) = yes z<s
n <? zero = no ¬s<z
(suc m) <? (suc n) with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

¬s≡s : ∀  { m  n  :  ℕ }  →  ¬  ( m  ≡  n )  →  ¬  ( suc m ≡ suc n ) 
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_  :  ∀  ( m  n  :  ℕ )  →  Dec  ( m  ≡  n )
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...             | yes m≡n = yes (cong suc m≡n)
...             | no  ¬m≡n = no (¬s≡s ¬m≡n)

_≤?′_  :  ∀  ( m  n  :  ℕ )  →  Dec  ( m  ≤  n ) 
m  ≤?′  n  with  m  ≤ᵇ  n  |  ≤ᵇ→≤  m  n  |  ≤→≤ᵇ  { m }  { n } 
...         |  true    |  p         |  _             =  yes  ( p  tt ) 
...         |  false   |  _         |  ¬p            =  no  ¬p

⌊_⌋  :  ∀  { A  :  Set }  →  Dec  A  →  Bool 
⌊  yes  x  ⌋   =   true 
⌊  no  ¬x  ⌋   =   false

_≤ᵇ′_  :  ℕ  →  ℕ  →  Bool 
m  ≤ᵇ′  n   =   ⌊  m  ≤?  n  ⌋

toWitness  :  ∀  { A  :  Set }  { D  :  Dec  A }  →  T  ⌊  D  ⌋  →  A 
toWitness  { A }  { yes  x }  tt   =   x 
toWitness  { A }  { no  ¬x }  ()

fromWitness  :  ∀  { A  :  Set }  { D  :  Dec  A }  →  A  →  T  ⌊  D  ⌋ 
fromWitness  { A }  { yes  a }  a′ = tt
fromWitness  { A }  { no  ¬a }  a  = ¬a a

≤ᵇ′→≤  :  ∀  { m  n  :  ℕ }  →  T  ( m  ≤ᵇ′  n )  →  m  ≤  n 
≤ᵇ′→≤   =   toWitness

≤→≤ᵇ′  :  ∀  { m  n  :  ℕ }  →  m  ≤  n  →  T  ( m  ≤ᵇ′  n ) 
≤→≤ᵇ′   =   fromWitness

infixr  6  _∧_

_∧_  :  Bool  →  Bool  →  Bool 
true   ∧  true   =  true 
false  ∧  _      =  false 
_ ∧ false = false 


infixr  6  _×-dec_

_×-dec_  :  ∀  { A  B  :  Set }  →  Dec  A  →  Dec  B  →  Dec  ( A  ×  B ) 
(yes  x)  ×-dec  (yes  y)  =  yes  ⟨  x  ,  y  ⟩ 
(no  ¬x)  ×-dec  _         =  no   λ{ ⟨  x  ,  y  ⟩  →  ¬x  x  } 
_         ×-dec  (no ¬y)   =  no   λ{ ⟨  x  ,  y  ⟩  →  ¬y  y  }
-- λ{ ⟨  x  ,  y  ⟩  →  ¬x  x  }  ==> 若 ⟨ x , y ⟩ 成立，則為真。但 ¬x x 引出矛盾，所以 ⟨ x , y ⟩ → ⊥

infixr  5  _∨_
_∨_  :  Bool  →  Bool  →  Bool 
true  ∨  _    = true 
_     ∨  true = true 
false ∨ false = false

infixr  5  _⊎-dec_
_⊎-dec_  :  ∀  { A  B  :  Set }  →  Dec  A  →  Dec  B  →  Dec  ( A  ⊎  B ) 
(yes x)  ⊎-dec  _       =  yes  ( inj₁ x ) 
_        ⊎-dec  (yes y) =  yes  ( inj₂ y ) 
(no ¬x)  ⊎-dec  (no ¬y) =  no λ { 
                                    ( inj₁ x ) → ¬x x ;
                                    ( inj₂ y ) → ¬y y  
                                }

not  :  Bool  →  Bool 
not  true   =  false 
not  false  =  true

¬?  :  ∀  { A  :  Set }  →  Dec  A  →  Dec  ( ¬  A ) 
¬?  ( yes  x ) = no  ( ¬¬-intro  x ) -- 要給出 ¬x 為假的證明 => 給出 ¬¬x 的證明
¬?  ( no  ¬x ) = yes  ¬x

_⊃_  :  Bool  →  Bool  →  Bool 
_      ⊃  true  =  true 
false  ⊃  _     =  true
true   ⊃  false =  false
-- 若P則Q

_→-dec_  :  ∀  { A  B  :  Set }  →  Dec  A  →  Dec  B  →  Dec  ( A  →  B ) 
_       →-dec  (yes  y)   =   yes (λ _  →   y ) 
(no ¬x) →-dec  _          =   yes (λ x  →  ⊥-elim ( ¬x x ))
(yes x) →-dec  (no ¬y)    =   no  (λ f  →  ¬y  ( f  x ))


∧-×  :  ∀  { A  B  :  Set }  ( x  :  Dec  A )  ( y  :  Dec  B )  →  ⌊  x  ⌋  ∧  ⌊  y  ⌋  ≡  ⌊  x  ×-dec  y  ⌋
∧-× (yes x) (yes x₁) = refl
∧-× (yes x) (no x₁) = refl
∧-× (no x) y = refl

∨-⊎  :  ∀  { A  B  :  Set }  ( x  :  Dec  A )  ( y  :  Dec  B )  →  ⌊  x  ⌋  ∨  ⌊  y  ⌋  ≡  ⌊  x  ⊎-dec  y  ⌋
∨-⊎ (yes x) y = refl
∨-⊎ (no x) (yes x₁) = refl
∨-⊎ (no x) (no x₁) = refl

not-¬  :  ∀  { A  :  Set }  ( x  :  Dec  A )  →  not  ⌊  x  ⌋  ≡  ⌊  ¬?  x  ⌋
not-¬ (yes x) = refl
not-¬ (no x) = refl

_iff_  :  Bool  →  Bool  →  Bool
true   iff  true  =  true
true   iff  false  =  false
false  iff  true  =  false
false  iff  false  =  true

open _⇔_

_⇔-dec_  :  ∀  { A  B  :  Set }  →  Dec  A  →  Dec  B  →  Dec  ( A  ⇔  B )
(yes x)  ⇔-dec  (yes y)  =   yes (record { to = λ x → y ; from = λ y → x })
(yes x)  ⇔-dec  (no  ny) =   no  (λ z → ny (to z x))
(no  nx) ⇔-dec  (yes y)  =   no  (λ z → nx (from z y))
(no  nx) ⇔-dec  (no  ny) =   yes (record {
    to = λ {
      x → {!   !}
    };
    from = λ {
      y → {!   !}
    }
  })


--  (λ z → nx {! (to z nx)  !})

iff-⇔  :  ∀  { A  B  :  Set }  ( x  :  Dec  A )  ( y  :  Dec  B )  →  ⌊  x  ⌋  iff  ⌊  y  ⌋  ≡  ⌊  x  ⇔-dec  y  ⌋
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (yes x) (no y)  = refl
iff-⇔ (no x)  (yes y) = refl
iff-⇔ (no x)  (no y)  = refl

minus  :  ( m  n  :  ℕ )  ( n≤m  :  n  ≤  m )  →  ℕ 
minus   m           zero        _            =  m 
minus  ( suc  m )  ( suc  n )  ( s≤s  n≤m )  =  minus  m  n  n≤m

_  :  minus  5  3  ( s≤s  ( s≤s  ( s≤s  z≤n )))  ≡  2 
_  =  refl

_-_  :  ( m  n  :  ℕ )  { n≤m  :  T  ⌊  n  ≤?  m  ⌋ }  →  ℕ 
_-_  m  n  { n≤m }  =  minus  m  n  ( toWitness  n≤m ) 

_  :  5  -  3  ≡  2 
_  =  refl

True  :  ∀  { Q }  →  Dec  Q  →  Set 
True  Q  =  T  ⌊  Q  ⌋

-- 給出True，toWitness和 fromWitness 的相反定義。分別稱為False，toWitnessFalse和fromWitnessFalse。
False : ∀ { Q } → Dec Q → Set
False DecQ = T ⌊ ¬? DecQ ⌋

toWitnessFalse  :  ∀  { A  :  Set } { D  :  Dec A }  →  T  ⌊ ¬? D  ⌋  →  ¬ A 
toWitnessFalse {A} {no x} tt = x

fromWitnessFalse  :  ∀  { A  :  Set }  { D  :  Dec  A }  →  ¬ A  →  T  ⌊  ¬? D  ⌋ 
fromWitnessFalse {A} {yes a} na = na a
fromWitnessFalse {A} {no a} a′ = tt


