module  plfa.part1.Negation  where
open  import  Relation.Binary.PropositionalEquality  using  ( _≡_ ;  refl ) 
open  import  Data.Nat  using  ( ℕ ;  zero ;  suc ) 
open  import  Data.Empty  using  ( ⊥ ;  ⊥-elim ) 
open  import  Data.Sum  using  ( _⊎_ ;  inj₁ ; inj₂) 
open  import  Data.Product  using  ( _×_ ;  proj₁ ; proj₂ ; _,_)
open  import plfa.part1.Relations2 using (_<_)
open  import plfa.part1.Isomorphism  using  ( _≃_ ;  extensionality )

open _<_


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀{A : Set}
  → ¬ A → A  → ⊥
¬-elim ¬x x = ¬x x
infix 3 ¬_

¬¬-intro : ∀{A : Set}
  → A → ¬ (¬ A)
¬¬-intro x = λ {
        ¬x → ¬x x
    }

¬¬-intro′ : ∀{A : Set}
  →  A → ¬ (¬ A)
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀{A : Set}
  → ¬ (¬ (¬ A)) → ¬ A
¬¬¬-elim ¬¬¬x = λ {
        x → ¬¬¬x ( ¬¬-intro x)
    }

-- ¬ (¬ A) → A

contraposition : ∀{A B : Set}
    → (A → B) → (¬ B  → ¬ A)
contraposition f ¬b a = ¬b (f a)
{- 
  嘗試證明最後一項的矛盾：
    1. 當A成立時，可以經由 ⊥ 推導出 ¬ A 
-}

_≠_ : ∀{A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

_ : 1 ≠ 2
_ = λ ()

peano : ∀{m : ℕ} → zero ≠ (suc m)
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′  :  id  ≡  id′
id≡id′ = extensionality λ ()

assimilation : ∀{A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality ( λ {
      x → ⊥-elim (¬x′ x)
  } )

<-irreflexive : ∀(n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

data Trichotomy (m n : ℕ) : Set where
  m<n :
    m < n → Trichotomy m n
  m=n :
    m ≡ n → Trichotomy m n
  m>n :
    n < m → Trichotomy m n

open Trichotomy

trichotomy₁ : ∀(m n : ℕ)
  → m < n → ¬ m ≡ n 
trichotomy₁ (suc m) .(suc _) (s<s _m<n) refl = <-irreflexive m _m<n
-- given m n m<n m≡n, use ¬ (m < m) to get ⊥

trichotomy₂ : ∀(m n : ℕ)
  → m < n → ¬ n < m
trichotomy₂ zero (suc n) _m<n ()
trichotomy₂ (suc m) (suc n) (s<s _m<n) (s<s _n<m) = trichotomy₂ m n _m<n _n<m

trichotomy₃ : ∀(m n : ℕ)
  → m ≡ n → ¬ m < n
trichotomy₃ (suc m) .(suc _) refl (s<s _m<n) = <-irreflexive m _m<n

trichotomy₄ : ∀(m n : ℕ)
  → m ≡ n → ¬ n < m
trichotomy₄ .(suc _) (suc n) refl (s<s _n<m) = <-irreflexive n _n<m

trichotomy₅ : ∀(m n : ℕ)
  → n < m → ¬ m < n
trichotomy₅ zero zero ()
trichotomy₅ zero (suc n) ()
trichotomy₅ (suc m) zero z<s ()
trichotomy₅ (suc m) (suc n) (s<s _n<m) (s<s _m<n) = trichotomy₅ m n _n<m _m<n

trichotomy₆ : ∀(m n : ℕ)
  → n < m → ¬ m ≡ n
trichotomy₆ (suc m) .(suc _) (s<s _n<m) refl = <-irreflexive m _n<m

⊎-dual-×-from : ∀ {A B : Set}
  →  (¬ A) × (¬ B) → ¬ (A ⊎ B)
⊎-dual-×-from (fst , snd) (inj₁ x) = fst x
⊎-dual-×-from (fst , snd) (inj₂ y) = snd y


⊎-dual-× : ∀ {A B : Set}
  → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = 
  record
  {
    to = λ {
      f → (λ { 
            a → f (inj₁ a)
          }), 
          (λ {
            b → f (inj₂ b)
          })
    };
    from = λ {
      (fst , snd) → λ {
        (inj₁ x) → fst x
      ; (inj₂ y) → snd y
      }
    };
    
    from∘to = λ {
      f → extensionality λ {
        (inj₁ x) → refl
      ; (inj₂ y) → refl
      }
    };
    to∘from = λ {
      (fst , snd) → refl
    }
  } 

×-dual-⊎ : ∀ {A B : Set}
  → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ na) = λ {
    a×b → na (proj₁ a×b)
  }
×-dual-⊎ (inj₂ nb) = λ {
    a×b → nb (proj₂ a×b)
  }
      

-- 應該不成立，要給出一個比同構更弱的關係將兩邊關聯起來

-- 海廷邏輯 (直覺)
postulate
  em  :  ∀  { A  :  Set }  →  A  ⊎  ¬  A
  
-- 希爾伯特邏輯 (經典)

em-irrefutable  :  ∀  { A  :  Set } 
  →  ¬  ¬  ( A  ⊎  ¬  A ) 

em-irrefutable k = k ((inj₂ λ{ x → k ((inj₁ x)) }))

Stable  :  Set  →  Set 
Stable  A  =  ¬  ¬  A  →  A

-- Classical Practice not complete

neg_stable : ∀(A : Set)
  → Stable (¬ A)
neg_stable A nnnA = ¬¬¬-elim nnnA

×-stable-simplify : ∀(A B : Set)
  → ¬ ¬ A → ¬ ¬ B → ¬ ¬ (A × B)
×-stable-simplify A B nna nnb na×b = nnb λ {
    b → nna λ {
      a → na×b (a , b)
    }
  }


×-stable : ∀{A B : Set}
  → Stable A → Stable B → Stable (A × B)
×-stable sa sb nna×b = ( sa (λ {
    na → nna×b λ {
      a×b → na (proj₁ a×b)
    }
  }),
  sb (λ {
    nb → nna×b λ {
      a×b → nb (proj₂ a×b)
    }
  }))

-- × == conjective  == 合取
-- ⊎ == disjunctive == 析取
   