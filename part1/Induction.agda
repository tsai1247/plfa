module plfa.part1.Induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = 
    begin 
        (suc m) + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
    ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + (suc n)
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎

+-suc (suc m) n =
  begin
    (suc m) + (suc n)
  ≡⟨⟩
    suc (m + (suc n))
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc (m) + n)
  ∎
  
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎

+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎


+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = 
  begin
    (m + n) + (p + q)  
  ≡⟨⟩
    (m + n) + (p + q)

  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎
    
finite-+-assoc : ∀ (m n p : ℕ) →  (m + n) + p ≡ m + (n + p)
finite-+-assoc zero n p = refl

finite-+-assoc (suc m) n p =
  begin
    (suc m) + n + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc (m + n + p)
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (finite-+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl


+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-assoc′² : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′² zero n p = refl
+-assoc′² (suc m) n p rewrite +-assoc′ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p  
  rewrite +-comm′ m (n + p)
    rewrite +-assoc′ n p m      
      rewrite +-comm′ m p
 = refl

*-inverse : ∀ (n : ℕ) → n * zero ≡ 0
*-inverse zero = refl
*-inverse (suc n)
  rewrite *-inverse n
   = refl

*-identity : ∀ (n : ℕ) → 1 * n ≡ n
*-identity zero = refl
*-identity (suc n) rewrite *-inverse n | +-identityʳ n = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) 
  rewrite *-identityʳ n
    = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ 0 n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
    rewrite +-assoc′ p (m * p) (n * p)
      = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p 
  rewrite *-distrib-+ n (m * n) p
    rewrite *-assoc m n p
  = refl

*-suc : ∀ (m n : ℕ) → (m + 1) * n ≡ m * n + n
*-suc 0 n rewrite +-identityʳ n = refl
*-suc (suc m) n
  rewrite *-distrib-+ m 1 n
  rewrite +-assoc n (m * n) n | +-identityʳ n
  = refl


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-inverse n = refl
*-comm n zero rewrite *-inverse n = refl
*-comm (suc m) (suc n)
  rewrite *-distrib-+ m 1 (suc n)
  | *-comm m (suc n)
  | *-comm n (suc m)
  | *-comm n m
  | sym(+-assoc n m (m * n))
  | +-comm n m 
  | +-assoc m n (m * n)
  = refl

0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl 

^-suc : ∀ (m n : ℕ) → m ^ (n + 1) ≡ m ^ n * m
^-suc m zero rewrite *-identityʳ m | +-identityʳ m = refl
^-suc m (suc n) rewrite ^-suc m n | *-assoc m (m ^ n) m = refl

^-distribˡ-+-*  : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m n zero rewrite +-identityʳ n | *-identityʳ (m ^ n) = refl
^-distribˡ-+-* m n (suc p) 
  rewrite +-comm 1 p | sym(+-assoc n p 1)
  | ^-suc m (n + p)
  | ^-distribˡ-+-* m n p 
  | *-assoc (m ^ n) (m ^ p) m 
  | *-comm (m ^ p) m
  = refl

*-swap : ∀ (m n p : ℕ) → m * n * p ≡ m * p * n
*-swap m n p
  rewrite *-assoc m n p
  | *-assoc m p n
  | *-comm n p
  = refl

^-distribʳ-*    : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl

^-distribʳ-* m n (suc p) 
  rewrite ^-distribʳ-* m n p                -- m * n * ((m ^ p) * (n ^ p))  ≡ m * (m ^ p) * (n * (n ^ p))
  
  | *-swap m n ((m ^ p) * (n ^ p))          -- m * ((m ^ p) * (n ^ p)) * n  ≡ m * (m ^ p) * (n * (n ^ p))
  
  | sym(*-assoc m (m ^ p) (n ^ p))          -- m * (m ^ p) * (n ^ p) * n    ≡ m * (m ^ p) * (n * (n ^ p))
  
  | *-swap (m * (m ^ p)) (n ^ p) n
  
  | *-assoc (m * (m ^ p)) n (n ^ p)
  
  = refl

^-*-assoc       : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-inverse n = refl
^-*-assoc m n (suc p) 
  rewrite ^-*-assoc m n p 
  | *-comm n (suc p)
  | ^-distribˡ-+-* m n (p * n) 
  | *-comm n p
  = refl


import plfa.part1.Naturals
-- open plfa.part1.Naturals using (Bin; inc; to; from)
-- kk : Bin
-- kk = ?
