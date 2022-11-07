module plfa.part1.Bins where
{- OPTIONS --exact-split -}

open  import  Data.Nat  using  ( ℕ ; zero ; suc ; _+_ ; _*_ ) 
open  import  Data.Nat.Properties  using  ( +-comm ; *-comm)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import plfa.part1.Relations using (_<_ ; _≤_)

-----------------------------------
-- Naturals

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

to   : ℕ → Bin
to zero = ⟨⟩
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = from m * 2
from (m I) = from m * 2 + 1

-------------------------------
-- Induction

bin-low₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-low₁ ⟨⟩ = refl
bin-low₁ (b O) rewrite +-comm (from b * 2) 1 = refl
bin-low₁ (b I) rewrite bin-low₁ b | +-comm (from b * 2) 1 = refl

{-
bin-low₂ : ∀ (b : Bin) → to (from b) ≡ b
bin-low₂ 反例: b ≡ ⟨⟩ O → to (from (⟨⟩ O)) = to 0 = ⟨⟩ ̸= b
-}

bin-low₃₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-low₃₁ ⟨⟩ = refl
bin-low₃₁ (b O) rewrite +-comm (from b * 2) 1 = refl
bin-low₃₁ (b I) rewrite bin-low₃₁ b | +-comm (from b * 2) 1 = refl

bin-low₃ : ∀ (n : ℕ) → from (to n) ≡ n
bin-low₃ zero = refl
bin-low₃ (suc n) rewrite bin-low₃₁ (to n) | bin-low₃ n = refl

--------------------------------
-- Relations


data Can : Bin → Set
data 0ne : Bin → Set

data 0ne where
  ⟨⟩I : 0ne (⟨⟩ I)
  apd₀ : ∀{b : Bin}
    → 0ne b → 0ne (b O)

  apd₁ : ∀{b : Bin}
    → 0ne b → 0ne (b I)

data Can where
  ⟨⟩None : Can ⟨⟩
  1ne : ∀ {b : Bin} → 0ne b → Can b

0ne-inc : ∀ {b : Bin}
  → 0ne b → 0ne (inc b)
0ne-inc {b O} (apd₀ 0neb) = apd₁ 0neb
0ne-inc {⟨⟩ I} ⟨⟩I = apd₀ ⟨⟩I
0ne-inc {b I} (apd₁ 0neb) = apd₀ (0ne-inc 0neb)

0ne-can-inc : ∀ {b : Bin}
  → 0ne b → Can (inc b)
0ne-can-inc {b O} (apd₀ 0neb) = 1ne (apd₁ 0neb)
0ne-can-inc {⟨⟩ I} ⟨⟩I = 1ne (apd₀ ⟨⟩I)
0ne-can-inc {b I} (apd₁ 0neb) = 1ne (apd₀ (0ne-inc 0neb))

can-inc : ∀ {b : Bin}
  → Can b → Can (inc b)

can-inc {⟨⟩} ⟨⟩None = 1ne ⟨⟩I
can-inc (1ne x) = 1ne (0ne-inc x)

can-to_n : ∀ {n : ℕ}
  → Can (to n)

can-to_n {zero} = ⟨⟩None
can-to_n {suc n} = can-inc {to n} (can-to_n {n})

open _≤_

1<n*2 : ∀ {n : ℕ}
  → 1 ≤ n → 1 ≤ n * 2
1<n*2 {suc n} 1≤n = s≤s z≤n

0ne>0 : ∀ {b : Bin}
  → 0ne b → 1 ≤ from b
0ne>0 {⟨⟩ I} ⟨⟩I = s≤s z≤n

0ne>0 {b O} (apd₀ 0neb) = 1<n*2 {from b} (0ne>0 0neb)
0ne>0 {b I} (apd₁ 0neb) rewrite +-comm (from b * 2) 1 = s≤s z≤n

*-to : ∀ {n : ℕ}
  → 1 ≤ n → to (n * 2) ≡ (to n) O
*-to {zero} ()
*-to {suc zero} z≤s = refl
*-to {suc (suc n)} (s≤s z≤s) = cong inc (cong inc (*-to {suc n} (s≤s z≤n) ))

0ne-to∘from_b : ∀ {b : Bin}
  → 0ne b → to (from b) ≡ b
0ne-to∘from_b {b O} (apd₀ 0neb) rewrite *-to {from b} (0ne>0 0neb)
                                | 0ne-to∘from_b 0neb = refl
0ne-to∘from_b {⟨⟩ I} ⟨⟩I = refl
0ne-to∘from_b {b I} (apd₁ 0neb) rewrite +-comm (from b * 2) 1 
                                | *-to {from b} (0ne>0 0neb)
                                | 0ne-to∘from_b 0neb = refl

can-to∘from_b : ∀ {b : Bin}
  → Can b → to (from b) ≡ b

can-to∘from_b {⟨⟩} canb = refl
can-to∘from_b {⟨⟩ O} (1ne (apd₀ ()))
-- can-to∘from_b {⟨⟩ O} (1ne x) = {!   !}
can-to∘from_b {b} (1ne x) = 0ne-to∘from_b x
-- 先在紙上證明，再改成code

--------------------------------
-- Isomorphism

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    ≲to      : A → B
    ≲from    : B → A
    ≲from∘to : ∀ (x : A) → ≲from (≲to x) ≡ x
open _≲_

Bin-embedding : ℕ ≲ Bin
Bin-embedding = 
  record
  {
    ≲to      = to;
    ≲from    = from;
    ≲from∘to = bin-low₃
  }
 