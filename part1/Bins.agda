module plfa.part1.Bins where
{- OPTIONS --exact-split -}

open  import  Data.Nat  using  ( ℕ ; zero ; suc ; _+_ ; _*_ ) 
open  import  Data.Nat.Properties  using  ( +-comm )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

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
    → 0ne (b O) → 0ne b

  apd₁ : ∀{b : Bin}
    → 0ne (b I) → 0ne (b)

data Can where
  ⟨⟩None : Can ⟨⟩
  1ne : ∀ {b : Bin} → 0ne b → Can b

can-inc : ∀ {b : Bin}
  → Can b → Can (inc b)

can-inc canb = {!   !}

can-to_n : ∀ {n : ℕ}
  → Can (to n)

can-to_n {zero} = ⟨⟩None
can-to_n {suc n} = can-inc {to n} (can-to_n {n})

can-to∘from_b : ∀ {b : Bin}
  → Can b → to (from b) ≡ b

can-to∘from_b {⟨⟩} canb = refl
can-to∘from_b {b O} canb = {!   !}  

can-to∘from_b {b I} canb = {!   !}

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
