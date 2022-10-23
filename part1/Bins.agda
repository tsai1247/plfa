module plfa.part1.Bins where
{- OPTIONS --exact-split -}

open  import  Data.Nat  using  ( ℕ ; zero ; suc ; _+_ ; _*_ ) 
open  import  Data.Nat.Properties  using  ( +-comm )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-----------------------------------
-- Naturals

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

postulate
  bin-identity : ⟨⟩ O ≡ ⟨⟩

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

bin-low₂₀ : ∀ (b : Bin) → from (b I) ≡ from (b O) + 1
bin-low₂₀ b = refl

bin-low₂₁ : ∀ (n : ℕ) → to (n * 2) ≡ (to n) O
bin-low₂₁ zero rewrite bin-identity = refl
bin-low₂₁ (suc n) rewrite bin-low₂₁ n = refl

bin-low₂₂ :  ∀ (n : ℕ) → to (n * 2 + 1) ≡ (to n) I
bin-low₂₂ n rewrite +-comm (n * 2) 1 | bin-low₂₁ n = refl

bin-low₂ : ∀ (b : Bin) → to (from b) ≡ b
bin-low₂ ⟨⟩ = refl
bin-low₂ (b O) rewrite bin-low₂₁ (from b) | bin-low₂ b = refl
bin-low₂ (b I) rewrite bin-low₂₂ (from b) | bin-low₂ b = refl


bin-low₃₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-low₃₁ ⟨⟩ = refl
bin-low₃₁ (b O) rewrite +-comm (from b * 2) 1 = refl
bin-low₃₁ (b I) rewrite bin-low₃₁ b | +-comm (from b * 2) 1 = refl

bin-low₃ : ∀ (n : ℕ) → from (to n) ≡ n
bin-low₃ zero = refl
bin-low₃ (suc n) rewrite bin-low₃₁ (to n) | bin-low₃ n = refl

--------------------------------
-- Relations

data 0ne : Bin → Set

data Can : Bin → Set
  
data 0ne where
  ⟨⟩I : 0ne (⟨⟩ I)
  apd₀ : ∀{b : Bin}
    → 0ne b → 0ne (b O)

  apd₁ : ∀{b : Bin}
    → 0ne b → 0ne (b I)

data Can where
  ⟨⟩O : Can (⟨⟩ O)
  1ne : ∀ {b : Bin} → 0ne b → Can b

can-inc : ∀ {b : Bin}
  → Can b → Can (inc b)

can-inc {⟨⟩} b = 1ne ⟨⟩I
can-inc {b₁ O} b = 1ne {!   !}
can-inc {b₁ I} b = {!   !}
