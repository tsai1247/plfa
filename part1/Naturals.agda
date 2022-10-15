module plfa.part1.Naturals where
{- OPTIONS --exact-split -}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

seven : ℕ
seven = suc (suc ( suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

+-example : 3 + 4 ≡ 7
+-example =
    begin
        3 + 4
    ≡⟨⟩
        suc (2 + 4)
    ≡⟨⟩
        suc (suc (1 + 4))
    ≡⟨⟩
        suc (suc (suc (0 + 4)))
    ≡⟨⟩
        suc (suc (suc 4))
    ≡⟨⟩
        7
    ∎


_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

*-example : 3 * 4 ≡ 12
*-example = 
    begin
        3 * 4
    ≡⟨⟩
        4 + (2 * 4)
    ≡⟨⟩
        4 + (4 + (1 * 4))
    ≡⟨⟩
        4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩
        4 + (4 + (4 + 0))
    ≡⟨⟩
        12    
    ∎

  
_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n


_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
    begin
        5 ∸ 3
    ≡⟨⟩
        4 ∸ 2
    ≡⟨⟩
        3 ∸ 1
    ≡⟨⟩
        2 ∸ 0
    ≡⟨⟩
        2
    ∎


∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
    begin
        3 ∸ 5
    ≡⟨⟩
        2 ∸ 4
    ≡⟨⟩
        1 ∸ 3
    ≡⟨⟩
        0 ∸ 2
    ≡⟨⟩
        0
    ∎


infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl


to   : ℕ → Bin
to zero = ⟨⟩
to (suc m) = inc (to m)

_ : to 0 ≡ ⟨⟩
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = from m * 2
from (m I) = from m * 2 + 1
-- why is ⟨ from (m I) = from (m O) + 1 ⟩ wrong?

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl
