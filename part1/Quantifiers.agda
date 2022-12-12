module  plfa.part1.Quantifiers  where
import  Relation.Binary.PropositionalEquality  as  Eq 
open  Eq  using (_≡_; refl; cong; cong-app ; sym)
open  Eq.≡-Reasoning 
open  import  Data.Nat  using  ( ℕ ;  zero ;  suc ;  _+_ ;  _*_ ) 
open  import  Data.Nat.Properties  using  ( +-comm ; +-suc ; +-assoc ; *-comm ;  +-identityʳ )
open  import  Relation.Nullary  using  ( ¬_ ) 
open  import  Data.Product  using  ( _×_ ;  proj₁ ;  proj₂)  renaming  ( _,_  to  ⟨_,_⟩) 
open  import  Data.Sum  using  ( _⊎_ ;  inj₁ ;  inj₂ ) 
open  import  plfa.part1.Isomorphism  using  ( _≃_ ) 
open  import  Function  using  ( _∘_ )
open import  Data.Nat  using  ( _≤_ ;  z≤n ;  s≤s ) 
open import  Data.Nat.Properties  using  ( ≤-refl ;  ≤-trans ;  ≤-antisym ;  ≤-total ; ≤-reflexive ;
                                  +-monoʳ-≤ ;  +-monoˡ-≤ ;  +-mono-≤ )

∀-elim  :  ∀  { A  :  Set }  { B  :  A  →  Set } 
  →  ( L  :  ∀  ( x  :  A )  →  B  x ) 
  →  ( M  :  A ) 
    ----------------- 
  →  B  M 
∀-elim  L  M  =  L  M

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g
    
postulate
  extensionality₂ : ∀ {A : Set} {P : A → Set} {F G : ( ∀(a : A) → (P a) )} -- B a × C a
    → (∀(x : A) → F x ≡ G x) → F ≡ G

∀-distrib-×  :  ∀  { A  :  Set } { B C : A → Set }
  → (∀(a : A) → (B a) × (C a) ) ≃ (∀(x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  {
    to = λ {
        f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    };
    from = λ {
      ⟨ g , h ⟩ → λ {
        x → ⟨ g x , h x ⟩
      }
    };
    from∘to = λ{
      f → extensionality₂ λ {
        x → refl
      }

    };
    to∘from = λ {
      ⟨ g , h ⟩ → refl
    }
  }

⊎∀-implies-∀⊎  :  ∀  {A : Set} {B C : A → Set}
  → (∀(x : A) → B x) ⊎ (∀(x : A) → C x)
  →  ∀(x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ bx) a = inj₁ (bx a)
⊎∀-implies-∀⊎ (inj₂ cx) a = inj₂ (cx a)

-- 逆命題顯然不成立，因為不能保證所有的 x 都滿足B x或C x同一邊

data Tri  :  Set  where
  aa  :  Tri
  bb  :  Tri
  cc  :  Tri

∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× = record
  {
    to = λ {
      x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩
    };
    from = λ {
      ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ {
        aa → Baa;
        bb → Bbb;
        cc → Bcc
      }
    };
    to∘from = λ {
      ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl
    };
    from∘to = λ {
      x → extensionality₂ λ {
        aa → refl;
        bb → refl;
        cc → refl
      }
    }
    -- 已經知道所有element都滿足，但不知道怎麼寫
  }

data Σ  ( A  :  Set )  ( B  :  A  →  Set )  :  Set  where
  ⟨_,_⟩  :  ( x  :  A )  →  B  x  →  Σ  A  B

Σ-syntax  =  Σ 
infix  2  Σ-syntax 
syntax  Σ-syntax  A  (λ  x  →  B )  =  Σ[  x  ∈  A  ]  B

record Σ′  ( A  :  Set )  ( B  :  A  →  Set )  :  Set  where 
  field
    proj₁′  :  A
    proj₂′  :  B  proj₁′
    
open Σ′

∃  :  ∀  { A  :  Set }  ( B  :  A  →  Set )  →  Set 
∃  { A }  B  =  Σ  A  B

∃-syntax  =  ∃ 
syntax  ∃-syntax  (λ  x  →  B )  =  ∃[  x  ]  B

∃-elim  :  ∀  { A  :  Set }  { B  :  A  →  Set }  { C  :  Set } 
  →  (∀  x  →  B  x  →  C ) 
  →  ∃[  x  ]  B  x 
    --------------- 
  →  C 
∃-elim  f  ⟨  x  ,  y  ⟩  =  f  x  y

∀∃-currying  :  ∀  { A  :  Set }  { B  :  A  →  Set }  { C  :  Set } 
  →  (∀  x  →  B  x  →  C )  ≃  ( ∃[  x  ]  B  x  →  C ) 
∀∃-currying  = 
  record 
    {  to       =   λ{  f  →  λ{  ⟨  x  ,  y  ⟩  →  f  x  y }} 
    ;  from     =   λ{  g  →  λ{  x  →  λ{  y  →  g  ⟨  x  ,  y  ⟩  }}} 
    ;  from∘to  =   λ{  f  →  refl  } 
    ;  to∘from  =   λ{  g  →  extensionality  λ{  ⟨  x  ,  y  ⟩  →  refl  }} 
    }

∃-distrib-⊎  :  ∀  { A  :  Set }  { B  C  :  A  →  Set }  → 
    ∃[  x  ]  ( B  x  ⊎  C  x )  ≃  ( ∃[  x  ]  B  x )  ⊎  ( ∃[  x  ]  C  x )
∃-distrib-⊎ = record {
    to = λ {
      ⟨ a , inj₁ ba ⟩ → inj₁ ⟨ a , ba ⟩
    ; ⟨ a , inj₂ ca ⟩ → inj₂ ⟨ a , ca ⟩
    };
    from = λ {
      (inj₁ ⟨ a , ba ⟩) → ⟨ a , inj₁ ba ⟩
    ; (inj₂ ⟨ a , ca ⟩) → ⟨ a , inj₂ ca ⟩
    };
    from∘to = λ {
      ⟨ a , inj₁ ba ⟩ → refl
    ; ⟨ a , inj₂ ca ⟩ → refl
    };
    to∘from = λ {
      (inj₁ ⟨ a , ba ⟩) → refl
    ; (inj₂ ⟨ a , ca ⟩) → refl
    }
  }

∃×-implies-×∃ : ∀{A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ ⟨ x , ⟨ bx , cx ⟩ ⟩ = ⟨ ⟨ x , bx ⟩ , ⟨ x , cx ⟩ ⟩ 

-- 逆命題不成立，可以寫成
-- (∃[ x ] B x) × (∃[ y ] C y) → ∃[ x ] (B x × C x)
-- 其中 x 跟 y 不一定相等

∃-⊎ : ∀ {B : Tri → Set}
  → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ = record {
    to = λ {
      ⟨ aa , x₁ ⟩ → inj₁ x₁
    ; ⟨ bb , x₁ ⟩ → inj₂ (inj₁ x₁)
    ; ⟨ cc , x₁ ⟩ → inj₂ (inj₂ x₁)
    };
    from = λ {
      (inj₁ x) → ⟨ aa , x ⟩
    ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩
    ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩
    };
    from∘to = λ {
      ⟨ aa , x₁ ⟩ → refl
    ; ⟨ bb , x₁ ⟩ → refl
    ; ⟨ cc , x₁ ⟩ → refl
    };
    to∘from = λ {
      (inj₁ x) → refl
    ; (inj₂ (inj₁ x)) → refl
    ; (inj₂ (inj₂ y)) → refl
    }
  }

data even  :  ℕ  →  Set 
data odd   :  ℕ  →  Set

data  even  where

  even-zero  :  even  zero

  even-suc  :  ∀  { n  :  ℕ } 
    →  odd  n 
      ------------ 
    →  even  ( suc  n )

data  odd  where
  odd-suc  :  ∀  { n  :  ℕ } 
    →  even  n 
      ----------- 
    →  odd  ( suc  n )

even-∃  :  ∀  { n  :  ℕ }  →  even  n  →  ∃[  m  ]  (       m  *  2  ≡  n )
odd-∃   :  ∀  { n  :  ℕ }  →   odd  n  →  ∃[  m  ]  ( 1  +  m  *  2  ≡  n )

even-∃ even-zero = ⟨ zero , refl ⟩ 

even-∃ ( even-suc  o )  with  odd-∃  o 
...                     |  ⟨  m  ,  refl  ⟩   =   ⟨ suc m , refl ⟩

odd-∃  ( odd-suc  e )   with  even-∃  e 
...                     |  ⟨  m  ,  refl  ⟩   =   ⟨  m  ,  refl  ⟩

∃-even  :  ∀  { n  :  ℕ }  →  ∃[  m  ]  (     m  *  2  ≡  n )  →  even  n
∃-odd   :  ∀  { n  :  ℕ }  →  ∃[  m  ]  ( 1  +  m  *  2  ≡  n )  →   odd  n

∃-even  ⟨   zero  ,  refl  ⟩  =  even-zero 
∃-even  ⟨  suc m  ,  refl  ⟩  =  even-suc  (∃-odd ⟨ m , refl ⟩) 
∃-odd   ⟨      m  ,  refl  ⟩  =  odd-suc  (∃-even ⟨ m , refl ⟩)

+-suc-distrib : ∀ (m n : ℕ)
  → suc (m + n) ≡ m + suc n
+-suc-distrib zero n = refl
+-suc-distrib (suc m) n = cong suc (+-suc-distrib m n)

-- ∃-even₁ : ∀  { n  :  ℕ }  →  ∃[  m  ]  (     2 * m  ≡  n )      →  even  n
-- ∃-odd₁  : ∀  { n  :  ℕ }  →  ∃[  m  ]  ( 1  +  2  *  m  ≡  n )  →   odd  n

-- ∃-even₁ ⟨  zero , refl ⟩ = even-zero
-- ∃-even₁ ⟨ suc m , refl ⟩ = even-suc (∃-odd₁ ⟨ m , +-suc-distrib m (m + zero) ⟩) -- 無法填寫(Termination checking failed)
-- ∃-odd₁  ⟨     m , refl ⟩ = odd-suc (∃-even₁ ⟨ m , refl ⟩) 

∃-+-≤-to : ∀ {y z : ℕ}
  → (∃[ x ] ( x + y ≡ z )) → (y ≤ z)
∃-+-≤-to {zero} {z} ⟨ x , x₁ ⟩ = z≤n
∃-+-≤-to {suc y} {.(zero + suc y)} ⟨ zero , refl ⟩ = ≤-reflexive refl
∃-+-≤-to {suc y} {.(suc x + suc y)} ⟨ suc x , refl ⟩ rewrite +-suc x y = s≤s (∃-+-≤-to {y} {suc x + y} ⟨ suc x , refl ⟩)

∃-+-≤-from-helper : ∀ {y z : ℕ}
  → (∃[ x ] ( x + y ≡ z )) → (∃[ x ] ( x + (suc y) ≡ (suc z) )) 
∃-+-≤-from-helper {y} {z} ⟨ x , refl ⟩ = ⟨ x , +-suc x y ⟩

∃-+-≤-from : ∀ {y z : ℕ}
  → (y ≤ z) → (∃[ x ] ( x + y ≡ z )) 
∃-+-≤-from {y} {z} z≤n = ⟨ z , +-identityʳ z ⟩
∃-+-≤-from {suc y} {suc z} (s≤s zz) = ∃-+-≤-from-helper (∃-+-≤-from zz) 

∃-+-≤ : ∀ {x y z : ℕ}
  → (∃[ x ] ( x + y ≡ z )) ≃ (y ≤ z)

∃-+-≤ {x} {y} {z} = record {
    to = ∃-+-≤-to;
    from = ∃-+-≤-from;
    from∘to = λ {
      ⟨ x , refl ⟩ → {!   !}
    };
    to∘from = λ {
      y≤z → {!   !}
    }
  }

¬∃≃∀¬  :  ∀  { A  :  Set }  { B  :  A  →  Set } 
  →  ( ¬  ∃[  x  ]  B  x )  ≃  ∀  x  →  ¬  B  x 
¬∃≃∀¬  = 
  record 
    {  to       =   λ{  ¬∃xy  x  y  →  ¬∃xy  ⟨  x  ,  y  ⟩  } 
    ;  from     =   λ{  ∀¬xy  ⟨  x  ,  y  ⟩ →  ∀¬xy  x  y  } 
    ;  from∘to  =   λ{  ¬∃xy  →  extensionality  λ{  ⟨  x  ,  y  ⟩  →  refl  }  } 
    ;  to∘from  =   λ{  ∀¬xy  →  refl  } 
    }

∃¬-implies-¬∀  :  ∀  { A  :  Set }  { B  :  A  →  Set } 
    →  ∃[  x  ]  ( ¬  B  x )  →  ¬  (∀  x  →  B  x )

∃¬-implies-¬∀ ⟨ x , ¬bx ⟩ ba = ¬bx (ba x)
-- (ba) x 可以得到 bx, 與 ¬bx 矛盾


-- ¬∀-implies-∃¬  :  ∀  { A  :  Set }  { B  :  A  →  Set } 
  -- →  ¬  (∀  x  →  B  x )  →  ∃[  x  ]  ( ¬  B  x ) 
-- 直覺邏輯認為，必須要確定是哪一個 x 使得(¬ B x)，而 ¬  (∀  x  →  B  x ) 的證據不足以讓我們得到確定的 x

open import plfa.part1.Bins using ( Bin ; 0ne ; Can )
open import plfa.part1.Bins using ( can-to_n ; inc ; can-to∘from_b ; bin-low₃ ) 
open import plfa.part1.Bins renaming (to to Binto ; from to Binfrom)
open Bin
open 0ne
open Can

≡0ne : ∀ {b : Bin} (o o′ : 0ne b) → o ≡ o′
≡0ne ⟨⟩I ⟨⟩I = refl
≡0ne (apd₀ o) (apd₀ o′) = cong apd₀ (≡0ne o o′)
≡0ne (apd₁ o) (apd₁ o′) = cong apd₁ (≡0ne o o′)

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can ⟨⟩None ⟨⟩None = refl
≡Can (1ne x) (1ne x₁) = cong 1ne (≡0ne x x₁)

{-
proj₁≡→Can≡ : {cb cb′ : ∃[ b ] (Can b)} → (proj₁ cb) ≡ (proj₁ cb′) → cb ≡ cb′
proj₁≡→Can≡ = ?
-}

N≃∃b : ∀(b : Bin)
  → ℕ ≃ ∃[ b ](Can b)

N≃∃b b = record
  {
    to = λ {
      x → ⟨ Binto x , can-to_n {x} ⟩
    };
    from = λ {
      ⟨ b , x ⟩ → Binfrom b
    };
    from∘to = λ {
      x → bin-low₃ x
    };
    to∘from = λ {
      ⟨ x , x₁ ⟩ → {!   !}
    }
    
  }