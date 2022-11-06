module  plfa.part1.Connectives  where

import  Relation.Binary.PropositionalEquality  as  Eq 
open  Eq  using  ( _≡_ ;  refl ) 
open  Eq.≡-Reasoning 
open  import  Data.Nat  using  ( ℕ ) 
open  import  Function  using  ( _∘_) 
open  import  plfa.part1.Isomorphism  using  ( _≃_ ;  _≲_ ;  extensionality ; _⇔_) 
open  plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
    ⟨_,_⟩  : A → B → A × B

proj₁ : ∀{A B : Set}
    → A × B → A

proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀{A B : Set}
    → A × B → B
    
proj₂ ⟨ x , y ⟩ = y

η-× : ∀{A B : Set} (w : A × B ) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
{-
    ⟨A, B⟩ ≡ A × B
    proj₁ (A x B) = A
    proj₂ (A x B) = B
    A, B 與 A × B 都可以視為參數，
    proj₁, proj₂, ⟨⟩ 則是一個class name，加入參數後建構成目標物件
-}

infixr  2  _×_

record _×′_ (A B : Set) : Set where 
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B 
open _×′_
η-×′ : ∀{A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Bool  :  Set  where
  true   :  Bool
  false  :  Bool

data Qutrit  :  Set  where
  |0⟩  :  Qutrit
  |1⟩  :  Qutrit
  |2⟩  :  Qutrit

×-count  :  Bool  ×  Qutrit  →  ℕ 
×-count ⟨ true  , |0⟩ ⟩ = 1
×-count ⟨ true  , |1⟩ ⟩ = 2
×-count ⟨ true  , |2⟩ ⟩ = 3
×-count ⟨ false , |0⟩ ⟩ = 4
×-count ⟨ false , |1⟩ ⟩ = 5
×-count ⟨ false , |2⟩ ⟩ = 6

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm = 
  record 
  { 
    to      = λ{
      ⟨ x , y ⟩ → ⟨ y , x ⟩
    };
    from    = λ{
      ⟨ y , x ⟩ → ⟨ x , y ⟩
    };
    from∘to = λ{
      ⟨ x , y ⟩ → refl
    };
    to∘from = λ{
      ⟨ y , x ⟩ → refl
    } 
  }
-- 同構的交換律，同構的兩者之間有對射，但其中的元素不一定相同

×-assoc : ∀{A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = 
  record
  {
    to = λ{
      ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩
    };
    from = λ{
      ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩
    };
    from∘to = λ{
      ⟨ ⟨ x , y ⟩ , z ⟩ → refl
    };
    to∘from = λ{
      ⟨ x , ⟨ y , z ⟩ ⟩ → refl
    }
  }

{-
是否有方法填入 record, begin... (在 c-c c-space 中)
是否有方法消除 hole
-}

⇔≃× : ∀{A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = 
  record
  {
    to = λ{
      record
      {
        to = A→B;
        from = B→A
      } → ⟨ A→B , B→A ⟩ };
    
    from = λ{
      ⟨ A→B , B→A ⟩ → record
      {
        to = A→B;
        from = B→A
      }
    };
    
    from∘to = λ{
      record
      {
        to = A→B;
        from = B→A
      } → refl
    };

    to∘from = λ{
      ⟨ A→B , B→A ⟩ → refl
    }
  }

  -- 同構的時候，通常 to 跟 from 會完全對稱

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀(w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where 
  constructor tt′

η-⊤′ : ∀(w : ⊤′) → tt′ ≡ w
η-⊤′ tt′ = refl
-- c-c c-d

truth′ : ⊤′ 
truth′ = tt′
-- 可能知道 _ 的值嗎？
--  c-c c-n

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀{ A : Set} → ⊤ × A ≃ A
⊤-identityˡ = 
  record
  {
    to = λ {
      ⟨ tt , a ⟩ → a
    };
    from = λ {
      a → ⟨ tt , a ⟩
    };
    from∘to = λ {
      ⟨ tt , a ⟩ → refl
    };
    to∘from = λ {
      a → refl
    }
  }

⊤-identityʳ : ∀{A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    ( A × ⊤ )
  ≃⟨ ×-comm ⟩
    ( ⊤ × A )
  ≃⟨ ⊤-identityˡ ⟩
    A 
  ≃-∎

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀{A B C : Set} 
  → (A → C) → (B → C) → A ⊎ B 
  → C
  -- 只要 A 與 B 任一成立，就可以經過 (A → C) 或 (B → C) 推導出 C
case-⊎ A→C B→C (inj₁ x) = A→C x
case-⊎ A→C B→C (inj₂ x) = B→C x

η-⊎ : ∀{A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀{A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w -- case-⊎ (A→C) (B→C) (A⊎B) ≡ C
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Qutrit → ℕ
⊎-count (inj₁ true) = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ |0⟩) = 3
⊎-count (inj₂ |1⟩) = 4
⊎-count (inj₂ |2⟩) = 5

⊎-comm : ∀{A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = 
  record
  {
    to = λ{
      ( inj₁  x )  →  inj₂ x;
      ( inj₂  y )  →  inj₁ y
    };
    from = λ {
      (inj₁ y) → inj₂ y;
      (inj₂ x) → inj₁ x
    };
    from∘to = λ{
      (inj₁ x) → refl;
      (inj₂ y) → refl
    };
    to∘from = λ {
      (inj₁ y) → refl;
      (inj₂ x) → refl
    }
  }

⊎-assoc : ∀{A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = 
  record
  {
    to = λ {
      (inj₁ (inj₁ x)) → inj₁ x;
      (inj₁ (inj₂ y)) → inj₂ (inj₁ y);
      (inj₂ c) → inj₂ (inj₂ c)
    };
    from = λ {
      (inj₁ a) → inj₁ (inj₁ a);
      (inj₂ (inj₁ x)) → inj₁ (inj₂ x);
      (inj₂ (inj₂ y)) → inj₂ y
    };
    from∘to = λ {
      (inj₁ (inj₁ x)) → refl;
      (inj₁ (inj₂ y)) → refl;
      (inj₂ c) → refl
    };
    to∘from = λ {
      (inj₁ a) → refl;
      (inj₂ (inj₁ x)) → refl;
      (inj₂ (inj₂ y)) → refl
    }
  }
 
data ⊥  :  Set  where
  -- Nothing

⊥-elim : ∀{A : Set}
  → ⊥ → A
⊥-elim  ()

uniq-⊥ : ∀{C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀{A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ = 
  record
  {
    to = λ {
      (inj₂ x) → x
    };
    from = λ{
      x → inj₂ x
    };
    from∘to = λ {
      (inj₂ x) → refl
    };
    to∘from = λ {
      x → refl
    }
  }

⊥-identityʳ : ∀{A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

→-elim : ∀{A B : Set}
  → (A → B) → A → B 
→-elim L M = L M
-- modus ponens

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Qutrit) → ℕ
→-count f with f true | f false
...           |  |0⟩   |  |0⟩ = 1 
...           |  |0⟩   |  |1⟩ = 2 
...           |  |0⟩   |  |2⟩ = 3 
...           |  |1⟩   |  |0⟩ = 4 
...           |  |1⟩   |  |1⟩ = 5 
...           |  |1⟩   |  |2⟩ = 6 
...           |  |2⟩   |  |0⟩ = 7 
...           |  |2⟩   |  |1⟩ = 8 
...           |  |2⟩   |  |2⟩ = 9

currying : ∀{A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = 
  record
  {
    to = λ{
      f → λ {
        ⟨ x , y ⟩ → f x y 
      }
    };
    
    from = λ{
      g → λ {
        x → λ { 
          y → g ⟨ x , y ⟩
        }
      }
    };
    from∘to = λ {
      f → refl
    };
    
    to∘from = λ {
      g → extensionality  λ{  
        ⟨  x  ,  y  ⟩ → refl
      }
    }
  }

→-distrib-⊎ : ∀{ A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = 
  record 
  {
    to = λ{
      f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    };
    from = λ{ 
      ⟨ g , h ⟩ → λ{
        (inj₁ x) → g x;
        (inj₂ y) → h y
      }
    };
    from∘to =  λ{
      f → extensionality  λ {
        (inj₁ x) → refl;
        (inj₂ y) → refl
      }
    };
    to∘from =  λ{ 
      ⟨ g , h ⟩ → refl
    }
  }

→-distrib-× : ∀{A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
  { 
    to = λ{
      f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    }; 
    from = λ{
      ⟨ g , h ⟩ → λ{
        x → ⟨ g x , h x ⟩
      }
    }; 
    from∘to = λ{
      f → extensionality λ{ 
        x → η-× (f x)
      }
    }; 
    to∘from = λ{
      ⟨ g , h ⟩ → refl
    } 
  }

×-distrib-⊎ : ∀{A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = 
  record
  {
    to = λ {
      ⟨ (inj₁ a) , c ⟩ → inj₁ ⟨ a , c ⟩;
      ⟨ (inj₂ b) , c ⟩ → inj₂ ⟨ b , c ⟩
    };
    from = λ {
      (inj₁ ⟨ a , c ⟩ ) → ⟨ inj₁ a , c ⟩;
      (inj₂ ⟨ b , c ⟩ ) → ⟨ inj₂ b , c ⟩
    };
    from∘to = λ {
      ⟨ (inj₁ a) , c ⟩ → refl;
      ⟨ (inj₂ b) , c ⟩ → refl  
    };
    to∘from = λ {
      (inj₁ ⟨ a , c ⟩ ) → refl;
      (inj₂ ⟨ b , c ⟩ ) → refl
    }
  }

⊎-distrib-× : ∀{A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = 
  record
  {
    to = λ {
      (inj₁ ⟨ a , b ⟩ ) → ⟨ inj₁ a , inj₁ b ⟩;
      (inj₂ c ) → ⟨ inj₂ c , inj₂ c ⟩
    };
    from = λ {
      ⟨ inj₁ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩;
      ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c;
      ⟨ inj₂ c , _ ⟩ → inj₂ c
    };
    from∘to = λ {
      (inj₁ ⟨ a , b ⟩ ) → refl;
      (inj₂ c ) → refl
    }
  }

-- A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
-- A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)


⊎-weak-× : ∀{A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× (⟨ (inj₁ a) , c ⟩) = inj₁ a
⊎-weak-× (⟨ (inj₂ b) , c ⟩) = inj₂ ⟨ b , c ⟩

⊎×-implies-×⊎ : ∀{A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ ( inj₁ (⟨ a , b ⟩) ) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ ( inj₂ (⟨ c , d ⟩) ) = ⟨ inj₂ c , inj₂ d ⟩

