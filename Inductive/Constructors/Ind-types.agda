
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Inductive.Constructors.Ind-types
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where
  
data Ind : A → Set where
  ind : (a : A)
        (i : I a)
        (f : (b : A) → C a i b → Ind b)
        → Ind a

El-Ind :  ∀ {e} (M : (a : A) → Ind a → Set e)
          (c : (a : A)
              (i : I a)
              (f : (j : A) → C a i j → Ind j)
              (h : (j : A) (r : C a i j) → M j (f j r))
              → M a (ind a i f))
          → (a : A) (w : Ind a) → M a w

El-Ind M c a (ind a i f) = c a i f λ j r → El-Ind M c j (f j r)

C-Ind : ∀ {e} (M : (a : A) → Ind a → Set e)
        (c : (a : A)
              (i : I a)
              (f : (j : A) → C a i j → Ind j)
              (h : (j : A) (r : C a i j) → M j (f j r))
              → M a (ind a i f))
        → (a : A) (i : I a) (f : (b : A) → C a i b → Ind b)
        → El-Ind M c a (ind a i f) ≡ c a i f λ j r → El-Ind M c j (f j r)

C-Ind M c a i f = refl