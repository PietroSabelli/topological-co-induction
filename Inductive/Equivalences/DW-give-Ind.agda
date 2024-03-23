
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Data.Product
open import Inductive.Constructors.DW-types

module Inductive.Equivalences.DW-give-Ind
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

Br : (a : A) → I a → Set
Br a i = Σ A (C a i)

ar : (a : A) (i : I a) → Br a i → A
ar a i = proj₁

Ind : A → Set
Ind = DW Br ar

ind : (a : A) (i : I a) → ((b : A) → C a i b → Ind b) → Ind a
ind a i f = dsup a i λ b → f (ar a i b) (proj₂ b)

El-Ind :  ∀ {e} (M : (a : A) → Ind a → Set e)
          (c : (a : A)
              (i : I a)
              (f : (j : A) → C a i j → Ind j)
              (h : (j : A) (r : C a i j) → M j (f j r))
              → M a (ind a i f))
          → (a : A) (w : Ind a) → M a w

El-Ind M c a (dsup a i f) =
  c a i (λ j z → f (j , z)) λ j r → El-Ind M c j (f (j , r))

C-Ind : ∀ {e} (M : (a : A) → Ind a → Set e)
        (c : (a : A)
              (i : I a)
              (f : (j : A) → C a i j → Ind j)
              (h : (j : A) (r : C a i j) → M j (f j r))
              → M a (ind a i f))
        → (a : A) (i : I a) (f : (b : A) → C a i b → Ind b)
        → El-Ind M c a (ind a i f) ≡ c a i f λ j r → El-Ind M c j (f j r)

C-Ind M c a i f = refl