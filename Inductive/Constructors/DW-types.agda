
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Inductive.Constructors.DW-types
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) → (i : I a) → Br a i → A)
  where

data DW : A → Set where
  dsup : (a : A)
         (i : I a)
         (f : (b : Br a i) → DW (ar a i b))
         → DW a

El-DW : ∀ {e} → (M : (a : A) → DW a → Set e)
        (d : (a : A)
             (i : I a)
             (h : (b : Br a i) → DW (ar a i b))
             (k : (b : Br a i) → M (ar a i b) (h b))
             → M a (dsup a i h))
        → (a : A) (w : DW a)
        → M a w

El-DW M d a (dsup a i f) =
  d a i f λ b → El-DW M d (ar a i b) (f b)

C-DW : ∀ {e} → (M : (a : A) → DW a → Set e)
      (d : (a : A)
           (i : I a)
           (h : (b : Br a i) → DW (ar a i b))
           (k : (b : Br a i) → M (ar a i b) (h b))
           → M a (dsup a i h))
      → (a : A) (i : I a) (f : (b : Br a i) → DW (ar a i b))
      → El-DW M d a (dsup a i f)
        ≡
        d a i f (λ b → El-DW M d (ar a i b) (f b))

C-DW M d a i f = refl
