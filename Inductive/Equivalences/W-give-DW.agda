
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Data.Product
open import Inductive.Constructors.W-types

module Inductive.Equivalences.W-give-DW
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) → (i : I a) → Br a i → A)
  where

Free : Set
Free = W (Σ A I) (λ z → Br (proj₁ z) (proj₂ z))

Legal : Free → A → Set
Legal (sup (a , i) f) j = (∀ b → Legal (f b) (ar a i b)) × (a ≡ j)

DW : A → Set
DW a = Σ Free (λ w → Legal w a)

dsup : (a : A) (i : I a) (f : (b : Br a i) → DW (ar a i b)) → DW a

dsup a i f = sup (a , i) (λ b → proj₁ (f b)) ,
              (λ b → proj₂ (f b)) ,
              refl

El-DW : ∀ {e} → (M : (a : A) → DW a → Set e)
        (d : (a : A)
             (i : I a)
             (h : (b : Br a i) → DW (ar a i b))
             (k : (b : Br a i) → M (ar a i b) (h b))
             → M a (dsup a i h))
        → (a : A) (w : DW a)
        → M a w

El-DW M d a (sup (.a , i) f , l , refl) =
  d a i (λ b → f b , l b) (λ b → El-DW M d (ar a i b) (f b , l b))

C-DW : ∀ {e} → (C : (a : A) → DW a → Set e)
      (c : (a : A)
           (i : I a)
           (f : (b : Br a i) → DW (ar a i b))
           (p : (b : Br a i) → C (ar a i b) (f b))
           → C a (dsup a i f))
      → (a : A) (i : I a) (f : (b : Br a i) → DW (ar a i b))
      → El-DW C c a (dsup a i f)
        ≡
        c a i f (λ b → El-DW C c (ar a i b) (f b))

C-DW C c a i f = refl