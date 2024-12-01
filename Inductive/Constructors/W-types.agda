
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Inductive.Constructors.W-types
  (A : Set) (B : A → Set)
  where

data W : Set where
  sup : (a : A) (f : B a → W) → W

El-W : ∀ {e} → (M : W → Set e)
         (d : (a : A)
             (f : B a → W)
             (h : (b : B a) → M (f b))
             → M (sup a f))
        → (w : W) → M w

El-W M d (sup a f) = d a f λ b → El-W M d (f b)

C-W : ∀ {e} → (M : W → Set e)
      (d : (a : A)
           (f : B a → W)
           (h : (b : B a) → M (f b))
           → M (sup a f))
      → (a : A) (f : B a → W)
      → El-W M d (sup a f) ≡ d a f λ b → El-W M d (f b)

C-W M d a f = refl