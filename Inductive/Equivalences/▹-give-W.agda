
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Data.Empty
open import Data.Unit
open import Inductive.Constructors.▹-types

module Inductive.Equivalences.▹-give-W
  (A : Set) (B : A → Set)
  where

C : ⊤ → A → ⊤ → Set
C _ a _ = B a

V : ⊤ → Set
V _ = ⊥

W : Set
W = ▹ C V tt

sup : (a : A) (f : B a → W) → W
sup a f = tr tt a λ { tt b → f b }

El-W : ∀ {e} (M : W → Set e)
        (c : (a : A) (f : B a → W) (h : (b : B a) → M (f b)) → M (sup a f))
        → (w : W) → M w

El-W M c (tr .tt a f) = c a (λ b → f tt b) λ b → El-W M c (f tt b)

C-W : ∀ {e} (M : W → Set e)
        (c : (a : A) (f : B a → W) (h : (b : B a) → M (f b)) → M (sup a f))
        → (a : A) (f : B a → W)
        → El-W M c (sup a f) ≡ c a f λ b → El-W M c (f b)

C-W M c a f = refl