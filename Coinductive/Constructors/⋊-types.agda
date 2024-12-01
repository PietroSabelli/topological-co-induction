{-# OPTIONS --without-K --exact-split #-}

open import Data.Product

module Coinductive.Constructors.⋊-types
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  (V : A → Set)
  where

  postulate
    ⋊ : A → Set
    corf : (a : A) (p : ⋊ a) → V a
    cotr : (a : A) (i : I a) (p : ⋊ a) → Σ A λ b → C a i b × ⋊ b
    ⋊coind :
      ∀ {P : A → Set}
      → (q₁ : ∀ a → P a → V a)
      → (q₂ : ∀ a i → (p : P a) → Σ A λ b → C a i b × P b)
      → (a : A) → P a → ⋊ a