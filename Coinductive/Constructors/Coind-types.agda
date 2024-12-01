

{-# OPTIONS --without-K --exact-split #-}

open import Data.Product

module Coinductive.Constructors.Coind-types
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where

  postulate
    CoInd : A → Set
    El : (a : A) (i : I a) (p : CoInd a) → Σ A λ b → C a i b × CoInd b
    coind :
      ∀ {P : A → Set}
      → (c : ∀ a i → P a → Σ A λ b → C a i b × P b)
      → (a : A) → P a → CoInd a