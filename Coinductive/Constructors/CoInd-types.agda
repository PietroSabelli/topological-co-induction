
{-# OPTIONS --without-K --exact-split #-}

open import Agda.Builtin.Equality
open import operators

module Coinductive.Constructors.CoInd-types
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

  postulate
    CoInd         : A → Set
    CoInd-correct : CoInd ⇒ Conf C CoInd
    CoInd-largest : ∀ {P : A → Set} → P ⇒ Conf C P → P ⇒ CoInd