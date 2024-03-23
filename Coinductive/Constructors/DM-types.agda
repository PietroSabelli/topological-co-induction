
{-# OPTIONS --without-K --exact-split #-}

open import Agda.Builtin.Equality
open import operators

module Coinductive.Constructors.DM-types
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) (i : I a) → Br a i → A)
  where

  -- proof-irrelevant dependent M-types
  -- as largest fixed points of the
  -- polynomial endofunctors Der Br ar
  postulate
    DM         : A → Set
    DM-correct : DM ⇒ Der' Br ar DM
    DM-largest : ∀ {P : A → Set} → P ⇒ Der' Br ar P → P ⇒ DM