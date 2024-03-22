
{-# OPTIONS --without-K --exact-split #-}

open import Agda.Builtin.Equality
open import operators

module Coinductive.Constructors.⋊-types
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  (V : A → Set)
  where

  postulate
    ⋊         : A → Set
    ⋊-correct : ⋊ ⇒ Conf⋊ C V ⋊
    ⋊-largest : ∀ {P : A → Set} → P ⇒ Conf⋊ C V P → P ⇒ ⋊