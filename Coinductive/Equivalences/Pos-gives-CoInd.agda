
{-# OPTIONS --exact-split --without-K #-}

open import Relation.Binary.PropositionalEquality.Core
open import Data.Unit
open import Data.Product
open import Data.Product.Properties

open import operators

module Coinductive.Equivalences.Pos-gives-CoInd
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where

  V : A → Set
  V = λ _ → ⊤

  open import Coinductive.Constructors.⋊-types C V

  CoInd = ⋊
  
  CoInd-correct : CoInd ⇒ Conf C CoInd
  CoInd-correct p = proj₂ (⋊-correct p)
  
  CoInd-largest : ∀ {P : A → Set} → P ⇒ Conf C P → P ⇒ CoInd
  CoInd-largest P-correct p = ⋊-largest (λ q → tt , P-correct q) p