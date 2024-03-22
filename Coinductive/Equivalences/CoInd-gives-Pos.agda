
{-# OPTIONS --exact-split --without-K #-}

open import Relation.Binary.PropositionalEquality.Core
open import Data.Unit
open import Data.Product
open import Data.Product.Properties

open import operators

module Coinductive.Equivalences.CoInd-gives-Pos
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  (V : A → Set)
  where

  A' : Set
  A' = Σ A λ a → V a

  I' : A' → Set
  I' (a , p) = I a

  C' : (z : A') → I' z → A' → Set
  C' (a , _) i (b , _) = C a i b

  open import Coinductive.Constructors.CoInd-types C'

  ⋊ : A → Set
  ⋊ a = Σ (V a) λ p → CoInd (a , p)

  ⋊-correct : ⋊ ⇒ Conf⋊ C V ⋊
  ⋊-correct {a} (p , q) = p , help
    where
    help : (i : I a) → Σ A (λ b → C a i b × ⋊ b)
    help i with CoInd-correct q i
    ... | (b , p) , c , r = b , c , p , r

  ⋊-largest : ∀ P → P ⇒ Conf⋊ C V P → P ⇒ ⋊
  ⋊-largest P f {a} p =
    v , CoInd-largest (λ { {a , v} → f' {a , v} }) p
    where
    v : V a
    v = proj₁ (f {a} p)

    P' : A' → Set
    P' (a , v) = P a

    f' : P' ⇒ Conf C' P'
    f' p i with f p
    ... | v , g with g i
    ... | b , c , r = (b , proj₁ (f r)) , c , r