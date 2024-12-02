
{-# OPTIONS --without-K --exact-split #-}

open import Data.Product

-- Endofunctors used to semantically define coinductive types
-- as in Section 4 of
-- "A topological reading of coinductive
--  predicates in Dependent Type Theory"

module Coinductive.Constructors.Endofunctors where

_⇒_ : ∀ {A : Set} → (A → Set) → (A → Set) → Set
_⇒_ {A} P Q = {a : A} → P a → Q a

module _
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

  Conf : (A → Set) → (A → Set)
  Conf P a = ∀ i → Σ A λ b → C a i b × P b

  Conf⇒ : ∀ {P Q} → P ⇒ Q → Conf P ⇒ Conf Q
  Conf⇒ p q i with q i
  ... | b , c , r = b , c , p r

module _
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) (i : I a) → Br a i → A)
  where

  Der : (A → Set) → (A → Set)
  Der P a = Σ (I a) λ i → ∀ b → P (ar a i b)

  Der⇒ : ∀ {P Q} → P ⇒ Q → Der P ⇒ Der Q
  Der⇒ p (i , f) = i , λ b → p (f b)