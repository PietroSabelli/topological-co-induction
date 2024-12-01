
{-# OPTIONS --without-K --exact-split #-}

open import Data.Unit
open import Data.Product

module Coinductive.Equivalences.⋊-gives-Coind
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where
  
  V : A → Set
  V = λ _ → ⊤

  open import Coinductive.Constructors.⋊-types A I C V

  CoInd : A → Set
  CoInd = ⋊

  El : (a : A) (i : I a) (p : CoInd a) → Σ A λ b → C a i b × CoInd b
  El = cotr

  coind :
    ∀ {P : A → Set}
    → (c : ∀ a i → P a → Σ A λ b → C a i b × P b)
    → (a : A) → P a → CoInd a
  coind = ⋊coind (λ _ _ → tt)