
{-# OPTIONS --without-K --exact-split #-}

open import Data.Product

module Coinductive.Equivalences.Coind-gives-⋊
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

  open import Coinductive.Constructors.Coind-types A' I' C'

  ⋊ : A → Set
  ⋊ a = Σ (V a) λ p → CoInd (a , p)

  corf : (a : A) (p : ⋊ a) → V a
  corf a (v , _) = v

  cotr : (a : A) (i : I a) (p : ⋊ a) → Σ A λ b → C a i b × ⋊ b
  cotr a i (v , p) with El (a , v) i p
  ... | (b , u) , c , q = b , c , u , q
  
  ⋊coind :
    ∀ {P : A → Set}
    → (q₁ : ∀ a → P a → V a)
    → (q₂ : ∀ a i → (p : P a) → Σ A λ b → C a i b × P b)
    → (a : A) → P a → ⋊ a
  ⋊coind {P} q₁ q₂ a p = (q₁ a p) , (coind c' _ p)
    where
    P' : A' → Set
    P' (a , _) = P a

    c' : ∀ a i → (p : P' a) → Σ A' λ b → C' a i b × P' b
    c' (a , v) i p with q₂ a i p
    ... | b , c , q = (b , q₁ b q) , c , q
