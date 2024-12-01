
{-# OPTIONS --exact-split --without-K #-}

open import Agda.Builtin.Equality
open import Data.Product

-- We show that each endofunctor of the form
-- Conf I C is isomorphic to one of the form
-- Der Br ar

module Coinductive.Equivalences.DM-gives-Coind
  (A : Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where

  open import Coinductive.Constructors.Endofunctors

  I' : A → Set
  I' a = (i : I a) → (Σ A λ b → C a i b)

  Br : (a : A) → I' a → Set
  Br a _ = I a

  ar : (a : A) (f : I' a) → Br a f → A
  ar a f i = proj₁ (f i)

  η : ∀ P → Der Br ar P ⇒ Conf C P
  η P (f , p) i with f i | p i
  ... | b , c | q = b , c , q

  η-naturality : ∀ {P Q : A → Set}
    → (f : P ⇒ Q) {a : A} (p : Der Br ar P a)
    → (Conf⇒ C {P} {Q} f) (η P p)
      ≡
      (η Q) (Der⇒ Br ar {P} {Q} f p)
  η-naturality f p = refl

  η⁻¹ : ∀ P → Conf C P ⇒ Der Br ar P
  η⁻¹ P p =
    (λ i → (proj₁ (p i)) , proj₁ (proj₂ (p i))) ,
    λ i → proj₂ (proj₂ (p i))
  
  η∘η⁻¹ : ∀ {P} {a} {w : Conf C P a} → η P (η⁻¹ P w) ≡ w
  η∘η⁻¹ = refl

  η⁻¹∘η : ∀ {P} {a} {w : Der Br ar P a} → η⁻¹ P (η P w) ≡ w
  η⁻¹∘η {P} {a} {w = f} = refl