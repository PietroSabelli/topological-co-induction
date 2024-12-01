
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Inductive.Constructors.▹-types
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  (V : A → Set)
  where

data ▹ : A → Set where
  rf : (a : A) → V a → ▹ a
  tr : (a : A) (i : I a) → ((b : A) → C a i b → ▹ b) → ▹ a

El-▹ : ∀ {e} → (M : (a : A) → ▹ a → Set e)
      (q₁ : (a : A) (r : V a) → M a (rf a r))
      (q₂ : (a : A)
            (i : I a)
            (k : (b : A) → C a i b → ▹ b)
            (f : (b : A) → (p : C a i b) → M b ((k b) p))
            → M a (tr a i k))
      → (a : A) (m : ▹ a)
      → M a m

El-▹ M q₁ q₂ a (rf a r) = q₁ a r
El-▹ M q₁ q₂ a (tr a i k) = q₂ a i k (λ b p → El-▹ M q₁ q₂ b (k b p))

C₁-▹ : ∀ {e} → (M : (a : A) → ▹ a → Set e)
      (q₁ : (a : A) (r : V a) → M a (rf a r))
      (q₂ : (a : A)
            (i : I a)
            (k : (b : A) → C a i b → ▹ b)
            (f : (b : A) → (p : C a i b) → M b ((k b) p))
            → M a (tr a i k))
      → (a : A) (r : V a)
      → El-▹ M q₁ q₂ a (rf a r) ≡ q₁ a r

C₁-▹ M q₁ q₂ a r = refl

C₂-▹ : ∀ {e} → (M : (a : A) → ▹ a → Set e)
      (q₁ : (a : A) (r : V a) → M a (rf a r))
      (q₂ : (a : A)
            (i : I a)
            (k : (b : A) → C a i b → ▹ b)
            (f : (b : A) → (p : C a i b) → M b ((k b) p))
            → M a (tr a i k))
      → (a : A) (i : I a) (r : (b : A) → C a i b → ▹ b)
      → El-▹ M q₁ q₂ a (tr a i r) ≡ q₂ a i r λ b p → El-▹ M q₁ q₂ b (r b p)

C₂-▹ M q₁ q₂ a i r = refl
