
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Inductive.Constructors.Ind-types

module Inductive.Equivalences.Ind-give-▹
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  (V : A → Set)
  where

I+V : A → Set
I+V a = I a ⊎ V a

C+V : (a : A) → I+V a → A → Set
C+V a (inj₁ i) = C a i
C+V a (inj₂ r) = λ _ → ⊥

absurd : (a : A) → ⊥ → Ind C+V a
absurd a ()

Canonical : {a : A} → Ind C+V a → Set
Canonical (ind _ (inj₁ i) f) = ∀ b r → Canonical (f b r)
Canonical (ind _ (inj₂ r) f) = f ≡ absurd

▹ : A → Set
▹ a = Σ (Ind C+V a) Canonical

rf : (a : A) → V a → ▹ a
rf a r = ind a (inj₂ r) absurd , refl

tr : (a : A) (i : I a) → ((b : A) → C a i b → ▹ b) → ▹ a
tr a i f = (ind a (inj₁ i) (λ j r → proj₁ (f j r))) ,
            λ b r → proj₂ (f b r)

El-▹ : ∀ {e} → (M : (a : A) → ▹ a → Set e)
        (q₁ : (a : A) (r : V a) → M a (rf a r))
        (q₂ : (a : A)
              (i : I a)
              (k : (b : A) → C a i b → ▹ b)
              (f : (b : A) → (p : C a i b) → M b ((k b) p))
              → M a (tr a i k))
          → (a : A) (m : ▹ a)
          → M a m

El-▹ M q₁ q₂ a (ind a (inj₂ r) absurd , refl) =
  q₁ a r

El-▹ M q₁ q₂ a (ind a (inj₁ i) f , c) =
  q₂ a i
  (λ b r → (f b r) , (c b r))
  λ b r → El-▹ M q₁ q₂ b ((f b r) , (c b r))

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