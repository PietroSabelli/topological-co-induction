
{-# OPTIONS --without-K --exact-split #-}

open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Data.Product.Properties

module operators where

record _≅_ (A : Set) (B : Set) : Set where
  field 
    to   : A → B
    from : B → A
    to∘from : ∀ {a} → from (to a) ≡ a
    from∘to : ∀ {b} → to (from b) ≡ b

_⇒_ : ∀ {A : Set} → (A → Set) → (A → Set) → Set _
_⇒_ {A = A} P Q = {a : A} → P a → Q a

_∘_ : ∀ {A} {P Q R : A → Set} → Q ⇒ R → P ⇒ Q → P ⇒ R
g ∘ f = λ p → g (f p)

postulate
  funext : {A : Set} {B : A → Set} {f g : (a : A) → B a}
    → (∀ x → f x ≡ g x) → f ≡ g

module _
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

  id : ∀ {P : A → Set} → P ⇒ P
  id {P} {a} = λ z → z

  Der : ∀ {l₄} → (A → Set l₄) → A → Set _
  Der P a = Σ (I a) λ i → ∀ b → C a i b → P b

  Der⇒ : ∀ {P Q} → P ⇒ Q → Der P ⇒ Der Q
  Der⇒ p (i , f) = i , λ b c → p (f b c)

  Der-id : ∀ {P a} → Der⇒ (id {P}) {a} ≡ id {Der P} {a}
  Der-id = funext (λ { (_ , _) → refl })

  Conf : ∀ {l₄} → (A → Set l₄) → A → Set _
  Conf P a = ∀ i → Σ A λ b → C a i b × P b

  Conf⇒ : ∀ {P Q} → P ⇒ Q → Conf P ⇒ Conf Q
  Conf⇒ p q i with q i
  ... | b , c , r = b , c , p r

  -- Topological operators
  module _ (V : A → Set) where

    Der▹ : (A → Set) → A → Set
    Der▹ P a = V a ⊎ Σ (I a) λ i → ∀ b → C a i b → P b

    Der▹⇒ : ∀ {P Q} → P ⇒ Q → Der▹ P ⇒ Der▹ Q
    Der▹⇒ p (inj₁ r) = inj₁ r
    Der▹⇒ p (inj₂ (i , f)) = inj₂ (i , λ b c → p (f b c))

    Conf⋊ : (A → Set) → A → Set
    Conf⋊ P a = V a × ∀ i → Σ A λ b → C a i b × P b

    Conf⋊⇒ : ∀ {P Q} → P ⇒ Q → Conf⋊ P ⇒ Conf⋊ Q
    Conf⋊⇒ p (v , f) =
      v , λ i → proj₁ (f i) , proj₁ (proj₂ (f i)) , p (proj₂ (proj₂ (f i)))
    
-- With alternative parameters Br ar
module _
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) (i : I a) → Br a i → A)
  where

  Der' : (A → Set) → A → Set
  Der' P a = Σ (I a) λ i → ∀ b → P (ar a i b)

  Der'⇒ : ∀ {P Q} → P ⇒ Q → Der' P ⇒ Der' Q
  Der'⇒ p (i , f) = i , λ b → p (f b)

  Conf' : (A → Set) → A → Set
  Conf' P a = ∀ i → Σ (Br a i) λ b → P (ar a i b)

  Conf'⇒ : ∀ {P Q} → P ⇒ Q → Conf' P ⇒ Conf' Q
  Conf'⇒ p f i with f i
  ... | b , q = b , p q


module Conf-give-Conf'
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) (i : I a) → Br a i → A)
  (funext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  C : (a : A) → I a → A → Set
  C a i b = Σ (Br a i) λ z → ar a i z ≡ b

  η : (P : A → Set) → Conf C P ⇒ Conf' Br ar P
  η P {a} f i with f i
  ... | _ , (b , refl) , p = b , p

  η-naturality : ∀ {P Q}
    → (f : P ⇒ Q) {a : A} (p : Conf C P a)
    → (Conf'⇒ Br ar {P} {Q} f) (η P p)
      ≡
      (η Q) (Conf⇒ C f p)
  η-naturality {P} {Q} p {a} f = funext help
    where
    help : ∀ i → Conf'⇒ Br ar {P} {Q} p (η P f) i ≡ η Q (Conf⇒ C p f) i
    help i with f i
    ... | _ , (b , refl) , q = refl

  η⁻¹ : (P : A → Set) → Conf' Br ar P ⇒ Conf C P
  η⁻¹ P f i with f i
  ... | b , p = ar _ i b , (b , refl) , p

  η∘η⁻¹ : ∀ {P} {a} {w : Conf' Br ar P a} → η P (η⁻¹ P w) ≡ w
  η∘η⁻¹ = refl

  η⁻¹∘η : ∀ {P} {a} {w : Conf C P a} → η⁻¹ P (η P w) ≡ w
  η⁻¹∘η {P} {a} {w = f} = funext help
    where
    help : ∀ i → η⁻¹ P (η P f) i ≡ f i
    help i with f i
    ... | _ , (b , refl) , p = refl

module Conf'-give-Conf
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

  Br : (a : A) → I a → Set
  Br a i = Σ A (C a i)
  
  ar : (a : A) (i : I a) → Br a i → A
  ar a i = proj₁

  η : (P : A → Set) → Conf' Br ar P ⇒ Conf C P
  η P {a} f i with f i
  ... | (b , c) , p = b , c , p

  η-naturality : ∀ {P Q} → (f : P ⇒ Q) {a : A} (p : Conf' Br ar P a)
    → (Conf⇒ C {P} {Q} f) (η P p)
      ≡
      (η Q) (Conf'⇒ Br ar f p)
  η-naturality {P} {Q} f {a} p = refl

  η⁻¹ : (P : A → Set) → Conf C P ⇒ Conf' Br ar P
  η⁻¹ P f i with f i
  ... | b , c , p = (b , c) , p

  η∘η⁻¹ : ∀ {P} {a} {w : Conf C P a} → η P (η⁻¹ P w) ≡ w
  η∘η⁻¹ = refl

  η⁻¹∘η : ∀ {P} {a} {w : Conf' Br ar P a} → η⁻¹ P (η P w) ≡ w
  η⁻¹∘η = refl

module Der-give-Der'
  {A : Set}
  {I : A → Set}
  (Br : (a : A) → I a → Set)
  (ar : (a : A) (i : I a) → Br a i → A)
  (funext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  C : (a : A) → I a → A → Set
  C a i b = Σ (Br a i) λ z → ar a i z ≡ b

  η : (P : A → Set) → Der C P ⇒ Der' Br ar P
  η P {a} (i , f) = i , λ b → f (ar a i b) (b , refl)

  η-naturality : ∀ {P Q}
    → (f : P ⇒ Q) {a : A} (p : Der C P a)
    → (Der'⇒ Br ar {P} {Q} f) (η P p)
      ≡
      (η Q) (Der⇒ C f p)
  η-naturality f p = refl

  η⁻¹ : (P : A → Set) → Der' Br ar P ⇒ Der C P
  η⁻¹ P {a} (i , f) = i , (λ { _ (b , refl) → f b })

  η∘η⁻¹ : ∀ {P} {a} {w : Der' Br ar P a} → η P (η⁻¹ P w) ≡ w
  η∘η⁻¹ = refl

  η⁻¹∘η : ∀ {P} {a} {w : Der C P a} → η⁻¹ P (η P w) ≡ w
  η⁻¹∘η {P} {a} {w = i , f} =
    Σ-≡,≡→≡ (refl ,
      funext λ x →
      funext λ { (b , refl) → refl })
      
module Der'-give-Der
  {A : Set}
  {I : A → Set}
  (C : (a : A) → I a → A → Set)
  where

  Br : (a : A) → I a → Set
  Br a i = Σ A (C a i)
  
  ar : (a : A) (i : I a) → Br a i → A
  ar a i = proj₁

  η : (P : A → Set) → Der' Br ar P ⇒ Der C P
  η P {a} (i , f) = i , λ b c → f (b , c)

  η-naturality : ∀ {P Q} → (f : P ⇒ Q) {a : A} (p : Der' Br ar P a)
    → (Der⇒ C {P} {Q} f) (η P p)
      ≡
      (η Q) (Der'⇒ Br ar f p)
  η-naturality {P} {Q} f {a} p = refl

  η⁻¹ : (P : A → Set) → Der C P ⇒ Der' Br ar P
  η⁻¹ P (i , f) = i , (λ { (b , c) → f b c })

  η∘η⁻¹ : ∀ {P} {a} {w : Der C P a} → η P (η⁻¹ P w) ≡ w
  η∘η⁻¹ = refl

  η⁻¹∘η : ∀ {P} {a} {w : Der' Br ar P a} → η⁻¹ P (η P w) ≡ w
  η⁻¹∘η = refl  