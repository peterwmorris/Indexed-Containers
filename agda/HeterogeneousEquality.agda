------------------------------------------------------------------------
-- Heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module HeterogeneousEquality where

open import Data.Product
open import Function
open import Function.Inverse using (Inverse)
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.Indexed as I using (_at_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_ _≇_

data _≅_ {l} {A : Set l} (x : A) : {B : Set l} → B → Set l where
  refl : x ≅ x

-- Nonequality.

_≇_ : ∀ {a} {A : Set a} → A → {B : Set a} → B → Set a
x ≇ y = ¬ x ≅ y

------------------------------------------------------------------------
-- Conversion

≡-to-≅ : ∀ {l} {A : Set l} {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

≅-to-≡ : ∀ {l} {A : Set l} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

------------------------------------------------------------------------
-- Some properties

reflexive : ∀ {l} {A : Set l} → _⇒_ {A = A} _≡_ (λ x y → x ≅ y)
reflexive refl = refl

sym : ∀ {l} {A : Set l} {B : Set l} {x : A} {y : B} → x ≅ y → y ≅ x
sym refl = refl

trans : ∀ {l} {A : Set l} {B : Set l} {C : Set l}
          {x : A} {y : B} {z : C} →
        x ≅ y → y ≅ z → x ≅ z
trans refl refl = refl

subst : ∀ {l} {A : Set l} {p} → Substitutive {A = A} (λ x y → x ≅ y) p
subst P refl p = p

subst₂ : ∀ {l p} {A : Set l} {B : Set l} (P : A → B → Set p) →
         ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

subst-removable : ∀ {l p} {A : Set l}
                  (P : A → Set p) {x y} (eq : x ≅ y) z →
                  subst P eq z ≅ z
subst-removable P refl z = refl

≡-subst-removable : ∀ {l p} {A : Set l}
                    (P : A → Set p) {x y} (eq : x ≡ y) z →
                    PropEq.subst P eq z ≅ z
≡-subst-removable P refl z = refl

cong : ∀ {l l'} {A : Set l} {B : A → Set l'} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

cong₂ : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : ∀ x → B x → Set l''}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂ f refl refl = refl

resp₂ : ∀ {l ℓ} {A : Set l} (∼ : Rel A ℓ) → ∼ Respects₂ (λ x y → x ≅ y)
resp₂ _∼_ = subst⟶resp₂ _∼_ subst

proof-irrelevance : ∀ {l} {A : Set l} {B : Set l} {x : A} {y : B}
                    (p q : x ≅ y) → p ≡ q
proof-irrelevance refl refl = refl



UIP' : ∀ {l} {A : Set l} {a : A} {B : Set l} {b : B} {p : b ≅ a} → _≅_ {_} {b ≅ b} refl p
UIP' {p = refl} = refl

isEquivalence : ∀ {l} {A : Set l} →
                IsEquivalence {A = A} (λ x y → x ≅ y)
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }


app≅ : {l l' : Level} {A : Set l} {B : A → Set l'} {f g : (a : A) → B a} → f ≅ g → (a : A) → f a ≅ g a 
app≅ refl a = refl

app≅' : {l l' : Level} {A : Set l} {A' : Set l} → A ≅ A' → {B : A → Set l'} {B' : A' → Set l'} → B ≅ B' → {f : (a : A) → B a} {g : (a' : A') → B' a'} → f ≅ g → (a : A) (a' : A') → a ≅ a' → f a ≅ g a' 
app≅' refl refl refl a .a refl = refl


postulate
  ext' : {l l' : Level} {A A' : Set l} {B : A → Set l'} {B' : A' → Set l'} {f : (a : A) → B a} {g : (a : A') → B' a} → ((a : A) (a' : A') → a ≅ a' → f a ≅ g a') → f ≅ g
  iext' : {l l' : Level} {A A' : Set l} {B : A → Set l'} {B' : A' → Set l'} {f : {a : A} → B a} {g : {a : A'} → B' a} → ({a : A} {a' : A'} → a ≅ a' → f {a} ≅ g {a'}) → (\{x} -> f {x}) ≅ (\{x} -> g {x}) 

postulate
  ext : {l l' : Level} {A : Set l} {B : A → Set l'} {f g : (a : A) → B a} → ((a : A) → f a ≅ g a) → f ≅ g
  iext : {l l' : Level} {A : Set l} {B : A → Set l'} {f g : {a : A} → B a} → ({a : A} → f {a} ≅ g {a}) → (\{x} -> f {x}) ≅ (\{x} -> g {x}) 
