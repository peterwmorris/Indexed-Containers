{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module common where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Product as Prod
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Coinduction
open import Data.Nat hiding (_⊔_)
open import Relation.Nullary

infixl 20  _$$_

unc : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : Σ A B → Set l''} →
      ((x : A) → (y : B x) → C (x , y)) →
      ((p : Σ A B) → C p)
unc = uncurry


_$$_ : ∀ {l l'} {A : Set l} {B : A → Set l'} →
      ((x : A) → B x) → ((x : A) → B x)
f $$ x = f x

_-**->_ : {I : Set} -> (A B : I -> Set) -> Set
_-**->_ {I} A B = {i : I} -> A i -> B i

cong′ : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≅ y → f x ≅ f y
cong′ f refl = refl

subst₂′ : ∀ {a b p} {A : Set a} {B : A → Set b} (P : (a : A) → B a → Set p) →
          ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
subst₂′ P refl refl p = p

_->>_ : ∀ {l l'} → (A : Set l) (B : Set l') -> Set (l ⊔ l')
_->>_ A B = A  -> B 

⊎case : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (x : A ⊎ B) →
        ((x : A) → C ) → ((x : B) → C ) →
        C 
⊎case (inj₁ x) l r = l x
⊎case (inj₂ y) l r = r y