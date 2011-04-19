{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module common where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Data.Product as Prod
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

ids : ∀ {l} {A : Set l} → A → A
ids = id 

idt : ∀ {l} {A : Set l} → A → A
idt = id 

infixr 102 ↦_!m

↦_!m : ∀ {l} {A : Set l} → A → A
↦_!m = id 

infixr 103 split_!s

split_!s : ∀ {l} {A : Set l} → A → A
split_!s = id 

infixr 101 unc
infixr 102 ids
infixr 102 idt

syntax unc (λ x → t) = x & t
syntax ids (λ x → t) = x tilps t 
syntax idt (λ x → t) = x !* t 

_$$_ : ∀ {l l'} {A : Set l} {B : A → Set l'} →
      ((x : A) → B x) → ((x : A) → B x)
f $$ x = f x

_-**->_ : {I : Set} -> (A B : I -> Set) -> Set
_-**->_ {I} A B = {i : I} -> A i -> B i


subst₂′ : ∀ {a b p} {A : Set a} {B : A → Set b} (P : (a : A) → B a → Set p) →
          ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
subst₂′ P refl refl p = p

_->>_ : ∀ {l l'} → (A : Set l) (B : Set l') -> Set (l ⊔ l')
_->>_ A B = A  -> B 