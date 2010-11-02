
{-# OPTIONS --universe-polymorphism #-}

module IFunc where

open import Level
open import Function
open import HeterogeneousEquality 
open import Isomorphism

_⟶_ : ∀ {l} {I : Set l} (A B : I → Set l) → Set l
_⟶_ {_} {I} A B = {i : I} → A i → B i

_⊚_ : ∀ {l} {I : Set l} {A B C : I → Set l} → (B ⟶ C) → (A ⟶ B) → A ⟶ C
_⊚_ f g {i} = f {i} ∘ g {i}

-- To simplfy we want a Lift which only goes up 1 floor: 

record ↑ {ℓ} (A : Set ℓ) : Set (suc ℓ) where
  constructor lift
  field ground : A

open ↑ public

-- Lift is a functor from Set l to Set (suc l) its action on morphisms given by:

↑M : {l : Level} {A B : Set l} {B : Set l} (f : A → B) → ↑ A → ↑ B
↑M f (lift a) = lift (f a) 

-- it should be obvious that this satisfies the functor laws



record IFunc {l : Level} (I : Set l) : Set (suc l) where
  constructor ifunc
  field
    obj : (I → Set l) → Set l
    mor : {A B : I → Set l} → (A ⟶ B) → obj A → obj B 
    idlaw : {A : I → Set l} → id {_} {obj A} ≅ mor {A} {A} id 
    complaw : {A B C : I → Set l} (f : B ⟶ C) (g : A ⟶ B) →
                (mor {B} {C}) f ∘ (mor {A} {B} g) ≅
                  mor {A} {C} (_⊚_ {B = B} f g) 

record NatTrans {l : Level} {I : Set l} (F G : IFunc I) : Set (suc l) where
  constructor nattrans
  field 
    fun : {A : I → Set l} → IFunc.obj F A → IFunc.obj G A
    law : {A B : I → Set l} {f : A ⟶ B} → 
            fun {B} ∘ (IFunc.mor F f) ≅ IFunc.mor G f ∘ (fun {A})
 
record _≅^F_ {l : Level} {I : Set l} (F G : IFunc I) : Set (suc l) where
  field 
    fiso : {A : I → Set l} → IFunc.obj F A ≈ IFunc.obj G A 
    law1 :  {A B : I → Set l} {f : A ⟶ B} → 
              _≈_.φ (fiso {B}) ∘ (IFunc.mor F f) ≅ IFunc.mor G f ∘ (_≈_.φ (fiso {A}))
    law2 : {A B : I → Set l} {f : A ⟶ B} → 
              _≈_.ψ (fiso {B}) ∘ (IFunc.mor G f) ≅ IFunc.mor F f ∘ (_≈_.ψ (fiso {A}))