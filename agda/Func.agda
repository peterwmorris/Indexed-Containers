
{-# OPTIONS --universe-polymorphism #-}

module Func where

open import Level
open import Function
open import HeterogeneousEquality 

-- To simplfy we want a Lift which only goes up 1 floor: 

record Func {l : Level} : Set (suc l) where
  constructor func
  field
    obj : Set l → Set l
    mor : {A B : Set l} → (A → B) → obj A → obj B 
    idlaw : {A : Set l} (x : obj A) → id x ≅ mor {A} {A} (λ a → a) x
    complaw : {A B C : Set l} (f : B → C) (g : A → B) →
               (x : obj A) → mor {B} {C} f (mor {A} {B} g x) ≅
                              mor {A} {C} (λ a → f (g a)) x

record NatTrans {l : Level} (F G : Func) : Set (suc l) where
  constructor nattrans
  field 
    fun : {A : Set l} → Func.obj F A → Func.obj G A
    law : {A B : Set l} {f : A → B} (x : Func.obj F A) → 
            fun {B} (Func.mor F f x) ≅ Func.mor G f (fun {A} x)
 