{-# OPTIONS --universe-polymorphism #-}

module Isomorphism where

  open import Level
  open import HeterogeneousEquality
  open import Function
  open import Relation.Binary.Core

  record _≈_ {l : Level} (A B : Set l) : Set l where
   constructor iso
   field
     φ : A → B
     ψ : B → A
     φψ : φ ∘ ψ ≅ id {_} {B}
     ψφ : ψ ∘ φ ≅ id {_} {A} 

  ≈refl : ∀ {l} {A : Set l} → A ≈ A
  ≈refl = record { φ = id; ψ = id; φψ = refl; ψφ = refl } 

  ≈sym : ∀ {l} {A B : Set l} → A ≈ B → B ≈ A
  ≈sym (iso φ ψ φψ ψφ) = record { φ = ψ; ψ = φ; φψ = ψφ; ψφ = φψ }

  ≈trans : ∀ {l} {A B C : Set l} → B ≈ C → A ≈ B → A ≈ C
  ≈trans (iso φ ψ φψ ψφ) (iso φ' ψ' φψ' ψφ') = 
    iso (φ ∘ φ') (ψ' ∘ ψ) 
        (ext (λ a → subst (λ f → φ (f (ψ a)) ≅ a) (sym φψ') (app≅ φψ a))) (
        (ext (λ c → subst (λ g → ψ' (g (φ' c)) ≅ c) (sym ψφ) (app≅ ψφ' c))))

  _≈≈_ : {l l' : Level} {I : Set l} (A B : I → Set l') → Set (l ⊔ l')
  _≈≈_ {I = I} A B = {i : I} → A i ≈ B i