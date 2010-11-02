{-# OPTIONS --universe-polymorphism #-}

module RelMonadPres where

  open import Level
  open import Function
  open import HeterogeneousEquality 
  open import IFunc
  open import ICont
  open import Isomorphism
  open import Unit 
  open import Data.Product renaming (uncurry to split)
  open import IFuncRelMonad
  open import IContRelMonad

  ηpres : {l : Level} {I : Set l} {i : ↑ I} → (η^F i) ≅^F ⟦ η^C i ⟧
  ηpres {l} {I} {i} = record { fiso = λ {A} → iso (λ a → _ , λ p → subst A p a) (split (λ _ a → a refl)) (ext (split λ _ f → cong₂ _,_ refl (iext (ext (λ p → foo {!!} p))) )) {!!}; law1 = {!!}; law2 = {!!} }
    where foo : {A : I → Set l} {i' : I} (f : {i' : I} → ground i ≅ i' → A i') 
                 (p : ground i ≅ i') → subst A p (f refl) ≅ f p
          foo f refl = refl