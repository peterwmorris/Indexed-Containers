{-# OPTIONS --universe-polymorphism #-}

module IFuncRelMonad where

open import Level
open import Function
open import HeterogeneousEquality 
open import IFunc
open import Isomorphism

η^F : {l : Level} {I : Set l} → ↑ I → IFunc I
η^F (lift i) = ifunc (λ A → A i) (λ f → f) refl (λ f g → refl) -- (λ x → refl) (λ f g x → refl)

_>>=^F_ : {l : Level} {I J : Set l} (H : ↑ I → IFunc J) (F : IFunc I) → IFunc J
H  >>=^F (ifunc obj mor idlaw complaw) = 
  ifunc (λ A → obj (λ i → IFunc.obj (H (lift i)) A)) 
        (λ f → mor (IFunc.mor (H _) f)) 
        (ext (λ x → trans (app≅ idlaw x) (cong₂ mor (iext (ext (λ a → app≅ (IFunc.idlaw (H _)) a))) refl))) (
        (λ f g → ext (λ x → trans (app≅ (complaw _ _) x) (cong₂ mor (iext (IFunc.complaw (H _) _ _)) refl)))) 

law1F : {l : Level} {I : Set l} {F : IFunc I} → F ≅^F (η^F >>=^F F)
law1F {F = ifunc a b c d} = record { fiso = λ {A} → iso id id refl refl; law1 = refl; law2 = refl }

law2F : {l : Level} {I J K : Set l} {H : ↑ J → IFunc K} {H' : ↑ I → IFunc J} {F : IFunc I} → (H >>=^F (H' >>=^F F)) ≅^F ((λ i → H >>=^F (H' i)) >>=^F F)
law2F {F = ifunc a b c d} = record { fiso = λ {A} → iso id id refl refl; law1 = refl; law2 = refl }




  