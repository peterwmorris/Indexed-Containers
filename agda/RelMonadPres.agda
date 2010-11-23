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

  ηpres : {l : Level} (I : Set l) (i : I) → (η^F i) ≅^F ⟦ η^C i ⟧
  ηpres {l} I i = record { fiso = λ {A} → iso (λ a → _ , λ p → subst A p a) (split (λ _ a → a refl)) (ext (λ a → cong₂ _,_ refl (iext (ext (foo a))))) refl; law1 = λ {A} {B} {f} → ext (λ a → cong₂ _,_ refl (iext (ext (λ p → trans (subst-removable B p (f a)) (cong₂ (λ i → f {i}) p (sym (subst-removable A p a))))))); law2 = refl }
    where foo : {A : I → Set l} {i' : I} (x : Σ (⊤ {l}) λ _ → {i' : I} → i ≅ i' → A i') 
                 (p : i ≅ i') → subst A p (proj₂ x refl) ≅ proj₂ x p
          foo (_ , f) refl = refl

  >>=pres : {l : Level} (I J : Set l) (H : I → ICont J) (F : ICont I) →
             ((λ i → ⟦ H i ⟧) >>=^F ⟦ F ⟧) ≅^F ⟦ H >>=^C F ⟧
  >>=pres {l} I J H (S ◁ P) = 
    record { fiso = λ {A} → iso (split (λ s f → (s , (λ i p → proj₁ (f {i} p))) , (λ {j} → split (split (λ i p q → proj₂ (f {i} p) q))))) (split (split (λ s f g → s , λ {i} p → (f i p) , (λ {j} q → g {j} ((i , p) , q))))) (ext (λ _ → refl)) refl; 
             law1 = refl; law2 = refl }   