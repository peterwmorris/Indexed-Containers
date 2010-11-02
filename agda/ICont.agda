{-# OPTIONS --universe-polymorphism #-}

module ICont where

  open import Level
  open import Function
  open import IFunc
  open import Unit
  open import Data.Product renaming (uncurry to split)
  open import HeterogeneousEquality 
  open import Isomorphism

  record ICont {l : Level} (I : Set l) : Set (suc l)  where
    constructor _◁_
    field
      sh : Set l
      po : sh → I → Set l

  ⟦_⟧ : ∀ {l} → {I : Set l} → ICont I → IFunc I
  ⟦_⟧ {I = I} (S ◁ P) = 
    ifunc (λ X → Σ S λ s → {i : I} → P s i → X i) 
          (λ f → split (λ x y → x , λ i → f (y i))) 
          refl (λ f g → refl)


  record _⇒_ {l : Level} {I : Set l} (C D : ICont I) : Set l where
    constructor _◁_
    field 
      sh : ICont.sh C → ICont.sh D
      po : (s : ICont.sh C) → ICont.po D (sh s) ⟶ ICont.po C s   
  
  ⟦_⟧⇒ : {l : Level} {I : Set l} {C D : ICont I} (m : C ⇒ D) → NatTrans ⟦ C ⟧ ⟦ D ⟧ 
  ⟦ f ◁ r ⟧⇒ = record { fun = split λ x y → f x , (λ q → y (r x q)); law = refl }

  q⇒ : {l : Level} {I : Set l} {C D : ICont I} → NatTrans ⟦ C ⟧ ⟦ D ⟧ → C ⇒ D
  q⇒ {C = S ◁ P} {D = T ◁ Q} nt =  (λ s → proj₁ (trick s)) ◁ λ s → proj₂ (trick s) 
    where trick : (s : S) → IFunc.obj ⟦ T ◁ Q ⟧ (P s)
          trick s = NatTrans.fun nt (s , λ p → p)

  record _≅^C_ {l : Level} {I : Set l} (C D : ICont I) : Set l where
    field 
      sh : ICont.sh C ≈ ICont.sh D
      po : (s : ICont.sh C) → ICont.po C s ≈≈ ICont.po D (_≈_.φ sh s)



