{-# OPTIONS --universe-polymorphism #-}

module Cont where

  open import Level
  open import Function
  open import Func
  open import Unit
  open import Data.Product renaming (uncurry to split)
  open import HeterogeneousEquality
  open import Isomorphism

  record Cont {l : Level} : Set (suc l)  where
    constructor _◁_
    field
      sh : Set l
      po : sh → Set l

  ⟦_⟧ : ∀ {l} → Cont {l} → Func {l}
  ⟦_⟧ (S ◁ P) = 
    func (λ X → Σ S λ s → P s → X) 
         (λ f → split (λ x y → x , f ∘ y)) 
         (λ _ → refl) (λ _ _ _ → refl)

  record _⇒_ {l : Level} (C D : Cont {l}) : Set l where
    constructor _◁_
    field 
      sh : Cont.sh C → Cont.sh D
      po : (s : Cont.sh C) → Cont.po D (sh s) → Cont.po C s   
  
  record _≡^C_ {l : Level} (C D : Cont {l}) : Set l where
    field
      sh : Cont.sh C ≈ Cont.sh D
      po : (s : Cont.sh C) → Cont.po C s ≈ Cont.po D (_≈_.φ sh s) 

  Id : ∀ {l} → Cont {l} ; Id = ⊤ ◁ λ _ → ⊤

  Comp : ∀ {l} → (C D : Cont {l}) → Cont {l}
  Comp C (T ◁ Q) = Func.obj ⟦ C ⟧ T ◁ split (λ x y → Σ (Cont.po C x) λ p → Q (y p))

  rule : ∀ {l} {C : Cont {l}} → Comp C Id ≡^C C
  rule = record { sh = record { φ = proj₁; ψ = λ s → s , _; φψ = refl; ψφ = refl }; po = split (λ x y → record { φ = proj₁; ψ = λ p → p , _; φψ = refl; ψφ = refl }) }

  ⟦_⟧⇒ : {l : Level} {C D : Cont {l}} (m : C ⇒ D) → NatTrans ⟦ C ⟧ ⟦ D ⟧ 
  ⟦ f ◁ r ⟧⇒ = record { fun = split λ x y → f x , (λ q → y (r x q)); law = λ x → refl }

  q⇒ : {l : Level} {C D : Cont {l}} → NatTrans ⟦ C ⟧ ⟦ D ⟧ → C ⇒ D
  q⇒ {C = S ◁ P} {D = T ◁ Q} nt =  (λ s → proj₁ (trick s)) ◁ λ s → proj₂ (trick s) 
    where trick : (s : S) → Func.obj ⟦ T ◁ Q ⟧ (P s)
          trick s = NatTrans.fun nt (s , λ p → p)


