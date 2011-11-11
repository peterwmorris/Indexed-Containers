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
          (λ f → split (λ x y → x , (λ {_} p → (f (y p))))) 
          refl (λ f g → refl)

  _⇒_ : {l : Level} {I : Set l} (C D : ICont I) → Set l 
  C ⇒ D = (s : ICont.sh C) → Σ (ICont.sh D) λ t → ICont.po D t ⟶ ICont.po C s  

  {- 
  record _⇒_ {l : Level} {I : Set l} (C D : ICont I) : Set l where
    constructor _◁_
    field 
      sh : ICont.sh C → ICont.sh D
      po : (s : ICont.sh C) → ICont.po D (sh s) ⟶ ICont.po C s   
  -}

  ⟦_⟧⇒ : {l : Level} {I : Set l} {C D : ICont I} (m : C ⇒ D) → NatTrans ⟦ C ⟧ ⟦ D ⟧ 
  ⟦ m ⟧⇒ = record { fun = split (λ s f → proj₁ (m s) , (λ {_} p → f (proj₂ (m s) p))) ; law = refl }

  q⇒ : {l : Level} {I : Set l} {C D : ICont I} → NatTrans ⟦ C ⟧ ⟦ D ⟧ → C ⇒ D
  q⇒ {C = S ◁ P} {D = T ◁ Q} nt =  λ s → NatTrans.fun nt (s , λ p → p) -- (λ s → proj₁ (trick s)) ◁ λ s → proj₂ (trick s) 

  {-
    where trick : (s : S) → IFunc.obj ⟦ T ◁ Q ⟧ (P s)
          trick s = NatTrans.fun nt (s , λ p → p)
-}
  record _≅^C_ {l : Level} {I : Set l} (C D : ICont I) : Set l where
    field 
      sh : ICont.sh C ≈ ICont.sh D
      po : (s : ICont.sh C) → ICont.po C s ≈≈ ICont.po D (_≈_.φ sh s)

  Δ^C : ∀ {l} {I : Set l} {J K : Set l} → (J → K) → (K → ICont I) → J → ICont I
  Δ^C f F j = F (f j) 

  Σ^C : ∀ {l} {I J K : Set l} → (J → K) → (J → ICont I) → K → ICont I
  Σ^C {J = J} f F k =     (Σ J λ j → f j ≅ k × ICont.sh (F j)) 
                       ◁  split (λ j → split λ p x → ICont.po (F j) x) 

  Π^C : ∀ {l} {I J K : Set l} → (J → K) → (J → ICont I) → K → ICont I
  Π^C {J = J} f F k =     ((j : J) → f j ≅ k → ICont.sh (F j)) 
                       ◁  λ g i → Σ J λ j → Σ (f j ≅ k) λ p → ICont.po (F j) (g j p) i 
 
  Δ≅ : ∀ {l} {I : Set l} {J K : Set l} (f : J → K) (F : K → ICont I) (j : J) {X : I → Set l} → IFunc.obj ⟦ Δ^C f F j ⟧ X ≅ IFunc.obj (Δ^F f (λ k → ⟦ F k ⟧) j) X
  Δ≅ f F j = refl

  Σ≅ : ∀ {l} {I : Set l} {J K : Set l} (f : J → K) (F : J → ICont I) (k : K) → ⟦ Σ^C f F k ⟧ ≅^F  Σ^F f (λ j → ⟦ F j ⟧) k
  Σ≅ f F k = record { fiso = λ {A} → iso (λ x → _ , (_ , (_ , (proj₂ x)))) (split (λ w → split (λ x → split (λ y z → (w , (x , y)) , z)))) refl refl; law1 = refl; law2 = refl }

  Π≅ : ∀ {l} {I : Set l} {J K : Set l} (f : J → K) (F : J → ICont I) (k : K) → ⟦ Π^C f F k ⟧ ≅^F  Π^F f (λ j → ⟦ F j ⟧) k
  Π≅ f F k = record { fiso = λ {A} → iso ( λ x j x' → (proj₁ x j x') , (λ x0 → proj₂ x (j , (x' , x0)))) (λ x → (λ j p → proj₁ (x j p)) , λ {i} → split (λ j → split λ p q → proj₂ (x j p) q)) refl refl; law1 = refl; law2 = refl }
 
{-

  Σ^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
  Σ^C {J} f (S ◁* P) =  λ* λ k →  (Σ J λ j → f j ≡ k × S j) ◁
                                split j & eq & s tilps ↦ P j s !m !s
 
  Π^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
  Π^C {J} f (S ◁* P) =  λ* λ k →  ((j : J) → f j ≡ k → S j) ◁
                                  λ s i → Σ J λ j → Σ (f j ≡ k) λ eq → P j (s j eq) i 


-}