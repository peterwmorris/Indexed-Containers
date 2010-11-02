{-# OPTIONS --universe-polymorphism #-}

module IContRelMonad where

  open import Level
  open import Function
  open import HeterogeneousEquality 
  open import IFunc
  open import ICont
  open import Isomorphism
  open import Unit 
  open import Data.Product renaming (uncurry to split)

  η^C : {l : Level} {I : Set l} → ↑ I → ICont I
  η^C {I = I} (lift i) = ⊤ ◁ λ _ i' → (i ≅ i') 

  _>>=^C_ : {l : Level} {I J : Set l} (H : ↑ I → ICont J) (F : ICont I) → ICont J 
  _>>=^C_ {I = I} H (S ◁ P) = 
    (Σ S (λ s → (i : I) → P s i → ICont.sh (H (lift i)))) ◁ 
     split (λ s f j → Σ (Σ I λ i → P s i) 
                         (split (λ i p → ICont.po (H (lift i)) (f i p) j)))

  law1C : {l : Level} {I : Set l} {C : ICont I} → C ≅^C (η^C >>=^C C)
  law1C {I = I} {C = S ◁ P} = 
    record { sh = iso (λ s → s , _) proj₁ refl refl
           ; po = λ s {i} → iso (λ p → (i , p) , refl) 
                                (split (split λ x y z → subst (P s) z y))
                                (ext (foo s i)) refl }
               where foo : (s : S) (i : I) (a : Σ (Σ I (P s)) (λ x → proj₁ x ≅ i)) →
                       _≅_ {_} {Σ (Σ I (P s)) (λ x → proj₁ x ≅ i)} ((i , subst (P s) (proj₂ a) (proj₂ (proj₁ a))) , refl) a 
                     foo s .i ((i , p) , refl) = refl
           

  

  law2C : {l : Level} {I J K : Set l} {H : ↑ J → ICont K} {H' : ↑ I → ICont J} {F : ICont I} → (H >>=^C (H' >>=^C F)) ≅^C ((λ i → H >>=^C (H' i)) >>=^C F)
  law2C {l} {I} {J} {K} {H} {H'} {S ◁ P} = 
    record { sh = iso (split (split (λ x y z → x , (λ i p → (y i p) , (λ j q → z j ((i , p) , q)))))) (split λ x y → (x , (λ i p → proj₁ (y i p))) , (λ j → split (split (λ i p q → proj₂ (y i p) j q )))) refl refl; 
             po = λ s {i} → iso (split (split (λ j → split (λ ip q r → ip , (j , q) , r)))) (split (λ ip → split (split (λ j q r → (j , (ip , q)) , r)))) refl refl } 