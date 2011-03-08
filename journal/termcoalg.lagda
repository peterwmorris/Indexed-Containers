
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module termcoalg where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality
open import Coinduction
open import Data.Nat hiding (_⊔_)
open import Relation.Nullary

open import common
open import tt
open import ifunc
open import icont

\end{code}

%endif

\section{Terminal Co-Algebras of Indexed Containers}

%format ∞ = "\infty"
%format ♯ = "\sharp"
%format ♭ = "\flat"
%format ν = "\nu"
%format ν^C = ν ^C
%format out^C = out ^C

\begin{code}

data MI  {I : Set} (S : I → Set) 
         (PI : (i : I) → S i → I → Set) : I → Set where
  sup : obj* ⟦ S ◁* PI ⟧* (λ i → ∞ (MI S PI i))  -**-> MI S PI 

sup⁻¹ :  {I : Set} {S : I → Set} {PI : (i : I) → S i → I → Set} →
          MI S PI -**-> obj* ⟦ S ◁* PI ⟧* (MI S PI)
sup⁻¹ (sup (s , f)) = s , λ i p → ♭ (f i p)

\end{code}

%if style == newcode

\begin{code}

unsup : {I : Set} {S : I → Set} {PI : (i : I) → S i → I → Set} → 
          {P : (i : I) → MI S PI i → Set} → ({i : I} (sf : Σ[ s ∶ S i ] ((i′ : I) → PI i s i′ → ∞ (MI S PI i′))) → P i (sup sf)) → {i : I} → (x : MI S PI i) → P i x
unsup f (sup x) = f x

\end{code}

%endif

\begin{code}

MIunfold :  ∀  {I} {X : I → Set} {S : I → Set} 
             {PI : (i : I) → S i → I → Set} →
             X -*-> obj* ⟦ S ◁* PI ⟧* X → X -*-> MI S PI 
MIunfold m i x with m i x
MIunfold m i x | s , f = sup (s , (λ i′ p → ♯ MIunfold m i′ (f i′ p)))

data Path  {I J : Set} (S : I → Set)  
           (PI  : (i : I) → S i → I  → Set) 
           (PJ  : (i : I) → S i → J  → Set) 
           : (i : I) → MI S PI i → J → Set where
  path : ∀  {i s f j} →     
               PJ i s j 
            ⊎  (Σ I λ i′ → Σ (PI i s i′) λ p → Path S PI PJ i′ (♭ (f i′ p)) j) 
            → Path S PI PJ i (sup (s , f)) j 

ν^C : {I J : Set} → ICont* (I ⊎ J) I → ICont* J I
ν^C {I} {J} (S ◁* P) = 
  let  PI  : (i : I) → S i → I  → Set ;  PI  i s i′  = P $$ i $$ s $$ (inj₁ i′) 
       PJ  : (i : I) → S i → J  → Set ;  PJ  i s j   = P $$ i $$ s $$ (inj₂ j)
  in   MI S PI ◁* Path S PI PJ

out^C : ∀ {I J} → (F : ICont* (I ⊎ J) I) → ν^C F ⇒* F ⟨ ν^C F ⟩C* 
out^C {I} {J} (S ◁* P) = (λ _ → sup⁻¹) ◁* unsup {_} {_} {_} {λ j s → (i : J) → P j (proj₁ (sup⁻¹ s)) (inj₂ i) ⊎
      Σ I
      (λ i' →
         Σ (P j (proj₁ (sup⁻¹ s)) (inj₁ i'))
         (λ p →
            Path S (λ i0 s' i′ → P i0 s' (inj₁ i′))
            (λ i0 s' j' → P i0 s' (inj₂ j')) i' (proj₂ (sup⁻¹ s) i' p) i)) →
      Path S (λ i' s' i′ → P i' s' (inj₁ i′))
      (λ i' s' j' → P i' s' (inj₂ j')) j s i} (λ sf i′ p → path p)

unfold^C : ∀  {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → 
              G ⇒* F ⟨ G ⟩C* → G ⇒* ν^C F
unfold^C {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = funfold ◁* runfold  
    where  PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = P i s (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = P i s (inj₂ j)
           funfold = MIunfold f
           runfold :  {i : I} (t : T i) (j : J) → Path S PI PJ i (funfold i t) j → Q i t j 
           runfold t j (path (inj₁ x)) = r t j (inj₁ x)
           runfold t j (path (inj₂ (i , (p , q)))) = r t j (inj₂ (i , p , runfold (proj₂ (f _ t) i p) j q))

\end{code}