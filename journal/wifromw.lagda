
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module wifromw where

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

\end{code}

%endif

\subsubsection{|WI| from |W|}

\begin{code}

WWI′ : (I : Set) (S : I → Set) (P : (i : I) (s : S i) → I → Set) → Set
WWI′ I S P = W (Σ I S) (uncurry λ i s → Σ I (P i s))

WWIl : (I : Set) (S : I → Set) (P : (i : I) (s : S i) → I → Set) → Set
WWIl I S P = W (I × (Σ I S)) (uncurry λ _ → uncurry λ i s → Σ I (P i s))

lup : (I : Set) (S : I → Set) (P : (i : I) (s : S i) → I → Set) → WWI′ I S P → WWIl I S P 
lup I S P (sup (i , s) f) = sup (i , (i , s)) (λ p → lup I S P (f p))

ldown : (I : Set) (S : I → Set) (P : (i : I) (s : S i) → I → Set) → I → WWI′ I S P → WWIl I S P 
ldown I S P i (sup s f) = sup (i , s) (uncurry λ i′ p → ldown I S P i′ (f (i′ , p)))

WWI : (I : Set) (S : I → Set) (P : (i : I) (s : S i) → I → Set) → I → Set
WWI I S P i = Σ (WWI′ I S P) λ x → lup I S P x ≡ ldown I S P i x 

supi :  {I : Set} {S : I → Set} {P : (i : I) (s : S i) → I → Set} {i : I} 
        (s : S i) (f : {i′ : I} → P i s i′ → WWI I S P i′) → WWI I S P i
supi s f =    (sup (_ , s) (λ p →  proj₁ (f (proj₂ p)))) 
           ,  cong (sup (_ , _ , s)) (ext λ p → proj₂ (f (proj₂ p)))

  

\end{code}

