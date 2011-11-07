
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module termcoalg where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Product as Prod
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

\section{Terminal Coalgebras of Indexed Containers}
\label{sec:termcoalg}

Dually to the initial algebra construction outlined above, we can also show
that indexed containers are closed under parameterised terminal coalgebras.
We proceed in much the same way as before, by first constructing the dual of
the indexed |W|-type, which we refer to as an indexed |M|-type. As you might
expect this is in fact the plain (as opposed to parametrized) terminal
coalgebra of an indexed container:

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
          {P : (i : I) → MI S PI i → Set} → ({i : I} (sf : Σ* s ∶ S i *Σ ((i′ : I) → PI i s i′ → ∞ (MI S PI i′))) → P i (sup sf)) → {i : I} → (x : MI S PI i) → P i x
unsup f (sup x) = f x

\end{code}

%endif

\begin{code}

MIunfold :  ∀  {I} {X : I → Set} {S : I → Set} 
             {PI : (i : I) → S i → I → Set} →
             X -*-> obj* ⟦ S ◁* PI ⟧* X → X -*-> MI S PI 
MIunfold m i x with m i x
MIunfold m i x | s , f = sup (s , (λ i′ p → ♯ MIunfold m i′ (f i′ p)))

\end{code}

Here we employ Agda's approach to coprogramming (e.g. see
\cite{txa:mpc2010g}), where we mark (possibly) infinite subtrees with
|∞|, |♯ : A → ∞ A| and |♭ : ∞ A → A| pack and unpack infinite objects
respectively. {\bf explain. and why?} The paths to positions in and indexed |M| tree, are always finite -- in fact modulo the use of |♭|, this |Path| is the same as the definition for the initial algebra case.

\begin{code}

data Path  {I J : Set} (S : J → Set)  
           (PI  : (j : J) → S j → I  → Set) 
           (PJ  : (j : J) → S j → J  → Set) 
           : (j : J) → MI S PJ j → I → Set where
  path : ∀  {j s f i} →     
               PI j s i 
            ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path S PI PJ j′ (♭ (f j′ p)) i)) 
            → Path S PI PJ j (sup (s , f)) i 

\end{code}

Just as with parameterised initial algebras of indexed containers are
built from |WI|-types, so parameterised terminal coalgebras of indexed
containers is built from |WI|-types as follows.

\begin{code}

ν^C : {I J : Set} → ICont* (I ⊎ J) J → ICont* I J
ν^C {I} {J} (S ◁* P) = 
  let  PI  : (j : J) → S j → I  → Set ;  PI  j s i   = P $$ j $$ s $$ (inj₁ i) 
       PJ  : (j : J) → S j → J  → Set ;  PJ  j s j′  = P $$ j $$ s $$ (inj₂ j′)
  in   MI S PJ ◁* Path S PI PJ

\end{code}

%if style == newcode

\begin{code}

{-

\end{code}

%endif

\begin{code}

out^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → ν^C F ⇒* F ⟨ ν^C F ⟩C* 
out^C {I} {J} (S ◁* P) = (λ _ (sup x) → x) ◁* λ (sup x) i′ p → path p 

\end{code}

%if style == newcode

unsup {_} {_} {_} {λ j s → (i : J) → P j (proj₁ (sup⁻¹ s)) (inj₂ i) ⊎
      Σ I
      (λ i' →
         Σ (P j (proj₁ (sup⁻¹ s)) (inj₁ i'))
         (λ p →
            Path S (λ i0 s' i′ → P i0 s' (inj₁ i′))
            (λ i0 s' j' → P i0 s' (inj₂ j')) ? (proj₂ (sup⁻¹ s) i' p) i)) →
      Path S (λ i' s' i′ → P i' s' (inj₁ i′))
      (λ i' s' j' → P i' s' (inj₂ j')) j s i} (λ sf i′ p → path p)


\end{code}

%endif

\begin{code}

unfold^C : ∀  {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → 
              G ⇒* F ⟨ G ⟩C* → G ⇒* ν^C F
unfold^C {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = funfold ◁* runfold  
    where  PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = P i s (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = P i s (inj₂ j)
           funfold = MIunfold f
           runfold :  {i : I} (t : T i) 
                      (j : J) → Path S PI PJ i (funfold i t) j → Q i t j 
           runfold t j (path (inj₁ x)) = 
             r t j (inj₁ x)
           runfold t j (path (inj₂ (i , (p , q)))) = 
             r t j (inj₂ (i , p , runfold (proj₂ (f _ t) i p) j q))

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

{\bf There must be something more to say}

%endif

