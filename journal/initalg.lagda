
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module initalg where

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

\section{Initial Algebras of Indexed Containers}

We will now examine how to construct the initial algebra of a container of the form |F : ICont* (I ⊎ J) I|. The shapes of such a container are an |I|-indexed family of |Set|s and the positions are in |(i : I) → S i → I ⊎ J → Set|; we will treat these position as two separate entities, those positions indexed by |I| (|PI : (i : I) → S i → I → Set|) -- the recusive positions -- and those by |J| 
(|PJ : (i : I) → S i → J → Set|) -- the payload positions.

The shapes of initial algebra we are constructing will be trees with S shapes at the nodes and which branch over the recursive |PI| positions. We call these trees \emph{indexed} |W|-types, denoted |WI| and they are the initial algebra of the functor |⟦ S ◁ PI ⟧*|:

\begin{code}

data WI  {I : Set} (S : I → Set) 
         (PI : (i : I) → S i → I → Set) : I → Set where
  sup : obj* ⟦ S ◁* PI ⟧* (WI S PI)  -**-> WI S PI 

WIfold :  ∀  {I} {X : I → Set} {S : I → Set} 
             {PI : (i : I) → S i → I → Set} →
             obj* ⟦ S ◁* PI ⟧* X -*-> X → WI S PI -*-> X
WIfold f i (sup (s , g)) = f i (s , λ i′ p → WIfold f i′ (g i′ p))

\end{code}


\noindent
This mirrors the construction for plain containers, where we can view ordinary |W| types as the initial algebra of a container functor.

Positions are given by paths through such a tree, terminated by a non-recursive |PJ|:

\begin{code}

data Path  {I J : Set} (S : I → Set)  
           (PI  : (i : I) → S i → I  → Set) 
           (PJ  : (i : I) → S i → J  → Set) 
           : (i : I) → WI S PI i → J → Set where
  path : ∀  {i s f j} →     
               PJ i s j 
            ⊎  (Σ I λ i′ → Σ (PI i s i′) λ p → Path S PI PJ i′ (f i′ p) j) 
            → Path S PI PJ i (sup (s , f)) j 

\end{code}

%if style == newcode

\begin{code}

pathminusone : {I J : Set} {S : I → Set}  
           {PI  : (i : I) → S i → I  → Set} 
           {PJ  : (i : I) → S i → J  → Set} 
           → {i : I} → {s : S i} {f : PI i s -*-> WI S PI} → {j : J} → Path S PI PJ i (sup (s , f)) j →
           PJ i s j  ⊎  (Σ I λ i′ → Σ (PI i s i′) λ p → Path S PI PJ i′ (f i′ p) j)
pathminusone (path p) = p

\end{code}

%endif

%format pathminusone = path minusone

\noindent
Again this mirrors the partial application construction where positions were 
given by a |PJ| position at the top level, or a pair of a |PJ| position and a 
sub |Q| position. Here the |Q| positions are recursive |Path| positions. 

%format μ = "\mu"
%format μ^C = μ ^C

\noindent
We can now give the object part of the patrametrized initial algebra of a container, given by:

\begin{code}

μ^C : {I J : Set} → ICont* (I ⊎ J) I → ICont* J I
μ^C {I} {J} (S ◁* P) = 
  let  PI  : (i : I) → S i → I  → Set ;  PI  i s i′  = P $$ i $$ s $$ (inj₁ i′) 
       PJ  : (i : I) → S i → J  → Set ;  PJ  i s j   = P $$ i $$ s $$ (inj₂ j)
  in   WI S PI ◁* Path S PI PJ
\end{code}

%format in^C = "\Varid{in}" ^C
%format fold^C = fold ^C
%format unfold^C = unfold ^C

\noindent
The algebra map is a container morphism from the partial aplication of |F| and its parametrised initial algebra, to the initial algebra, given by the algebra map of |WI| (|sup|) and our mediation funtion |path|:

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) I) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F = (λ _ → sup) ◁* λ _ _ p → pathminusone p 

\end{code}

\begin{code}

fold^C : ∀  {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → 
            F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = ffold ◁* rfold 
    where  PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = P i s (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = P i s (inj₂ j)
           ffold = WIfold f
           rfold :  {i : I} (s : WI S PI i) (j : J) → Q i (ffold i s) j → Path S PI PJ i s j
           rfold (sup (s , f)) j p  with r (s , _) j p
           rfold (sup (s , f)) j p  | inj₁ x               = path (inj₁ x)
           rfold (sup (s , f)) j p  | inj₂ (i′ , (q , y))  = path (inj₂ (i′ , (q , rfold (f i′ q) j y)))

\end{code}
