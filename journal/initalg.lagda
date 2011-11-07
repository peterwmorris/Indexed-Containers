
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module initalg where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Product as Prod
open import Function
open import Relation.Binary.HeterogeneousEquality
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
\label{sec:initalg}

We will now examine how to construct the parameterised initial algebra
of an indexed container of the form |F : ICont* (I ⊎ J) J|. The shapes of such
a container are an |J|-indexed family of |Set|s and the positions are
indexed by |I ⊎ J|; we will treat these position as two separate
entities, those positions indexed by |I| -- the recursive positions --
and those by |J| -- the payload positions.

The shapes of initial algebra we are constructing will be trees with S
shapes at the nodes and which branch over the recursive |PI|
positions. We call these trees \emph{indexed} |W|-types, denoted |WI|,
and they are the initial algebra of the functor |⟦ S ◁ PJ ⟧*|. In
Agda, we can implement the |WI| constructor and its associated 
iteration operator |WIfold| as follows:

\begin{code}

data WI  {J : Set} (S : J → Set) 
         (PJ : (j : J) → S j → J → Set) : J → Set where
  sup : obj* ⟦ S ◁* PJ ⟧* (WI S PJ)  -**-> WI S PJ 


WIfold :  ∀  {J} {X : J → Set} {S : J → Set} 
             {PJ : (j : J) → S j → J → Set} →
             obj* ⟦ S ◁* PJ ⟧* X -*-> X → WI S PJ -*-> X
WIfold f j (sup (s , g)) = f j (s , λ j′ p → WIfold f j′ (g j′ p))

\end{code}


\noindent This mirrors the construction for plain containers, where we
can view ordinary |W|-types as the initial algebra of a container
functor.  Positions in an indexed |W|-type are given by the paths through
such a tree which terminate in a non-recursive |PI|-position:

\begin{code}

data Path  {I J : Set} (S : J → Set)  
           (PI  : (j : J) → S j → I  → Set) 
           (PJ  : (j : J) → S j → J  → Set) 
           : (j : J) → WI S PJ j → I → Set where
  path : ∀  {j s f i} →     
               PI j s i 
            ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path S PI PJ j′ (f j′ p) i)) 
            → Path S PI PJ j (sup (s , f)) i 

\end{code}

%if style == newcode

\begin{code}

pathminusone :  {I J : Set} {S : J → Set}  
                {PI  : (j : J) → S j → I  → Set} 
                {PJ  : (j : J) → S j → J  → Set} 
                → {j : J} → {s : S j} {f : PJ j s -*-> WI S PJ} → {i : I} → Path S PI PJ j (sup (s , f)) i →
           PI j s i  ⊎  (Σ J λ j′ → Σ (PJ j s j′) λ p → Path S PI PJ j′ (f j′ p) i)
pathminusone (path p) = p

\end{code}

%endif

%format pathminusone = path minusone

\noindent Again this mirrors the partial application construction
where positions were given by a |PJ| position at the top level, or a
pair of a |PJ| position and a sub |Q| position. Here the |Q| positions
are recursive |Path| positions. This reflects the fact that a
|WI|-type can be thought of as iterated partial application.  {\bf
indentation and line spacing} We can now use |WI|-types, or
equivalently initial algebras of indexed contianers, to construct the
parametrised initial algebra of an indexed container. Firstly we
construct the carrier {\bf defined} of the parameterised initial algebra:

%format μ = "\mu"
%format μ^C = μ ^C


\begin{code}

μ^C : {I J : Set} → ICont* (I ⊎ J) J → ICont* I J
μ^C {I} {J} (S ◁* P) = 
  let  PI  : (j : J) → S j → I  → Set ;  PI  j s i   = P $$ j $$ s $$ (inj₁ i) 
       PJ  : (j : J) → S j → J  → Set ;  PJ  j s j′  = P $$ j $$ s $$ (inj₂ j′)
  in   WI S PJ ◁* Path S PI PJ
\end{code}

%format in^C = "\Varid{in}" ^C
%format fold^C = fold ^C
%format unfold^C = unfold ^C

\noindent Next, we note that the structure map {\bf defined} for this
parameterised initial algebra is a container morphism from the partial
application of |F| and its parametrised initial algebra, to the
parameterised initial algebra. This structure map is given by the
constructor |sup| of |WI| and the constructor |path| of |Path|:

%if style == newcode

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F = (λ _ → sup) ◁* λ _ _ p → pathminusone p 

{-

\end{code}

%endif

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F = (λ _ → sup) ◁* λ _ _ (path p) → p 

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif

That we have a parameterised initial algebra follows from the
definition of the associated iteration operator which we now present.

\begin{code}

fold^C : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) → 
            F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = ffold ◁* rfold 
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i   = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′  = P j s (inj₂ j′)
           ffold = WIfold f
           rfold :  {j : J} (s : WI S PJ j) 
                    (i : I) → Q j (ffold j s) i → Path S PI PJ j s i
           rfold (sup (s , f)) i p  with r (s , _) i p
           rfold (sup (s , f)) i p  | inj₁ x               = 
             path (inj₁ x)
           rfold (sup (s , f)) i p  | inj₂ (j′ , (q , y))  =
             path (inj₂ (j′ , (q , rfold (f j′ q) i y)))


\end{code} {\bf Do we need some kind of proof of initiality, either
for mu C or |WI|. Do we have a notion of parameterised algebra or is
it translated to algebra of F[]. See cotianers for reference point.
}

%if style == newcode

\begin{code}


module Pathkk {I J : Set} (S : J → Set)  
        (PI  : (j : J) → S j → I  → Set) 
        (PJ  : (j : J) → S j → J  → Set) (i : I) where


  PathS : Σ J (WI S PJ) → Set
  PathS (j , sup (s , f)) = PI j s i ⊎ Σ J (PJ j s)
  PathP : (iw : Σ J (WI S PJ)) (s : PathS iw) → Σ J (WI S PJ) → Set
  PathP (j , sup (s , f)) (inj₁ p) (j′ , w′) = ⊥
  PathP (j , sup (s , f)) (inj₂ (j′′ , p)) (j′ , w′) = 
          (j′′ ≡ j′) × (f j′′ p ≅ w′)

  Pathk : (j : J) → WI S PJ j → Set 
  Pathk j w = WI PathS PathP (j , w) 

open Pathkk

{-

pathk : {I J : Set} {S : J → Set}  
           {PI  : (j : J) → S j → I  → Set} 
           {PJ  : (j : J) → S j → J  → Set} 
           → {j : J} → {s : S j} {f : PJ j s -*-> WI S PJ} → {i : I} → 
           PI j s i  ⊎  (Σ J λ j′ → Σ (PJ j s j′) λ p → Pathk S PI PJ i j′ (f j′ p))        → Pathk S PI PJ i j (sup (s , f)) 
pathk (inj₁ p) = sup (inj₁ p , λ j ())
pathk {I} {J} {S} {PI} {PJ} {j} {s} {f} {i} (inj₂ (j′′ , (q , r))) = sup ((inj₂ (j′′ , q)) , sub) 
  where sub : (jw : Σ J (WI S PJ)) →
                 (j′′ ≡ proj₁ jw) × (f j′′ q ≅ proj₂ jw) → Pathk S PI PJ i (proj₁ jw) (proj₂ jw) 
        sub (j′ , w′) (eqj , eqw) = subst (WI _ _) (cong₂ _,_ eqj eqw) r 

-}

\end{code}

%endif
