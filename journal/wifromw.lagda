
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module wifromw where

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

sup₁≡ : ∀  {S P} → {s s' : S} {f : P s → W S P} {f' : P s' → W S P} → 
           (sup (s , f)) ≡ (sup (s' , f')) → s ≡ s'
sup₁≡ refl = refl

sup₂≡ : ∀  {S P} → {s s' : S} {f : P s → W S P} {f' : P s' → W S P} → 
           (sup (s , f)) ≡ (sup (s' , f')) → f ≅ f'
sup₂≡ refl = refl


proj₁≡ : ∀  {l l'} {S : Set l} {T : S → Set l'} → {s s' : S} {t : T s} {t' : T s'} → 
            _≡_ {_} {Σ S T} (s , t) (s' , t') → s ≡ s'
proj₁≡ refl = refl 

\end{code}

%endif

So far we have developed a theory of indexed containers using a rich Type
Theory. We claimed in the introduction, however, that this theory required
only the presence of |W|-types. In this section we will outline the
translation of many of the definitions above into such a spartan theory.
First we will show how to obtain indexed |W|-types from un-indexed ones, and
by analogy |MI| from |M|, and then we will revisit a proof of how to derive
|M|-types from |W|.

%format proj₁≡ = proj₁ ≡

\subsection*{|WI| from |W|}
\label{wifromw}

How, then, can we build |WI| from |W|? The initial step is to create a type
of \emph{pre}-|WI| trees, with nodes containing a shape \emph{and} its index,
and branching over positions \emph{and their} indices:

\begin{code}

WI′ :  {I : Set} (S : I → Set) 
       (P : (i : I) (s : S i) → I → Set) → Set
WI′ {I} S P = W (Σ* i ∶ I *Σ S i) (split i & s tilps ↦ Σ* i′ ∶ I *Σ P i s i′ !m !s)

\end{code}

Given such a tree we want to express the property that the subtrees of such a pre-tree have the correct index in their node information. In order to do this we need a second |W|-type, which is similar to |WWI′|, but with an extra copy of the index information stored in that node:

\begin{code}

WIl :  {I : Set} (S : I → Set) 
       (P : (i : I) (s : S i) → I → Set) → Set
WIl {I} S P = W (I × (Σ* i ∶ I *Σ S i)) (split i′ & i & s tilps ↦ Σ* i′ ∶ I *Σ P i s i′ !m !s)

\end{code}

There are two possible completions of this extra indexing information, either we push the indexes down to the subtrees, or we copy it from the sub-trees themselves:

%if style == newcode

\begin{code}

module label {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set} where

\end{code}

%endif

\begin{code}

  lup : WI′ S P → WIl S P 
  lup (sup ((i , s) , f)) = sup ((i , (i , s)) , (λ p → lup (f p)))

  ldown : I → WI′ S P → WIl S P 
  ldown i (sup (s , f)) = sup ((i , s) , split i′ & p tilps ↦ ldown i′ (f (i′ , p)) !m !s)

\end{code} 

%if style == newcode

\begin{code}

open label 

\end{code}

%endif

The property of a pre-tree being type correct can be stated as its two possible labellings being equal:

\begin{code}

WI :  {I : Set} (S : I → Set) 
      (P : (i : I) (s : S i) → I → Set) → I → Set
WI S P i = Σ (WI′ S P) λ x → lup {_} {S} {P} x ≡ ldown {_} {S} {P} i x 

\end{code}

%if style == newcode

\begin{code}

module supm {I : Set} {S : I → Set} {P : (i : I) (s : S i) → I → Set} where  

\end{code}

%endif

%format supi = sup

We rely on function extensionality to define the constructor |supi|:

%if style == newcode

\begin{code}

  open import ifunc
  open import icont

\end{code}

%endif

\begin{code}

  supi : obj* ⟦ S ◁* P ⟧* (WI S P)  -**-> WI S P
  supi (s , f) =  (  sup ((_ , s) , split i & p tilps ↦ proj₁ (f i p) !m !s)) 
                  ,  cong (λ x → sup ((_ , _ , s) , x)) (ext split i & p tilps ↦ proj₂ (f i p) !m !s)

\end{code}

The recursion principle then relies on the uniqueness of identity 
proofs. It's also the case that in its form below |wirec| does not pass Agda's termination checker. The direct encoding via |wrec| would avoid this problem, at the expense of being even more verbose:

\begin{code}

  wirec : {i : I} (x : WI S P i) (Q : {i : I} → WI S P i → Set)
          (m :  {i : I} (s : S i) (f : P i s -*-> WI S P)
                (h : {i′ : I} (p : P i s i′) → Q (f i′ p)) → Q {i} (supi (s , f)))
          → Q x
  wirec {i} (sup ((i′ , s) , f) , ok) Q m with proj₁≡ (sup₁≡ ok)
  wirec {i} (sup ((.i , s) , f) , ok) Q m | refl = 
    subst Q (cong {B = λ _ → WI S P i} (λ x → sup ((i , s) , f) , x) UIP) 
      (m s (λ i p → f (i , p) , ext⁻¹ (sup₂≡ ok) (i , p)) 
           (λ {i′} p → wirec (f (i′ , p) , ext⁻¹ (sup₂≡ ok) (i′ , p)) Q m))

\end{code}

It's then straight forward but labourious to prove the $\beta$ law for |wirec|, which would has type:

%if style == newcode

\begin{code}

{-

\end{code}

%endif

%format βwirec = "\beta" wirec

\begin{code}

  βwirec :  
           {i : I} (s : S i) (f : P i s -*-> WI I S P) 
           (Q : {i : I} → WI I S P i → Set)
           (m :  {i : I} (s : S i) (f : {i′ : I} → P i s i′ → WI I S P i′)
                 (h : {i′ : I} (p : P i s i′) → Q (f p)) → Q {i} (supi s f))
           → wirec {i} (supi {I} {S} {P} s f) Q m ≡ m {i} s f (λ {i′} p → wirec (f p) Q m)

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif

We can use this proof that |WI|-types can be encoded by |W| to explain where 
|Path| fits in, since it is straight forwardly encoded as a |WI|:

%if style == newcode

\begin{code}

{-

\end{code}

%endif

\begin{code}

Path :  {I J : Set} (S : J → Set)  
        (PI  : (j : J) → S j → I  → Set) 
        (PJ  : (j : J) → S j → J  → Set) 
        (j : J) → WI S PJ j → I → Set 
Path {I} {J} S PI PJ j w i = WI PathS PathP (j , w) 
  where PathS : Σ* j ∶ J *Σ WI S PJ j → Set
        PathS (j , sup (s , f)) = PI j s i ⊎ Σ J (PJ j s)
        PathP : (jw : Σ* j ∶ J *Σ WI S PJ j) (s : PathS jw) → Σ* j ∶ J *Σ WI S PJ j → Set
        PathP (j , sup (s , f)) (inj₁ p) (j′ , w′) = ⊥
        PathP (j , sup (s , f)) (inj₂ (j′′ , p)) (j′ , w′) = 
          (j′′ ≡ j′) × (f j′′ p ≅ w′)

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif

