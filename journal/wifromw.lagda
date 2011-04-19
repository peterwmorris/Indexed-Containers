
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
open import Relation.Binary.HeterogeneousEquality
open import Coinduction
open import Data.Nat hiding (_⊔_)
open import Relation.Nullary

open import common
open import tt

sup₁≡ : ∀  {S P} → {s s' : S} {f : P s → W S P} {f' : P s' → W S P} → 
           (sup s f) ≡ (sup s' f') → s ≡ s'
sup₁≡ refl = refl

sup₂≡ : ∀  {S P} → {s s' : S} {f : P s → W S P} {f' : P s' → W S P} → 
           (sup s f) ≡ (sup s' f') → f ≅ f'
sup₂≡ refl = refl


proj₁≡ : ∀  {l l'} {S : Set l} {T : S → Set l'} → {s s' : S} {t : T s} {t' : T s'} → 
            _≡_ {_} {Σ S T} (s , t) (s' , t') → s ≡ s'
proj₁≡ refl = refl 

\end{code}

%endif

%format proj₁≡ = proj₁ ≡

\subsubsection{|WI| from |W|}

How, then, can we build |WI| from |W|? The initial step is to create a type of \emph{pre}-|WI| trees, with nodes containing a shape \emph{and} its index, and branching over positions \emph{and their} indicies:

\begin{code}

WI′ : {I : Set} (S : I → Set) (P : (i : I) (s : S i) → I → Set) → Set
WI′ {I} S P = W (Σ I S) (split i & s tilps ↦ Σ I (P i s) !m !s)

\end{code}

Given such a tree we want to express the property that the subtrees of such a pre-tree have the correct index in their node information. In order to do this we need a second |W|-type, which is similar to |WWI′|, but with an extra copy of the index information stored in that node:

\begin{code}

WIl : {I : Set} (S : I → Set) (P : (i : I) (s : S i) → I → Set) → Set
WIl {I} S P = W (I × (Σ I S)) (split i′ & i & s tilps ↦ Σ I (P i s) !m !s)

\end{code}

There are two possible completions of this extra indexing information, either we push the indexes down to the subtrees, or we copy it from the sub-trees themselves:

%if style == newcode

\begin{code}

module label {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set} where

\end{code}

%endif

\begin{code}

  lup : WI′ S P → WIl S P 
  lup (sup (i , s) f) = sup (i , (i , s)) (λ p → lup (f p))

  ldown : I → WI′ S P → WIl S P 
  ldown i (sup s f) = sup (i , s) split i′ & p tilps ↦ ldown i′ (f (i′ , p)) !m !s

\end{code} 

%if style == newcode

\begin{code}

open label 

\end{code}

%endif

The property of a pre-tree being type correct can be stated as its two possible labellings being equal:

\begin{code}

WI : {I : Set} (S : I → Set) (P : (i : I) (s : S i) → I → Set) → I → Set
WI S P i = Σ (WI′ S P) λ x → lup {_} {S} {P} x ≡ ldown {_} {S} {P} i x 

\end{code}

%if style == newcode

\begin{code}

module supm {I : Set} {S : I → Set} {P : (i : I) (s : S i) → I → Set} where  

\end{code}

%endif

%format supi = sup

We rely on function extensionality to define the constructor |supi|:

\begin{code}
  open import ifunc
  open import icont

  supi : obj* ⟦ S ◁* P ⟧* (WI S P)  -**-> WI S P
  supi (s , f) =  (  sup (_ , s) (split i & p tilps ↦ proj₁ (f i p) !m !s)) 
                  ,  cong (sup (_ , _ , s)) (ext split i & p tilps ↦ proj₂ (f i p) !m !s)

\end{code}

The recursion principle inevitably then relies on the uniqueness of identity 
proofs. It's also the case that in its form below |wirec| does not pass Agda's termination checker. The direct encoding via |wrec| would avoid this problem, at the expense of being even more verbose:

\begin{code}

  wirec : {i : I} (x : WI S P i) (Q : {i : I} → WI S P i → Set)
          (m :  {i : I} (s : S i) (f : P i s -*-> WI S P)
                (h : {i′ : I} (p : P i s i′) → Q (f i′ p)) → Q {i} (supi (s , f)))
          → Q x
  wirec {i} (sup (i′ , s) f , ok) Q m with proj₁≡ (sup₁≡ ok)
  wirec {i} (sup (.i , s) f , ok) Q m | refl = 
    subst Q (cong {B = λ _ → WI S P i} (λ x → sup (i , s) f , x) UIP) 
      (m s (λ i p → f (i , p) , ext⁻¹ (sup₂≡ ok) (i , p)) 
           (λ {i′} p → wirec (f (i′ , p) , ext⁻¹ (sup₂≡ ok) (i′ , p)) Q m))

\end{code}

It's then straight forward but labourious to prove the $\beta$ law for |wirec|, which would have this type:

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

\begin{code}

Path :  {I J : Set} (S : I → Set)  
        (PI  : (i : I) → S i → I  → Set) 
        (PJ  : (i : I) → S i → J  → Set) 
        (i : I) → WI S PI i → J → Set 
Pathk {I} {J} {S} {PI} {PJ} i w = WI PathS PathP (i , w) 
  where PathS : Σ I (WI S PI) → Set
        PathS (i , sup (s , f)) = PJ i s j ⊎ Σ I (PI i s)
        PathP : (iw : Σ I (WI S PI)) (s : PathS iw) → Σ I (WI S PI) → Set
        PathP (i , sup (s , f)) (inj₁ p) (i′ , w′) = ⊥
        PathP (i , sup (s , f)) (inj₂ (i′′ , p)) (i′ , w′) = 
          (i′′ ≡ i′) × (f i′′ p ≅ w′)

path :  {I J : Set} {S : I → Set}  
        {PI  : (i : I) → S i → I  → Set} 
        {PJ  : (i : I) → S i → J  → Set} 
        {i : I} → {s : S i} {f : PI i s -*-> WI S PI} → {j : J} 
        →  PJ i s j  ⊎  (Σ I λ i′ → Σ (PI i s i′) λ p → Pathk S PI PJ i′ (f i′ p) j)        
        →  Pathk S PI PJ i (sup (s , f)) j 
pathk (inj₁ p) = sup (inj₁ p , λ i ())
pathk {I} {J} {S} {PI} {PJ} {i} {s} {f} {j} (inj₂ (i′′ , (q , r))) = sup ((inj₂ (i′′ , q)) , sub) 
  where sub : (iw : Σ I (WI S PI)) →
                 (i′′ ≡ proj₁ iw) × (f i′′ q ≅ proj₂ iw) → Pathk S PI PJ (proj₁ iw) (proj₂ iw) j 
        sub (i′ , w′) (eqi , eqw) = subst (WI _ _) (cong₂ _,_ eqi eqw) r 

\end{code}

