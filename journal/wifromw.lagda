
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
open import ifunc
open import icont

sup⁻¹ : ∀  {S P} → W S P → Σ S λ s → P s → W S P
sup⁻¹ (sup x) = x


\end{code}

%endif

So far we have developed a theory of indexed containers using a rich
Type Theory with features such as |WI|- and |MI|-types. We claimed in
the introduction, however, that the theory of indexed containers could
be developed even when one only has |W|-types. In this section we will
outline the translation of many of the definitions above into such a
spartan theory.  First we will show how to obtain indexed |WI|-types
from |W|-types, and by analogy |MI|-types from |M|-types, and then we
will revisit our proof of how to derive |M|-types from |W|-types.

%format proj₁≡ = proj₁ ≡

\subsection*{|WI| from |W|}
\label{wifromw}

How, then, can we build |WI|-types from |W|-typs? The initial step is
to create a type of \emph{pre}-|WI| trees, with nodes containing a
shape \emph{and} its index, and branching over positions \emph{and
their} indices:

\begin{code}

WI′ :  {I : Set} (S : I → Set) 
       (P : (i : I) (s : S i) → I → Set) → Set
WI′ {I} S P = W (Σ* i ∶ I *Σ S i) (λ { (i , s) → Σ* i′ ∶ I *Σ P i s i′})

\end{code}

Given such a tree we want to express the property that the subtrees of
such a pre-tree have the correct index in their node information. In
order to do this we need a second |W|-type, which is similar to
|WI′|, but with an extra copy of the index information stored in that
node:

\begin{code}

WIl :  {I : Set} (S : I → Set) 
       (P : (i : I) (s : S i) → I → Set) → Set
WIl {I} S P = W  (I × (Σ* i ∶ I *Σ S i)) 
                 (λ { (i′ , i , s) → Σ* i′ ∶ I *Σ P i s i′})

\end{code}

There are two canonical ways to turn an element of |WI' S P| into an
element of |WIl S P|, both of which involve filling in this extra indexing
information: i) we can simply copy the index already stored at the node;
or ii) we can push the indexes down from parent nodes to
child nodes:

%if style == newcode

\begin{code}

module label {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set} where

\end{code}

%endif

\begin{code}

  lup : WI′ S P → WIl S P 
  lup (sup ((i , s) , f)) = sup ((i , (i , s)) , (λ p → lup (f p)))

  ldown : I → WI′ S P → WIl S P 
  ldown i (sup (s , f)) = sup ((i , s) , λ { (i′ , p) → ldown i′ (f (i′ , p)) })

\end{code} 

%if style == newcode

\begin{code}

open label 

\end{code}

%endif

The property of a pre-tree being type correct can be stated as its two
possible labellings being equal. That is we can use |W|-types to
define the |WI|-type as follows:

\begin{code}

WI :  {I : Set} (S : I → Set) 
      (P : (i : I) (s : S i) → I → Set) → I → Set
WI S P i = 
  Σ* x ∶ (WI′ S P) *Σ 
   lup {_} {S} {P} x ≡ ldown {_} {S} {P} i x

\end{code}



%format supi = sup

Having built the |WI|-type from the |W|-type, we must next build the
constructor |supi| which makes elements of |WI|-types. We rely on
function extensionality to define the constructor |supi|:

\begin{code}

supi : ∀ {J S PJ} → obj* ⟦ S ◁* PJ ⟧* (WI {J} S PJ)  -*-> WI S PJ
supi {J} {S} {PJ} j (s , f) =  
  (  sup ((_ , s) , λ { (j , p) → proj₁ (f j p) })) 
  ,  cong (λ x → sup ((j , j , s) , x)) (λ≡ ip →≡ proj₂ (f _ (proj₂ ip)))

\end{code}

\begin{proposition}
|(WI S PJ , supi)| is the initial object in the category of |⟦ S ◁* PJ ⟧|-algebras.
\end{proposition}

\begin{proof}

We must once again show that for any |⟦ S ◁* PJ ⟧|-algebra |(X , α)| where |α : obj*  ⟦ S ◁* PJ ⟧* X -*-> X| there is a unique mediating morphism |WIfold : WI S PJ -*-> X|. It is simple enough to define |WIfold|:

\begin{code}

WIfold : ∀        {J} {S X  : J → Set} {PJ} →
            obj*  ⟦ S ◁* PJ ⟧* X -*-> X ->
                  WI S PJ -*-> X
WIfold α j (sup ((j′ , s) , f) , ok) with cong (proj₁ ∘ proj₁ ∘ sup⁻¹) ok
WIfold α j (sup ((.j , s) , f) , ok) | refl =  
 α j (s , (λ j′ p → WIfold α j′ (f (j′ , p) , ext⁻¹ (cong (proj₂ ∘ sup⁻¹) ok) (j′ , p))))

\end{code}

\noindent
In the form below |WIfold| does not pass Agda's termination checker; The direct encoding via |Wfold| would avoid this problem, at the expense of being even more verbose.

To show that |WIfold| makes the initial algebra diagram commute, we must employ the |UIP| principle, that any two proofs of an equality are equal:

%format βwirec = "\beta" wirec

\begin{code}

WIcomm : ∀  {J} {S X : J → Set} {PJ} 
            (α : obj*  ⟦ S ◁* PJ ⟧* X -*-> X)
            (j : J) → (x : obj* ⟦ S ◁* PJ ⟧* (WI S PJ) j) →
            WIfold α j (supi {J} {S} {PJ} j x) ≡ 
             α j (mor* ⟦ S ◁* PJ ⟧* (WIfold α) j x)  
WIcomm α j (s , f) with 
         (cong (proj₁ ∘ proj₁ ∘ sup⁻¹)
          (cong (λ x → sup ((j , j , s) , x))
           (λ≡ ip →≡ proj₂ (f (proj₁ ip) (proj₂ ip)))))
WIcomm α j (s , f) | refl = 
  cong (λ g → α j (s , g)) 
   (λ≡ j′ →≡ λ≡ p →≡ 
    cong (λ eq → WIfold α j′ (proj₁ (f j′ p) , eq)) UIP≡)

\end{code}

We can also show that the fold is unique:

\begin{code}

WIfoldUniq′ : ∀  {J} {X : J → Set} {S : J → Set} 
                 {PJ : (j : J) → S j → J → Set} 
                 (α : obj* ⟦ S ◁* PJ ⟧* X -*-> X) 
                 (β : WI S PJ -*-> X) → 
                 (β ⊚ supi) ≡ (α ⊚ mor* ⟦ S ◁* PJ ⟧* β) →
                 (j : J) (x : WI S PJ j) → β j x ≡ WIfold α j x
WIfoldUniq′ α β commβ j (sup ((j′ , s) , f) , ok) 
  with cong (proj₁ ∘ proj₁ ∘ sup⁻¹) ok
WIfoldUniq′ α β commβ j (sup ((.j , s) , f) , ok) | refl =  begin 
    β j (sup ((j , s) , f) , ok)
  ≅⟨ cong (λ ok′ → β j (sup ((j , s) , f) , ok′)) UIP≡  ⟩
    β j  (  sup ((j , s) , f) 
         ,  cong (λ p → sup ((j , j , s) , p))
             (ext (ext⁻¹ (cong (proj₂ ∘ sup⁻¹) ok))))
  ≅⟨ ext⁻¹ (ext⁻¹ commβ j) (s , _) ⟩ 
    α j  (s, λ j p → β j  (  f (j , p) 
                          ,  ext⁻¹ (cong (proj₂ ∘ sup⁻¹) ok) (j , p))) 
  ≅⟨ (cong   (λ n → α j (s , n)) 
             (λ≡ j →≡ λ≡ p →≡ 
               WIfoldUniq′ α β commβ j 
                (f (j , p) , ext⁻¹ (cong (proj₂ ∘ sup⁻¹) ok) (j , p)))) ⟩ 
    α j  (s, λ j p → WIfold α j  (  f (j , p) 
                                 , ext⁻¹ (cong (proj₂ ∘ sup⁻¹) ok) (j , p))) 
  ∎  
 where open ≅-Reasoning
\end{code}

\end{proof}

\noindent
We can use this proof that |WI|-types can be encoded by |W| to explain
where |Path| fits in, since it is straight forwardly encoded as a
|WI|: 

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
  where  PathS : Σ* j ∶ J *Σ WI S PJ j → Set
         PathS (j , sup (s , f)) = PI j s i ⊎ Σ J (PJ j s)
         PathP :  (jw : Σ* j ∶ J *Σ WI S PJ j) (s : PathS jw) →
                  Σ* j ∶ J *Σ WI S PJ j → Set
         PathP (j , sup (s , f)) (inj₁ p) (j′ , w′) = ⊥
         PathP (j , sup (s , f)) (inj₂ (j′′ , p)) (j′ , w′) = 
           (j′′ ≡ j′) × (f j′′ p ≅ w′)

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif
The reader will be unsuprised to learn that a similar construction to
the above allows us to derive |MI|-types from |M|-types. The details are, once again, somewhat obfiscated by the experimental treatment of co-induction in Agda, but are in the spirit of the dual of the proof above.
