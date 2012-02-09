
%if style==code

\begin{code}

{-# OPTIONS --universe-polymorphism #-}

module termcoalg where

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

sup' : ∀ {I S PI} → obj* ⟦ S ◁* PI ⟧* (MI {I} S PI)  -**-> MI S PI 
sup' (s , f) = sup (s , (λ i x → ♯ (f i x)))

\end{code}

%endif

\noindent
Here, we employ Agda's approach to coprogramming (e.g. see
\cite{txa:mpc2010g}), where we mark (possibly) infinite subtrees with
|∞|. The type |∞ A| as a suspended computation of type |A|. |♯ : A → ∞ A| delays
a value of type |A| and |♭ : ∞ A → A| forces a computation. A simple syntactic 
test then ensures that co-recursive programs 
total --- recursive calls must be immediately {\em guarded} by a |♯| 
constructor. This technology is 
currently at an experimental stage.

The equality between infinite objects will be bi-simulation, for instance |MI|, 
types are bi-similar if they have the same node shape, and all their sub-trees 
are bi-similar:

%format _≈MI_ = _ ≈MI _
%format ≈MI = "\approx^{" MI "}" 

\begin{code}

data _≈MI_ {J S PJ} {j : J} : (x y : MI S PJ j) → Set where
  sup : ∀ {s f g} → (∀  {j′} (p : PJ j s j′) → 
                        ∞  (♭ (f j′ p)  ≈MI  ♭ (g j′ p))) → 
                           sup (s , f)  ≈MI  sup (s , g)

\end{code}

It is simple to show that this bi-simulation is an equivalence relation. 

%if style==code

\begin{code}

≈MIrefl : ∀ {J S PJ} {j : J} {x : MI S PJ j} → x ≈MI x
≈MIrefl {x = sup (s , f)} = sup (λ p → ♯ ≈MIrefl)

≈MIsym : ∀ {J S PJ} {j : J} {x y : MI S PJ j} → x ≈MI y → y ≈MI x
≈MIsym (sup pr) = sup (λ p → ♯ (≈MIsym (♭ (pr p))))

≈MItrans : ∀ {J S PJ} {j : J} {x y z : MI S PJ j} → 
             x ≈MI y → y ≈MI z → x ≈MI z
≈MItrans (sup pr) (sup qr) = sup (λ p → ♯ (≈MItrans (♭ (pr p)) (♭ (qr p)))) 

\end{code}

%endif

\begin{proposition} 
|(MI S PJ , sup⁻¹)| is the terminal object in the category of 
|⟦ S ◁* PJ ⟧|-coalgebras.
\end{proposition}

We must construct a co-iteration operator |MIunfold|, a morphism in the category 
of |⟦ S ◁* PJ ⟧|-coalgebras from our candidate teminal coalgebra to any other 
coalgebra. Such that the following diagram commutes:

\[
\xymatrix{
\mbox{|X|}
\ar[rr]^{\mbox{|α|\quad\quad}}
\ar[d]_{\mbox{|MIunfold α|}} & \quad\;\; &
\mbox{|obj* ⟦ S ◁* PJ ⟧* X|}
\ar[d]^{\mbox{|mor*  ⟦ S ◁* PJ ⟧* (MIunfold α)|}}
\\
\mbox{|MI S PJ|}
\ar@@<1ex>[rr]^{\mbox{|sup⁻¹|\quad\;\;}}
& &
\mbox{|obj* ⟦ S ◁* PJ ⟧* (MI S PJ)|} 
\ar@@<1ex>[ll]^{\mbox{|sup|\phantom{|⁻¹|}\quad\;\;}}
}
\]

\noindent
The following definition of |MIunfold| should obviously make the diagram commute
up-to bisimulation.

\begin{code}

MIunfold :  ∀  {J S PJ} {X : J → Set} →
             X -*-> obj* ⟦ S ◁* PJ ⟧* X → X -*-> MI S PJ 
MIunfold α j x with α j x
MIunfold α j x | s , f = sup (s , λ j′ p → ♯ MIunfold α j′ (f j′ p))

\end{code}

We also require that |MIunfold| is unique, {\em i.e.} any morphism that makes the diagram above should be provably equal (again upto bi-simulation) to |MIunfold α|. This seems to be easy to show:

%format sup' = sup

%if style == code

\begin{code}

{-

\end{code}

%endif

\begin{code}

MIunfolduniq : ∀ {J} {X : J → Set} {S PJ} 
                 (α : X -*-> obj* ⟦ S ◁* PJ ⟧* X) → (β : X -*-> MI {J} S PJ) →
                 ((j : J) (x : X j) → sup' ((mor* ⟦ S ◁* PJ ⟧* β ⊚ α) j x) ≈MI β j x) → 
                 (j : J) → (x : X j) → MIunfold α j x ≈MI β j x
MIunfolduniq α β commβ i x with commβ i x 
MIunfolduniq α β commβ i x | commix with β i x 
MIunfolduniq α β commβ i x  | sup {._} {._} {g} y 
                            | sup .(proj₁ (α i x) , g) = 
  sup (λ p → ♯ ≈MItrans (MIunfolduniq α β commβ _ _) (♭ (y p)))

\end{code}

However, Agda rejects this definition due to the recursive call not being guarded immediately by the |♯|, instead it is also under the appeal to the transitivity of bi-simulation. We can persuade the system this is ok my fusing the definition of |≈MItrans| with this one in a cumbersome but straight forward way, for details see the source of this paper.

%if style == code

\begin{code}

-}

Munfolddiag : ∀ {I} {X : I → Set} S PI (α : X -*-> obj* ⟦ S ◁* PI ⟧* X) → (β : X -*-> MI {I} S PI) → Set
Munfolddiag {I} {X} S PI α β = 
  (i : I) (x : X i) → (sup' ((mor* ⟦ S ◁* PI ⟧* β ⊚ α) i x)) ≈MI (β i x)


Munfolduniq' : ∀ {I} {X : I → Set} {S PI} 
                (α : X -*-> obj* ⟦ S ◁* PI ⟧* X) → (β : X -*-> MI {I} S PI) →
                Munfolddiag S PI α β → (i : I) → {t : MI S PI i} → (x : X i) →
                (β i x) ≈MI t → (MIunfold α i x) ≈MI t
Munfolduniq' α β comm i x bb with comm i x
Munfolduniq' α β comm i x bb | commix with β i x 
Munfolduniq' α β comm i x (sup bb) | sup {._} {._} {g} y | sup .(proj₁ (α i x) , g) = 
  sup (λ p → ♯ (Munfolduniq' α β comm _ (proj₂ (α i x) _ _) (≈MItrans (♭ (y p)) (♭ (bb p)))))

Munfolduniq : ∀ {I} {X : I → Set} {S PI} 
                (α : X -*-> obj* ⟦ S ◁* PI ⟧* X) → (β : X -*-> MI {I} S PI) →
                Munfolddiag S PI α β → (i : I) → (x : X i) →
                (MIunfold α i x) ≈MI (β i x)
Munfolduniq α β comm i x = Munfolduniq' α β comm i x ≈MIrefl

\end{code}

%endif


\noindent
The paths to positions in an indexed |M| tree, are always 
finite -- in fact modulo the use of |♭|, this |Path| is the same as the 
definition for the initial algebra case.

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

\begin{code}

out^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → ν^C F ⇒* F ⟨ ν^C F ⟩C* 
out^C {I} {J} (S ◁* P) = 
      (  λ {_ (sup (s , f)) → (s , (λ j p → ♭ (f j p)))})
  ◁*     λ {(sup x) i′ p → path p} 

\end{code}

%if style == newcode

\begin{code}


path⁻¹ : ∀  {I J S PI PJ j s f i} → Path S PI PJ j (sup (s , f)) i →
              PI j s i 
           ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path {I} {J} S PI PJ j′ (♭ (f j′ p)) i)) 
path⁻¹ (path (inj₁ x)) = inj₁ x
path⁻¹ (path (inj₂ y)) = inj₂ y 



in^C' :  ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ ν^C F ⟩C* ⇒* ν^C F 
in^C' {I} {J} (S ◁* P) = (λ {_ (s , f) → sup (s , λ i x → ♯ (f i x))}) ◁* λ _ _ → path⁻¹ 

\end{code}

%endif

\begin{proposition}
|(ν^C F . out^C F)| is terminal in the category of parametrized |F|-coalgebras of indexed containers. Further, by full and faithfulness, |(⟦ ν^C F ⟧* , ⟦ out^C F ⟧⇒*)| will also be terminal in the indexed functor case.
\end{proposition}

Mirroring the initial algebras, the coiteration for this terminal co-algebra employs the coiteration of |MI| for the shape maps. The position map takes a |Path| and builds a |Q| position by applying the position map from the coalgebra at every step in the path --- note that this position map is {\em inductive} in its path argument.

\begin{code}

unfold^C : ∀  {I J} (F : ICont* (I ⊎ J) J) {G : ICont* I J} → 
              G ⇒* F ⟨ G ⟩C* → G ⇒* ν^C F
unfold^C {I} {J} (S ◁* P) {T ◁* Q} (f ◁* r) = funfold ◁* runfold  
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i    = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′   = P j s (inj₂ j′)
           funfold = MIunfold f
           runfold :  {j : J} (t : T j) 
                      (i : I) → Path S PI PJ j (funfold j t) i → Q j t i 
           runfold t i (path (inj₁ x)) = 
             r t i (inj₁ x)
           runfold t i (path (inj₂ (j , (p , q)))) = 
             r t i (inj₂ (j , p , runfold (proj₂ (f _ t) j p) i q))

\end{code}

We must then show that |unfold^C| is the unique morphism that makes the following diagram commmute:

\[
\xymatrix{
\mbox{|G|}
\ar[d]_{\mbox{|F ⟨ (unfold^C F α) ⟩M*|}}\ar[rr]^{\mbox{|α|\quad}}
& &\mbox{|F ⟨ G ⟩C*|}\ar[d]^{\mbox{|unfold^C F α|}}
\\
\mbox{|ν^C F|} \ar[rr]^{\mbox{|out^C F|\quad}}
& 
\quad&
\mbox{|F ⟨ ν^C F ⟩C*|}  }
\]

\noindent
In order to show this in Agda, we are going to have to assume a second extensionality principle, namely that if two |MI| trees are bi-similar, then they are in fact equal:

\begin{code}

postulate MIext : ∀ {J S PJ} {j : J} {x y : MI S PJ j} → x ≈MI y → x ≅ y

\end{code}

\noindent
The inverse of this princple is obviously true:

\begin{code}

MIext⁻¹ : ∀ {J S PJ} {j : J} {x y : MI S PJ j} → x ≅ y → x ≈MI y
MIext⁻¹ refl = ≈MIrefl

\end{code}

\noindent
It is reasonable to assume that any language with fully fledged support for co-inductive types {\em and} extensional equality would admit such an axiom.

We can now show that unfold indeed makes the diagram above commute:

\begin{code}

unfoldComm : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
                (α : G ⇒* F ⟨ G ⟩C*) →
                (comp^C* (out^C F) (unfold^C F α)) ≡
                  (comp^C* (F ⟨ (unfold^C F α) ⟩CM*) α)       
unfoldComm (S ◁* P) (f ◁* r) = {!!}

\end{code}