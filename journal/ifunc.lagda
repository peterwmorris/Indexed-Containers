
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module ifunc where

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

\end{code}

%endif

\section{Indexed Functors}
\label{sec:ifunc}

%format IFunc.obj = "\!"
%format IFunc.mor = "\!"

Given |I : Set| we consider the category of families over |I|. Its objects are
|I|-indexed families of types |A : I → Set| and morphisms are given by 
|I|-indexed families of functions:

%format * = "^{\star}" 
%format -*-> = "\rightarrow" *
%format -**-> = "\rightarrow" *
%format _-*->_ = _ -*-> _
%format _-**->_ = _ -**-> _
%format _⊚_ = _ "\circ" * _ 
%format ⊚ = "\circ" * 
%format idd = id *

\begin{code}

_-*->_ : {I : Set} -> (A B : I -> Set) -> Set
_-*->_ {I} A B = (i : I) -> A i -> B i

idd : {I : Set} {A : I → Set} → A -*-> A
idd i a = a 

_⊚_ :  {I : Set} {A B C : I → Set} → 
       (B -*-> C) → (A -*-> B) → (A -*-> C)
f ⊚ g = λ i → (f i) ∘ (g i)

\end{code}


%if style==code

\begin{code}

Fam : Set → Set₁
Fam I = I → Set

\end{code}

%endif

\noindent
We call this category |Fam I|.
An |I|-indexed functor is then a functor from |Fam I| to |Set|, given by:

\begin{code}

record IFunc (I : Set) : Set₁ where
  field
    obj : (A : Fam I) -> Set
    mor : ∀ {A B} -> (A -*-> B) -> obj A -> obj B

\end{code}

\noindent
such that both |idd| is mapped to |id| and |_⊚_| to |_∘_| under the action of 
|mor|. We adopt the convention that the projections |obj| and |mor| are silent, 
\emph{i.e.} depending on the context |F :  IFunc I| can stand for either the 
functor's action on objects, or on morphisms. A morphism between to such 
indexed functors is a natural transormation:

%format ^F = "^{\text{\tiny F}}"
%format ⇒^F = "\Rightarrow" ^F
%format _⇒^F_ = _ ⇒ ^F _

\begin{code}
_⇒^F_ : ∀ {I} → (F G : IFunc I) → Set₁
F ⇒^F G =  ∫ A ** IFunc.obj F A ->> IFunc.obj G A
\end{code}

\noindent



%format η = "\eta"
%format η^F = η ^F
%format >>=^F = >>= ^F
%format _>>=^F_ = _ >>=^F _

|IFunc| comes with a monad like structure given by:

\begin{code}

η^F : ∀ {I} → I → IFunc I
η^F i = record { obj = λ A → A i; mor = λ f → f i }

_>>=^F_ : ∀ {I J} → IFunc I → (I → IFunc J) → IFunc J
F >>=^F H = 
   record  {  obj  =  λ A  → IFunc.obj F (λ i  → IFunc.obj  (H i)  A  )
           ;  mor  =  λ f  → IFunc.mor F (λ i  → IFunc.mor  (H i)  f  ) }

\end{code}

\noindent
It's clear that |IFunc| cannot be a monad in the usual sense, since it is not 
an endo-functor, it does how ever fit with the notion of relative monad 
presented by Altenkirch \emph{et al.} Note that in the code above we have 
elided the use of the lifting functor.

%format Seti = Set "_{i}"
%format Setsi = Set "_{i+1}" 
%format ↑ = "\uparrow"

\begin{proposition} 
|(IFunc , η^F , _>>=^F_)| is a \emph{relative monad}\cite{relmonads} on the 
lifting functor |↑ : Seti → Setsi|.
\end{proposition}

\begin{proof}
To prove the structure is a relative 
monad we observe that the following equalities hold up to 
Agda's $\beta\eta$-equality, and our postulate |ext|.

For |F : IFunc I|, |G : IFunc* J I|, |H : IFunc* K J|:
\begin{align}
|H i|                 &\quad& \equiv &&\quad& |(η^F i) >>=^F H|               \\
|F|                   && \equiv &&& |F >>=^F η^F|                 \\
|(F >>=^F G) >>=^F F| && \equiv &&& |F >>=^F (λ i → (G i) >>=^F H)| 
\end{align}

\end{proof}

%format IFunc* = IFunc * 
%format obj* = obj *
%format mor* = mor *

\noindent
The opposite of the Kleisli category associated with |IFunc| has objects 
|I , J : Set| and morphisms given by |J|-indexed families of |I|-indexed 
functors. We denote this notion of indexed functor |IFunc*|: 

\begin{code}

  

IFunc* : (I J : Set) → Set₁ 
IFunc* I J = J → IFunc I 

obj* : ∀ {I J} → IFunc* I J → Fam I → Fam J
obj* F A j    = IFunc.obj (F j) A

mor* :  ∀ {I J A B} (F : IFunc* I J) → A -*-> B → obj* F A -*-> obj* F B
mor* F m j  = IFunc.mor (F j) m 

\end{code}

\noindent
Again, we will omit |obj*| and |mor*| when inferable from the context 
in which they appear. Natural transformations extend to this double index 
setting, too:

%format obj* = 
%format mor* = 

%format ^F* = "^{\text{\tiny F}^{\star}}"
%format =*=>^F = "\Rightarrow" ^F*
%format _=*=>^F_ = _ "\Rightarrow" ^F* _


\begin{code}

_=*=>^F_ : ∀ {I J} → (F G : IFunc* I J) → Set₁
F =*=>^F G = ∫ A ** obj* F A -*-> obj* G A 

\end{code}

%format Δ = "\Delta"
%format Δ^F = Δ ^F
%format Π = "\Pi"
%format Π^F = Π ^F
%format Σ^F = Σ ^F

\noindent
Clearly, the Kleisli structure gives rise to identities and composition in 
|IFunc*|. Indeed, composition gives rise to a \emph{re-indexing} operation which
we denote |Δ^F|:

\begin{code}

Δ^F : ∀ {I J K} → (J → K) → IFunc* I K → IFunc* I J
Δ^F f F = F ∘ f 

\end{code}


\noindent
This construction is used, for instance, in building the pattern functor for |ScLam| as in the introduction; Concentranting only on the |abs| case we want to build  
|ScLam′ X n = (X ∘ suc) n|. Or simply |ScLam′ X = Δ^F suc X|. In general this combinator 
restricts the functor |X| to the indicies in the image of the
function |f|.

What if the restriction appears on the right of such an equation? As an example,
consider the successor constructor for |Fin|; here we want to build the pattern functor: |FFin′ X (1+ n) = X n|. To do this we observe that this is equivalent to
the equation |FFin′ X n = Σ Nat λ m → n ≡ 1+ m × X m|. We denote the general
construction |Σ^F|, so the 2nd equation can be written |FFin′ X = Σ^F suc X|:

\begin{code}

Σ^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Σ^F {J} f F k = 
   record  {  obj  =  λ A → Σ* j ∶ J *Σ (f j ≡ k × obj* F A j) 
           ;  mor  =  λ m → split j & p & x tilps ↦ (j , p , mor* F m j x) !m !s }
 
\end{code}

\noindent
Perhaps unsuprisingly, |Σ^F| turns out to be the left adjoint to re-indexing 
(|Δ^F|). Its right adjoint, we denote |Π^F|:

\begin{code}

Π^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Π^F {J} f F k = 
   record  {  obj  =  λ A → (j : J) → f j ≡ k → obj* F A j 
           ;  mor  =  λ m g j p → mor* F m j (g j p) }

\end{code}

\begin{proposition}
|Σ^F| and |Π^F| are left and right adjoint to re-indexing (|Δ^F|). 
\end{proposition}

\begin{proof}

To show this we need to show that for all |f : J → K|, |g : K → J|, | F : IFunc* I J| and |G : IFunc* I K|:

\[\begin{array}{c}
|Σ^F f F =*=>^F G|
\\\hline\hline
|F =*=>^F Δ^F f G|\\
\end{array}
\quad
\begin{array}{c}
|Δ^F f F =*=>^F G|
\\\hline\hline
|F =*=>^F Π^F f G|\\
\end{array}
\]

We can build the components of these isomorphisms easily:

%format Σ⊣Δ = "\Sigma\!\dashv\!\Delta"
%format Δ⊣Π = "\Delta\!\dashv\!\Pi"
%format Σ⊣Δφ = Σ⊣Δ 
%format Σ⊣Δψ = Σ⊣Δ minusone
%format Δ⊣Πψ = Δ⊣Π minusone
%format Δ⊣Πφ = Δ⊣Π 

%if style == newcode

\begin{code}

module SigDeltaPi {I J K : Set} {F : IFunc* I J} {G : IFunc* I K} where
  

\end{code}

%endif

\begin{code}

  Σ⊣Δφ : (f : J → K) → (Σ^F f F =*=>^F G) → (F =*=>^F Δ^F f G)
  Σ⊣Δφ f m j x = m (f j) (j , refl , x)

  Σ⊣Δψ : (f : J → K) → (F =*=>^F Δ^F f G) → (Σ^F f F =*=>^F G)
  Σ⊣Δψ f m .(f j) (j , refl , x) = m j x

  Δ⊣Πφ : (g : K → J) → (Δ^F g F =*=>^F G) → (F =*=>^F Π^F g G)
  Δ⊣Πφ g m .(g k) x k refl = m k x

  Δ⊣Πψ : (g : K → J) → (F =*=>^F Π^F g G) → (Δ^F g F =*=>^F G)
  Δ⊣Πψ g m k x = m (g k) x k refl

\end{code}

\noindent
It only remains to observe that these pairs or functions are mutual inverses, 
which is a simple proof.

\end{proof}

In abstracting over all possible values for the extra indexing information |Π^F|
allows for the construction of infinitely branching trees, such as rose trees. 
We also note that finite co-products and products can be derived from |Σ^F| and 
|Π^F| respectively:


%format ⊥^F = ⊥ ^F
%format ⊤^F = ⊤ ^F

%format +^F = "\mathbin{" ⊎ ^F "}"
%format _+^F_ = _ ⊎ ^F _

%format ×^F = "\mathbin{" × ^F "}"
%format _×^F_ = _ ×^F _


\begin{code}
⊥^F : ∀ {I} → IFunc* I ⊤
⊥^F = Σ^F  {J = ⊥} _ λ ()

_+^F_ : ∀ {I} → (F G : IFunc I) → IFunc* I ⊤
F +^F G = Σ^F _ λ b → if b then F else G 

⊤^F : ∀ {I} → IFunc* I ⊤
⊤^F = Π^F  {J = ⊥} _ λ ()

_×^F_ : ∀ {I} → (F G : IFunc I) → IFunc* I ⊤
F ×^F G = Π^F _ λ b → if b then F else G  
\end{code}

\noindent
Clearly these are simply the constantly |⊤| and |⊥| valued functors, and the 
point-wise product and co-product of functors, but this encoding allows us to 
keep the number of constants in our vocabulary to a minimum.

\subsection{Initial algebras of indexed functors}

We observe that an |F : IFunc* I I| is an endo-functor on the category |Fam I|. 
Using this observation we know that an algebra of such a functor is a family 
|A : Fam I| and a map |α : obj* F A -*-> A|. A morphism, then, between two such 
algebras |(A , α)| and |(B , β)| is a map |f : A -*-> B| such that the follow 
diagram commutes:

 \[
\xymatrix{
\mbox{|obj* F A|}  \ar[r]^{\;\mbox{|α|}} 
\ar[d]_{\mbox{|mor* F f|}} & \mbox{|A|} \ar[d]^{\mbox{|f|}}\\
\mbox{|obj* F B|} \ar[r]^{\;\mbox{|β|}} & \mbox{|B|}}
\]

\noindent
If it exists then the initial algebra of |F| is the initial object of the 
category of |F|-algebras spelt out above. It follows from the fact that not all
functors in |Set → Set| (for instance |F A = (A → Bool) → Bool|) have initial 
algebras that neither do all indexed-functors.

We also know that we cannot iterate the construction of initial algebras given 
above, an endo-functor |IFunc* I I| gives rise to an initial algebra in |Fam I|.
This prevents us from being able to define nested, or mutual inductive families 
in this way.

For the morphism part of an indexed-functor over a co-product we can eliminate
the coproduct and curry the result ing definition in this way:

\begin{align*}
|IFunc (I ⊎ J)| 
  & \equiv      & |(I ⊎ J → Set) → Set| \\
  & \cong       & |(I → Set) × (J → Set) → Set|\\
  & \cong       & |(I → Set) → (J → Set) → Set|\\
\end{align*}

\noindent
This gives us partial application for indexed 
functors of the form |IFunc (I ⊎ J)|. Spelt out concretely we have:


%format ⟨ = [
%format ⟩F = ] ^F
%format _⟨_⟩F = _ ⟨ _ ⟩F
%format ⟩M = ] ^F
%format _⟨_⟩M = _ ⟨ _ ⟩M 
\begin{code}

_⟨_⟩F : ∀ {I J} → IFunc (I ⊎ J) → IFunc* I J →  IFunc I
F ⟨ G ⟩F  = 
  record  {  obj  = λ A  → IFunc.obj F [ A  , obj*  G A  ]
          ;  mor  = λ f  → IFunc.mor F [ f  , mor*  G f  ] }
\end{code}

\noindent
This construction is functorial:


\begin{code}
_⟨_⟩M :  ∀ {I J}  (F : IFunc (I ⊎ J)) {G H : IFunc* I J}  
           →        G      =*=>^F        H                  
           →   F ⟨  G ⟩F   ⇒^F      F ⟨  H ⟩F   
F ⟨ γ ⟩M = IFunc.mor F [ (λ _ a → a) , γ ] 

\end{code}

\noindent
Each of these definitions generalises to |IFunc*|:

%format ⟩F*  = ] "^{\text{\tiny{F}}^{\star}}"
%format _⟨_⟩F* = _ ⟨ _ ⟩F*
%format ⟩M*  = ] "^{\text{\tiny{F}}^{\star}}"
%format _⟨_⟩M* = _ ⟨ _ ⟩M*

\begin{code}

_⟨_⟩F* : ∀ {I J K} → IFunc* (I ⊎ J) K → IFunc* I J →  IFunc* I K
F ⟨ G ⟩F*  = λ k → (F k) ⟨ G ⟩F 

_⟨_⟩M* :  ∀ {I J K}  (F : IFunc* (I ⊎ J) K) {G H : IFunc* I J}  
            →           G       =*=>^F       H                    
            →      F ⟨  G ⟩F*   =*=>^F  F ⟨  H ⟩F*  
_⟨_⟩M* F {G} {H} γ = λ k → _⟨_⟩M  (F k) {G} {H} γ  

\end{code}

\noindent
A parametrized |F|-algebra for |F : IFunc* (I ⊎ J) I| is a pair of an 
indexed-functor |G : IFunc J I| and a natural transformation
|α : F ⟨ G ⟩F* =*=>^F G|. A morphism between two such algebras 
|(G , α)| and |(H , β)| is a natural transformation |γ : G =*=>^F H| 
such that the follow diagram commutes:

\[
\xymatrix{
\mbox{|F ⟨ G ⟩F*|}  \ar[r]^{\quad\mbox{|α|}} 
\ar[d]_{\mbox{|F ⟨ γ ⟩M*|}} & \mbox{|G|} \ar[d]^{\mbox{|γ|}}\\
\mbox{|F ⟨ H ⟩F*|} \ar[r]^{\quad\mbox{|β|}} & \mbox{|H|}}
\]

\noindent
As you might expect, a parametrized initial algebra for |F|, if it is exists, 
will be the initial object in the category of parametrized |F|-algebras. 

The fact that the parametrized initial algebra construction can be iterated, 
means that we can define nested and mutual families of data-types, such as the
tuple of neutral and normal |λ|-terms outlined in the introduction. 

As before we know that not all |IFunc* (I ⊎ J) I| functors have initial 
algebras. In the next section, however we spell out what it is for a functor to 
be given by an indexed container, and these functors are those which have such 
initial algebras.