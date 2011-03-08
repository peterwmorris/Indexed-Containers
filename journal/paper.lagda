%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module paper where

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

infixl 20  _$$_

unc : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : Σ A B → Set l''} →
      ((x : A) → (y : B x) → C (x , y)) →
      ((p : Σ A B) → C p)
unc = uncurry

ids : ∀ {l} {A : Set l} → A → A
ids = id 

idt : ∀ {l} {A : Set l} → A → A
idt = id 

infixr 102 ↦_!m

↦_!m : ∀ {l} {A : Set l} → A → A
↦_!m = id 

infixr 103 split_!s

split_!s : ∀ {l} {A : Set l} → A → A
split_!s = id 

infixr 101 unc
infixr 102 ids
infixr 102 idt

syntax unc (λ x → t) = x & t
syntax ids (λ x → t) = x tilps t 
syntax idt (λ x → t) = x !* t 

_$$_ : ∀ {l l'} {A : Set l} {B : A → Set l'} →
      ((x : A) → B x) → ((x : A) → B x)
f $$ x = f x

_-**->_ : {I : Set} -> (A B : I -> Set) -> Set
_-**->_ {I} A B = {i : I} -> A i -> B i


\end{code}

%endif

%format . = "."
%format $$ = "\!\!" 
%format split = \ ( "\!"
%format tilps = "\!\!" )
%format & = "\!" , "\!"
%format ↦ =  →
%format !* = "\!" 
%format !s = "\!"
%format !m = "\!"

\documentclass[a4paper]{article}

\usepackage{url}
\usepackage{times}
\usepackage{amsmath}
\usepackage{xypic}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}

\newcommand{\note}[1]{}

%include lhs2TeX.fmt
%include agda.fmt


%include lib.fmt

\begin{document}

\newcounter{theorem}

\newtheorem{proposition}[theorem]{Proposition}
\newenvironment{proof}[1][Proof]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}

\title{Indexed Containers}
\author{Thorsten Altenkirch 
   \and Neil Ghani 
   \and Peter Hancock 
   \and Conor McBride 
   \and Peter Morris}
\date{\today}

\maketitle

\begin{abstract}

Blah

\end{abstract}


\section{Introduction}

\section{Background}

\subsection{Type Theory}

\newcommand{\prodd}{\ensuremath{\mathaccent\cdot{\prod}}}

%format ∫ = "\prodd"
%format ** = "."
%format Setop = Set "^{" op "}"

%if style==newcode

\begin{code}
EndS : ∀ {l l'} {T : Set l} → (F : T → Set l') → Set (l ⊔ l')
EndS {T = T} F = {X : T} → F X


syntax EndS (λ X → F) = ∫ X ** F

Setop : Set₁
Setop  = Set 
\end{code}

%endif


Our contructions are all developed in Agda, and so we adopt it's type-theory and
syntax. With the following extra pieces of notation:

\begin{code}

postulate ext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g

ext⁻¹ : {A : Set} {B : A → Set} {f g : (a : A) → B a} → f ≡ g → ((a : A) → f a ≡ g a)
ext⁻¹ refl a = refl

data W (S : Set) (P : S → Set) : Set where
  sup : (s : S) (f : P s → W S P) → W S P

\end{code}

We are going to use type theory versions of certain category theoretic concepts 
For instance, we use ends |End| to capture natural transformations.
Given a bifunctor |F : Setop → Set → Set|, an element of |∫ X ** F X X| is
equivalent to an element of |f : {X : Set} → F X X|, along with a proof:

\[ \mbox{|{A B : Set} (g : A → B) → F g B (f {B}) ≡ F A g (f {A})|} \]


\noindent
The natural transformations between functors |F| and |G| are
ends |∫ X ** F X → G X|. We will often ignore the presence of the proofs, and 
use such ends directly as polymorphic functions.

In this setting, the Yoneda lemma can be stated as follows:

\[\mbox{| F X ≅ ∫ Y ** (X → Y) → F Y |}\]

we will make use of this fact later on.

\subsection{Containers}

%format ◁ = "\lhd"
%format _◁_ = _ ◁ _


\begin{code}

record Cont : Set₁ where
  constructor _◁_ 
  field 
    S : Set
    P : S → Set

⟦_⟧′ : Cont → Set → Set
⟦ S ◁ P ⟧′ X = Σ S λ s → P s → X

\end{code}

\section{Indexed Functors}

%if style==code

\begin{code}

\end{code}

%endif

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

_⊚_ : {I : Set} {A B C : I → Set} → B -*-> C → A -*-> B → A -*-> C
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
Such that both |idd| is mapped to |id| and |_⊚_| to |_∘_| under the action of 
|mor|. We adopt the convention that the projections |obj| and |mor| are silent, 
\emph{i.e.} depending on the context |F :  IFunc I| can stand for either the 
functor's action on objects, or on morphisms. A morphism between too such 
indexed functors is a natural transormation:

%format ^F = "^{\text{\tiny F}}"
%format ⇒^F = "\Rightarrow" ^F
%format _⇒^F_ = _ ⇒ ^F _

\begin{code}
_⇒^F_ : ∀ {I} → (F G : IFunc I) → Set₁
F ⇒^F G = ∫ A ** (IFunc.obj F A → IFunc.obj G A)
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

_>>=^F_ : ∀ {I J} → (I → IFunc J) → IFunc I → IFunc J
H >>=^F F = 
   record  {  obj  =  λ A  → IFunc.obj F (λ i  → IFunc.obj  (H i)  A  )
           ;  mor  =  λ f  → IFunc.mor F (λ i  → IFunc.mor  (H i)  f  ) }

\end{code}

%format Seti = Set "_{i}"
%format Setsi = Set "_{i+1}" 
%format ↑ = "\uparrow"

\begin{proposition} 
|(IFunc , η^F , _>>=^F_)| is a \emph{relative monad}\cite{relmonads} on the 
lifting functor |↑ : Seti → Setsi|.
\end{proposition}

\begin{proof}
It's clear that |IFunc| cannot be a monad in the usual sense, since it is not 
an endo-functor, it does how ever fit with the notion of relative monad 
presented by Altenkirch \emph{et al.} Note that in the code above we have 
elided the use of the lifting functor. To prove the structure is a relative 
monad we observe that the following natural isomorphisms hold immediately up to 
Agda's $\beta\eta$-equality.

For |F : IFunc I|, |G : I → IFunc J|, |H : J → IFunc K|:
\begin{align}
|H i|                 &\quad& \approx &&\quad& |H >>=^F (η^F i)|               \\
|F|                   && \approx &&& |η^F >>=^F F|                 \\
|H >>=^F (G >>=^F F)| && \approx &&& |(λ i → H >>=^F (G i)) >>=^F F| 
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
This construction is used, for instance, if we try to build an indexed functor
whose fixed point is |Lam|; Concentranting only on the |abs| case we build a functor 
|F′ n X = F (1+ n) X|. Or simply |F′ = Δ^F (1+) F|. In general this combinator 
restricts the functor |F′| to the parts of |F| over indexes in the image of the
function |F|.

What if the restriction appears on the right of such an equation? As an example,
consider the successor constructor for |Fin|; here we want to solve the 
equation |F′ (1+ n) X = F n X|. To do this we observe that this is equivalent to
the equation |F′ n X = Σ Nat λ m → n ≡ 1+ m × F m X|. We denote the general
construction |Σ^F|, so the 2nd equation can be written |F′ = Σ^F (1+) F|:

\begin{code}

Σ^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Σ^F {J} f F k = 
   record  {  obj  =  λ A → Σ J λ j → f j ≡ k × obj* F A j 
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
|Π^F| respectively. First we construct:

%format H0 = H "_{0}"
%format H2 = H "_{2}"

%format ⊥^F = ⊥ ^F
%format ⊤^F = ⊤ ^F

%format +^F = "\mathbin{" + ^F "}"
%format _+^F_ = _ + ^F _

%format ×^F = "\mathbin{" × ^F "}"
%format _×^F_ = _ ×^F _

\begin{code}
H0 : ∀ {I} → IFunc* I ⊥
H0 ()

H2 : ∀ {I} → (F G : IFunc I) → IFunc* I Bool
H2 F G true   = F
H2 F G false  = G
\end{code}

We can then obtain:

\begin{code}
⊥^F : ∀ {I} → IFunc* I ⊤
⊥^F = Σ^F  _ H0

_+^F_ : ∀ {I} → (F G : IFunc I) → IFunc* I ⊤
F +^F G = Σ^F _ (H2 F G) 

⊤^F : ∀ {I} → IFunc* I ⊤
⊤^F = Π^F  _ H0

_×^F_ : ∀ {I} → (F G : IFunc I) → IFunc* I ⊤
F ×^F G = Π^F _ (H2 F G) 
\end{code}

\noindent
Clearly these are simply the constantly |⊤| and |⊥| valued functors, and the 
point-wise product and co-product of functors, but this encoding allows us to 
keep the number of constants in out vocabulary to a minimum.

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
triple of terms, types and contexts outlined in the introduction. 

As 
before we know that not all |IFunc* (I ⊎ J) I| functors have initial algebras. 
In the next section, however we spell out what it is for a functor to be given 
by an indexed container, and these functors are those which have such initial 
algebras.

\section{Indexed containers}

%format _◁_ = "\_\mbox{$\lhd$}\_"
%format ICont* = ICont *
%format ⟧* = ⟧ *
%format ◁* = ◁ *
%format _◁*_ = _ ◁* _
%format ICont.S = _ "." S
%format ICont.P = _ "." P
%format projS  = "\!." S
%format projP  = "\!." P
%format projS*  = projS 
%format projP*  = projP 
%format $* = "\!\!"
%format λ* = "\!\!"

An |I|-indexed container is given by a set of shapes, and an |I|-indexed \emph{family} of positions:

\begin{code}

record ICont (I : Set) : Set₁ where
  constructor _◁_
  field
    S : Set
    P : S → I → Set

\end{code}

The extension of such a container is an |IFunc I|:

\begin{code}

⟦_⟧ : ∀ {I} → ICont I → IFunc I
⟦_⟧ {I} (S ◁ P) = 
  record  {  obj  = λ A  → Σ S (λ s → (i : I) → P s i → A i)
          ;  mor  = λ m  → split s & f tilps ↦ (s , m ⊚ f) !m !s }

\end{code}

As with |IFunc| we can extend this notion to doubly indexed containers, where
an |ICont* I J| is a function from |J| to |ICont I|:

\begin{code}
record ICont* (I J : Set) : Set₁ where
  constructor _◁*_
  field
    S : J → Set
    P : (j : J) → S j → I → Set


⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ S ◁* P ⟧* i = ⟦ S i ◁ P i ⟧


\end{code}

We will denote the two projections for an |ICont| postfix as |_ projS| and
|_ projP|. 

%if style == code 

\begin{code}

_projS : ∀ {I} → ICont I → Set
_projS = ICont.S

_projP : ∀ {I} → (C : ICont I) → ICont.S C → I → Set
_projP = ICont.P

_projS* : ∀ {I J} → ICont* J I → I → Set
_projS* C = ICont*.S C 

_projP* : ∀ {I J} → (C : ICont* J I) → (i : I) → ICont*.S C i → J → Set
_projP* C = ICont*.P C

_$*_ : ∀ {I J} → ICont* I J → J → ICont I
(S ◁* P) $* j = S j ◁ P j

λ* : ∀ {I J} → (J → ICont I) → ICont* I J
λ* F = (λ j → (F j) projS) ◁* (λ j → (F j) projP)

\end{code}

%endif

%format ^C = "^{\text{\tiny C}}"
%format ^C* = "^{\text{\tiny C}^{\star}}"
%format ⇒ = "\Rightarrow" ^C
%format _⇒_ = _ ⇒ _
%format ⇒* = "\Rightarrow" ^C*
%format _⇒*_ = _ "\Rightarrow" ^C* _
%format ⟧⇒ = ⟧ "\mbox{$\!^{\Rightarrow}$}"
%format ⟦_⟧⇒ = ⟦ _ ⟧⇒
%format ⟧⇒* = ⟧ "\mbox{$\!^{\Rightarrow^{\!\star}}$}"
%format ⟦_⟧⇒*_ = ⟦ _ ⟧⇒* _

\noindent
We can establish what denotes a morphism between a container |S ◁ P : ICont I|
and functor |F : IFunc I|, simply by expanding the definition and employing 
the following derivation:

\begin{align*}
                & |⟦ S ◁ P ⟧ ⇒^F F| & \\
  \equiv  \;    & |∫ X ** (Σ S λ s → P s -*-> X) → F X| & \{\mbox{by definition}\} \\
  \equiv  \;    & |∫ X ** (s : s) → (P s -*-> X) → F X| & \{\mbox{currying}\} \\
  \cong   \;    & |(s : S) → ∫ X ** (P s -*-> X) → F X| & \{\mbox{commuting end and pi} \} \\
  \cong   \;    & |(s : S) → F (P s)| & \{\mbox{Yoneda}\} \\
\end{align*}

\noindent
If |F| is also an indexed container |T ◁ Q| then we have:

\begin{align*}
           & |⟦ S ◁ P ⟧ ⇒^F ⟦ T ◁ Q ⟧| \\
 \cong \;  & |(s : S) → Σ T λ t → Q t -*-> P s| \\
 \cong \;  & |Σ (S → T) λ f → (s : S) → Q (f s) -*-> P s|
\end{align*}
 
We will use this last line as the definition for container morphisms, captured by 
this record type:  

\begin{code}

record _⇒_ {I} (C D : ICont I) : Set₁ where
  constructor _◁_
  field 
    f : C projS → D projS
    r : (s : C projS) → (D projP $$ (f s)) -*-> (C projP $$ s)

\end{code}

\noindent
We witness one side of the isomorphism between container morphisms and natural 
transformations:

\begin{code}

⟦_⟧⇒ : ∀ {I} {C D : ICont I} (m : C ⇒ D)  → 
              ∫ A ** (IFunc.obj ⟦ C ⟧ A  → IFunc.obj ⟦ D ⟧ A)
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ⊚ r s

\end{code}

\begin{proposition}

The functor |(⟦_⟧_ , ⟦_⟧⇒_)| in |[ ICont I , IFunc I ]| is full and faithful.

\end{proposition}

\begin{proof}

By construction.

%%\begin{code}
%%
%%q : {I : Set} (C D : ICont I) → ({A : I → Set}  → IFunc.obj ⟦  C ⟧ A  → IFunc.%%obj ⟦  D ⟧ A) 
%%                                                →              C      ⇒       %%       D
%%q C D m = (proj₁ ∘ eureka) ◁ (proj₂ ∘ eureka)
%% where
%%  eureka : (s : C projS) → IFunc.obj ⟦ D ⟧ (C projP $$ s)
%%  eureka s =  m (s , idd)
%%
%%\end{code}
%%
%%By naturality this must be the unique inverse to the extesion of a container
%%morphism given above.
%%

\end{proof}

We can lift this functor to the doubly indexed variant:

\begin{code}

record _⇒*_ {I J} (C D : ICont* I J) : Set₁ where
  constructor _◁*_
  field 
    f : C projS* -*-> D projS*
    r : {j : J} (s : C projS* $$ j) → (D projP* $$ j $$ (f j s)) -*-> (C projP* $$ j $$ s)


⟦_⟧⇒* : ∀  {I J} {C D : ICont* I J} (m : C ⇒* D) → 
           ∫ A ** (obj* ⟦ C ⟧* A  -*-> obj* ⟦ D ⟧* A)
⟦ f ◁* r ⟧⇒* j = ⟦ (f j) ◁ r ⟧⇒  

\end{code}

%format projf  = "\!." f
%format projr  = "\!." r
%format projf*  = "\!." f 
%format projr*  = "\!." r 

%if style == code 

\begin{code}

_projf :  ∀ {I} {C D : ICont I} (m : C ⇒ D) → C projS → D projS
_projf = _⇒_.f

_projr : ∀ {I} {C D : ICont I} (m : C ⇒ D) (s : C projS) → (D projP $$ (m projf $$ s)) -*-> (C projP $$ s)
_projr = _⇒_.r

_projf* :  ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) → C projS* $$ j → D projS* $$ j
_projf* m j = _⇒*_.f m j 

_projr* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) (s : C projS* $$ j) → (D projP* $$ j $$ (m projf* $$ j $$ s)) -*-> (C projP* $$ j $$ s)
_projr* m j = _⇒*_.r m  

\end{code}

%endif

%format η^C = η ^C
%format >>=^C = >>= ^C
%format _>>=^C_ = _ >>=^C _

As with |IFunc|, we can equip |ICont| with a relative monadic structure:

\begin{code}

η^C : ∀ {I} → I → ICont I
η^C i = ⊤ ◁ λ _ i′ → i ≡ i′

_>>=^C_ : ∀ {I J} → ICont* J I → ICont I → ICont J
_>>=^C_ {I} (T ◁* Q) (S ◁ P) =  
     (IFunc.obj ⟦ S ◁ P ⟧ T) 
  ◁  split s & f tilps j !* ↦ Σ  (Σ I (P s)) (split i & p tilps ↦ Q i (f i p) j !m !s) !m !s  

\end{code}

%format ≈^C = "\approx^{\text{\tiny{C}}}"

\begin{proposition}

The triple |(ICont , η^C , _>>=^C_)| is a relative monad.

\end{proposition}

\begin{proof}

Instead of proving this directly, we observe that the |η^C| and |_>>=^C_|
are preserved under |⟦_⟧_|, i.e.:

\begin{align*}
|⟦ η^C i ⟧| && \approx &&& |η^F i| \\
|⟦ C >>=^C D ⟧| && \approx &&& |⟦ C ⟧* >>=^F ⟦ D ⟧| \\
\end{align*}

Which follow from the extensionality of our propositional equality, the 
assosciativity of |Σ| and the terminality of |⊤|. By the full and faithful 
nature of the embedding into |IFunc| we can then reuse the result that
|(IFunc , η^F , _>>=^F_)| is a relative monad.

\end{proof}

%format Δ^C = Δ ^C
%format Π^C = Π ^C
%format Σ^C = Σ ^C

As with indexed functors, the re-indexing |Δ^C| is defined by composition, and 
has left and right adjoints |Σ^C| and |Π^C|:

%if style == newcode 

\begin{code}

module DelSigPi {I J K : Set} where

\end{code}

%endif

\begin{code}

  Δ^C : (J → K) → ICont* I K → ICont* I J
  Δ^C f F = λ* λ k → F $* (f k) 

  Σ^C : (J → K) → ICont* I J → ICont* I K
  Σ^C f (S ◁* P) = λ* λ k →  
       (Σ J λ j → f j ≡ k × S j) 
    ◁  split j & eq & s tilps ↦ P j s !m !s
 
  Π^C : (J → K) → ICont* I J → ICont* I K
  Π^C f (S ◁* P) =  λ* λ k →  
       ((j : J) → f j ≡ k → S j)
    ◁  λ s i → Σ J λ j → Σ (f j ≡ k) λ eq → P j (s j eq) i 

\end{code}

%if style == newcode 

\begin{code}

open DelSigPi

\end{code}

%endif

\begin{proposition}
|Σ^C| and |Π^C| are left and right adjoint to re-indexing (|Δ^C|).
\end{proposition}

\begin{proof}

Again we appeal to the full and faithfullness of |⟦_⟧_| and show instead that
the embedding into |IFunc| preserves these constructions. That, is we want to show that the following three statements hold:

\begin{align*}
|⟦ Σ^C f F j ⟧| && \approx &&& |Σ^F f ⟦ F ⟧* j| \\
|⟦ Δ^C f F j ⟧| && \equiv &&& |Δ^F f ⟦ F ⟧* j| \\
|⟦ Π^C f F j ⟧| && \approx &&& |Π^F f ⟦ F ⟧* j| \\
\end{align*}

These can be proved simply by employing the associativity of |Σ|.

\end{proof}

%format ✧ = "\lozenge"

%format ⟩C = ] ^C
%format ⟩C*  = ] "^{\text{\tiny{C}}^{\star}}"
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format _⟨_⟩C* = _ ⟨ _ ⟩C*
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 

%format PI = P "^{" I "}"
%format PJ = P "^{" J "}" 

Before we build the initial algebras of indexed containers, it will help to 
define their partial application. 

\begin{code}

_⟨_⟩C : ∀ {I J} → ICont (I ⊎ J) → ICont* J I → ICont J
_⟨_⟩C {I} {J} (S ◁ P) (T ◁* Q) = 
  let  PI  : S  → I  → Set            ;  PI  s  i  = P s (inj₁ i) 
       PJ  : S  → J  → Set            ;  PJ  s  j  = P s (inj₂ j) 
  in   IFunc.obj ⟦ S ◁ PI ⟧ T ◁     (split s & f tilps j !* ↦ PJ s j 
                                 ⊎  (Σ I λ i → Σ (PI s i) λ p → Q i (f i p) j) !m !s)

\end{code}

\noindent
The composite container has shapes given by a shape |s : S| and an assigment of |T| 
shapes to |PI s| positions. Positions are then a choice between 
a |J|-indexed position, or a pair of an |I|-indexed position, and a |Q| position
\emph{underneath} the appropriate |T| shape. 

%if style==code

\begin{code}

_⟨_⟩C* : ∀ {I J K} → ICont* (I ⊎ J) K → ICont* J I →  ICont* J K
_⟨_⟩C* C D = λ* λ k → (C $* k) ⟨ D ⟩C

\end{code}

%endif

\noindent
As with indexed functors, this construction is functorial in its second 
argument, and lifts container morphisms in this way:

\begin{code}

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* J I} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  split s & f tilps ↦ (s , λ i p → γ projf* $$ i $$ (f i p)) !m !s) ◁ 
     split s & f tilps j !* ↦ [ inj₁ , (split i & p & q tilps ↦ inj₂ (i , p , γ projr* $$ i $$ (f i p) $$ j $$ q) !m !s) ] !m !s 

\end{code}



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

\section{Terminal Co-Algebras of Indexed Containers}

%format ∞ = "\infty"
%format ♯ = "\sharp"
%format ♭ = "\flat"
%format Math = Path
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


MIunfold :  ∀  {I} {X : I → Set} {S : I → Set} 
             {PI : (i : I) → S i → I → Set} →
             X -*-> obj* ⟦ S ◁* PI ⟧* X → X -*-> MI S PI 
MIunfold m i x with m i x
MIunfold m i x | s , f = sup (s , (λ i′ p → ♯ MIunfold m i′ (f i′ p)))

data Math  {I J : Set} (S : I → Set)  
           (PI  : (i : I) → S i → I  → Set) 
           (PJ  : (i : I) → S i → J  → Set) 
           : (i : I) → MI S PI i → J → Set where
  math : ∀  {i s f j} →     
               PJ i s j 
            ⊎  (Σ I λ i′ → Σ (PI i s i′) λ p → Math S PI PJ i′ (♭ (f i′ p)) j) 
            → Math S PI PJ i (sup (s , f)) j 

ν^C : {I J : Set} → ICont* (I ⊎ J) I → ICont* J I
ν^C {I} {J} (S ◁* P) = 
  let  PI  : (i : I) → S i → I  → Set ;  PI  i s i′  = P $$ i $$ s $$ (inj₁ i′) 
       PJ  : (i : I) → S i → J  → Set ;  PJ  i s j   = P $$ i $$ s $$ (inj₂ j)
  in   MI S PI ◁* Math S PI PJ

out^C : ∀ {I J} → (F : ICont* (I ⊎ J) I) → ν^C F ⇒* F ⟨ ν^C F ⟩C* 
out^C (S ◁* P) = (λ _ → sup⁻¹) ◁* {!!}
  -- where
--    outS : 

unfold^C : ∀  {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → 
              G ⇒* F ⟨ G ⟩C* → G ⇒* ν^C F
unfold^C {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = funfold ◁* runfold  
    where  PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = P i s (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = P i s (inj₂ j)
           funfold = MIunfold f
           runfold :  {i : I} (t : T i) (j : J) → Math S PI PJ i (funfold i t) j → Q i t j 
           runfold t j (math (inj₁ x)) = r t j (inj₁ x)
           runfold t j (math (inj₂ (i , (p , q)))) = r t j (inj₂ (i , p , runfold (proj₂ (f _ t) i p) j q))

\end{code}

\section{W is still enough}

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

\end{code}

\noindent
Since we have shown that both |WI| and |MI| types can be reduced to their 
non-indexed counterparts, it only remains to show that |M| types can be, reduced
to |W| types. This is a result from \cite{C-CSPTs}, though in the setting of 
indexed |WI| types, we can give a better intuition.

We begin by costructing a counterpart to |W| but which is \emph{cut-off}
at a known depth:

%if style == newcode

\begin{code}

module MfromW where

\end{code}

%endif

\begin{code}

  data WM (S : Set) (P : S → Set) : ℕ → Set where
    wm⊥ : WM S P zero
    sup : ∀ {n} → ⟦ S ◁ P ⟧′ (WM S P n) → WM S P (suc n)

\end{code}

\noindent
This is itself encodable as an indexed |WI| type, and by the result above, a |W|
type:

\begin{code}

  WM′ : (S : Set) (P : S → Set) → ℕ → Set
  WM′ S P = WI S′ P′
    where
      S′ : ℕ → Set
      S′ zero = ⊤
      S′ (suc n) = S
      P′ : (n : ℕ) → S′ n → ℕ → Set 
      P′ zero _ _ = ⊥
      P′ (suc m) s n with m ≟ n 
      P′ (suc .n) s n | yes refl = P s
      P′ (suc m) s n | no ¬p = ⊥

\end{code}

\noindent
We can truncate any given tree of depth greater than 1:

\begin{code}

  trunc : ∀ {S P} → {n : ℕ} → WM S P (suc n) → WM S P n
  trunc {n = zero} (sup (s , f)) = wm⊥
  trunc {n = suc n} (sup (s , f)) = sup (s , trunc ∘ f)

\end{code}

\noindent
We then say that an |M| type is an infinitie sequence of approximations, cut off
at sucessively lower depths, with the property that truncating any tree results 
in the previous tree in the sequence:

\begin{code}

  M : (S : Set) (P : S → Set) → Set
  M S P = Σ  (  (n : ℕ) → WM S P n) λ f → 
                (n : ℕ) → trunc (f (suc n)) ≡ f n

\end{code}

\noindent
Building an algebra map, (|sup|) for this encoding of |M| is straight-forward, 
the difficulty is in constructing the co-algebra map (|sup⁻¹|):

\begin{code}

  ssup⁻¹ :  {S : Set} {P : S → Set} → M S P → ⟦ S ◁ P ⟧′ (M S P)

\end{code}

\noindent
We have to produce a top level shape, but in theory we have an infinite choice
of candidates. We know, though, that all these shapes must 
be equal, so our choice doesn't matter.

\begin{code}

  ssup⁻¹ (wm , t) with wm 1 
  ... | sup (s , f) = s , λ p → ((λ n → {!wm !}) , {!!})

\end{code}

\noindent
\textbf{Question: How much do we show of the proof that this is inverse to |sup|? It's pretty ugly.} 

A path to a position in such an infinite tree is a choice of a particular 
finite approximation, and a path through that tree. Since all paths are finite, 
this is all we need to complete the construction of |ν^C|, above, by only using 
|W| types.

\section{Strictly Positive Types}

\section{Conclusions}


\bibliographystyle{plain}
\bibliography{paper}

\end{document}
