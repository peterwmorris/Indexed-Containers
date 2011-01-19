%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module paper where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality

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


\subsection{Containers}

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

We call this category |Fam I|.

%if style==code

\begin{code}

Fam : Set → Set₁
Fam I = I → Set

\end{code}

%endif

An |I|-indexed functor is then a functor from |Fam I| to |Set|, given by:

\begin{code}

record IFunc (I : Set) : Set₁ where
  field
    obj : (A : Fam I) -> Set
    mor : ∀ {A B} -> (A -*-> B) -> obj A -> obj B

\end{code}

Such that both |idd| is mapped to |id| and |_⊚_| to |_∘_| under the action of 
|mor|. We adopt the convention that the projections |obj| and |mor| are silent, 
\emph{i.e.} depending on the context |F :  IFunc I| can stand for either the 
functor's action on objects, or on morphisms.

A natural transformation between two such functors is given by:

%format ^F = "^{\text{\tiny F}}"
%format ⇒^F = "\Rightarrow" ^F
%format _⇒^F_ = _ ⇒ ^F _

\begin{code}
_⇒^F_ : ∀ {I} → (F G : IFunc I) → Set₁
F ⇒^F G = ∀ {A} → IFunc.obj F A → IFunc.obj G A
\end{code}

with the obvious naturality condition that given |m : F ⇒ G| the following diagram
commutes for all |f : A -*-> B|:

 \[
\xymatrix{
\mbox{|IFunc.obj F A|}  \ar[r]^{\qquad\mbox{|m {A}|}\qquad} 
\ar[d]_{\mbox{|IFunc.mor F f|}} & \mbox{|IFunc.obj G A|} \ar[d]^{\mbox{|IFunc.mor G f|}}\\
\mbox{|IFunc.obj F B|} \ar[r]^{\qquad\mbox{|m {B}|}\qquad} & \mbox{|IFunc.obj G B|}}
\]

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

The opposite of the Kliesli category associated with |IFunc| has objects 
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

Again, we will omit calls to |obj*| and |mor*| when inferrable from the context 
in which they appear.

%format obj* = 
%format mor* = 

Natural transformations:

%format ^F* = "^{\text{\tiny F}^{\star}}"
%format =*=>^F = "\Rightarrow" ^F*
%format _=*=>^F_ = _ "\Rightarrow" ^F* _


\begin{code}

_=*=>^F_ : ∀ {I J} → (F G : IFunc* I J) → Set₁
F =*=>^F G = ∀ {A} → obj* F A -*-> obj* G A   

\end{code}


%format Δ = "\Delta"
%format Δ^F = Δ ^F
%format Π = "\Pi"
%format Π^F = Π ^F
%format Σ^F = Σ ^F

Clearly, the Kliesli structure gives rise to identities and composition in 
|IFunc*|. Indeed, composition gives rise to a \emph{re-indexing} operation which
we denote |Δ^F|:

\begin{code}

Δ^F : ∀ {I J K} → (J → K) → IFunc* I K → IFunc* I J
Δ^F f F = F ∘ f 

\end{code}

This construction is used, for instance, if we try to build an indexed functor
whose fixed point is |Lam|. In the |abs| case we must build a functor 
|F′ n X = F (1+ n) X|. Or simply |F′ = Δ^F (1+) F|. In general this combinator 
restricts the functor |F′| to the parts of |F| over indexes in the image of the
function |F|.

|Δ^F| has left and right adjoints |Σ^F| and |Π^F|:

\begin{code}

Σ^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Σ^F {J} f F k = 
   record  {  obj  =  λ A → Σ J λ j → f j ≡ k × obj* F A j 
           ;  mor  =  λ m → split j & p & x tilps ↦ (j , p , mor* F m j x) !m !s }
 
Π^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Π^F {J} f F k = 
   record  {  obj  =  λ A → (j : J) → f j ≡ k → obj* F A j 
           ;  mor  =  λ m f j p → mor* F m j (f j p) }
\end{code}

\begin{proposition}
|Σ^F| and |Π^F| are left and right adjoint to re-indexing (|Δ^F|).
\end{proposition}

If we imagine that the indexing set |K| is somehow \emph{larger} than |J| (and 
that the function |f| is then a projection). We can explain these constructions 
as the two possible ways to add the extra information --- 
by picking one instance, or considering all possible instantiations. The 
equalities state that `projecting' the smaller index out of the larger gives the
index we cam in with.

We can employ the |Σ^F| construction to buld a functor whose fixed point is 
|Fin| where we want a solution to the equation 
|F′ n X = Σ Nat λ m → n ≡ 1+ m × ⊤ + F m X| or |F′ = Σ^F (1+) F|. In 
abstracting over all possible values for the extra indexing information |Π^F| 
allows for the construction of infinitely branching trees. 
We also note that finite co-products and 
products can be derived from |Σ^F| and |Π^F| respectively. First we construct:

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

If it exists then the initial algebra of |F| is the initial object of the 
category of |F|-algebras spelt out above. It follows from the fact that not all
functors in |Set → Set| (for instance |F A = (A → Bool) → Bool|) have initial 
algebras that neither do all indexed-functors.

We also know that we cannot iterate the construction of initial algebras given 
above, an endo-functor |IFunc* I I| gives rise to an initial algebra in |Fam I|.
This prevents us from being able to define nested, or mutual inductive families 
in this way.

Before we get there we observe that, for the morphism part of an indexed-functor:

\begin{align*}
|IFunc (I ⊎ J)| 
  & \equiv      & |(I ⊎ J → Set) → Set| \\
  & \cong       & |(I → Set) × (J → Set) → Set|\\
  & \cong       & |(I → Set) → (J → Set) → Set|\\
  & \rightarrow & |((I → Set) → J → Set) → (I → Set) → Set|\\
  & \equiv      & |IFunc* I J → IFunc I|
\end{align*}

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

It's an important observation that this construction is functorial, in that it 
lifts natural transformations in this way:


\begin{code}
_⟨_⟩M :  ∀ {I J}  (F : IFunc (I ⊎ J)) {G H : IFunc* I J}  
           →        G      =*=>^F        H                  
           →   F ⟨  G ⟩F   ⇒^F      F ⟨  H ⟩F   
F ⟨ γ ⟩M = IFunc.mor F [ (λ _ a → a) , γ ] 

\end{code}

Each of these observations generalises to |IFunc*|:

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

As you might expect, a parametrized initial algebra for |F|, if it is exists, 
will be the initial object in the category of parametrized |F|-algebras. As 
before we know that not all |IFunc* (I ⊎ J) I| functors have initial algebras. 
In the next section, however we spell out what it is for a functor to be given 
by an indexed container, and these functors are those which have such initial 
algebras.

\section{Indexed containers}

%format ◁ = "\lhd"
%format _◁_ = "\_\mbox{$\lhd$}\_"
%format ICont* = ICont *
%format ⟧* = ⟧ *
%format ◁* = ◁ *
%format _◁*_ = _ ◁* _
%format ICont.S = _ "." S
%format ICont.P = _ "." P
%format projS  = "\!." S
%format projP  = "\!." P
%format projS*  = projS *
%format projP*  = projP *

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

ICont* : (I J : Set) → Set₁
ICont* I J = J → ICont I

_◁*_ : ∀ {I J} → (S : I → Set) → (P : (i : I) → S i → J → Set) → ICont* J I
S ◁* P = λ i → S i ◁ P i

⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ C ⟧* = λ j → ⟦ C j ⟧ 

\end{code}

We will denote the two projections for an |ICont| postfix as |ICont.sh| and
|ICont.po|. Similarly for |C : ICont* I J| we have |C projS* : J → S| and 
|C projP* : (j : J) → I → C projS* j → Set|. 

%if style == code 

\begin{code}

_projS : ∀ {I} → ICont I → Set
_projS = ICont.S

_projP : ∀ {I} → (C : ICont I) → ICont.S C → I → Set
_projP = ICont.P

_projS* : ∀ {I J} → ICont* J I → I → Set
_projS* C i = ICont.S (C i)

_projP* : ∀ {I J} → (C : ICont* J I) → (i : I) → ICont.S (C i) → J → Set
_projP* C i = ICont.P (C i)


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
%format ⟦_⟧⇒* = ⟦ _ ⟧⇒*

As with plain containers morphisms in the category of indexed containers are 
given by functions on shapes and contravariant {\emph indexed} functions on 
positions:  

\begin{code}

record _⇒_ {I} (C D : ICont I) : Set₁ where
  constructor _◁_
  field 
    f : C projS → D projS
    r : (s : C projS) → (D projP $$ (f s)) -*-> (C projP $$ s)

\end{code}

Container morphisms give rise to natural transformations between the functors 
they represent:

\begin{code}

⟦_⟧⇒_ : ∀ {I} {C D : ICont I} (m : C ⇒ D) {A : I → Set} → IFunc.obj ⟦ C ⟧ A → IFunc.obj ⟦ D ⟧ A
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ⊚ r s

_⇒*_ : ∀ {J I} (C D : ICont* I J) → Set₁ 
_⇒*_ {J} C D = (j : J) → C j ⇒ D j 

⟦_⟧⇒* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) {A : I → Set} → obj* ⟦ C ⟧* A -*-> obj* ⟦ D ⟧* A
⟦ m ⟧⇒* j x = ⟦ m j ⟧⇒ x 

\end{code}

%format projf  = "\!." f
%format projr  = "\!." r
%format projf*  = "\!." f *
%format projr*  = "\!." r *

%if style == code 

\begin{code}

_projf :  ∀ {I} {C D : ICont I} (m : C ⇒ D) → C projS → D projS
_projf = _⇒_.f

_projr : ∀ {I} {C D : ICont I} (m : C ⇒ D) (s : C projS) → (D projP $$ (m projf $$ s)) -*-> (C projP $$ s)
_projr = _⇒_.r

_projf* :  ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) → C projS* $$ j → D projS* $$ j
_projf* m j = _⇒_.f (m j) 

_projr* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) (s : C projS* $$ j) → (D projP* $$ j $$ (m projf* $$ j $$ s)) -*-> (C projP* $$ j $$ s)
_projr* m j = _⇒_.r (m j) 

\end{code}

%endif

\begin{proposition}

The functor |(⟦_⟧_ , ⟦_⟧⇒_)| in |[ ICont I , IFunc I ]| is full and faithful.

\end{proposition}

\begin{proof}

This is a straight-forward generalisation of the proof for plain containers. 
The proof relies on showing that we can `quote' a natural transformation between
two container functors:

\begin{code}

q : {I : Set} (C D : ICont I) → ({A : I → Set}  → IFunc.obj ⟦  C ⟧ A  → IFunc.obj ⟦  D ⟧ A) 
                                                →              C      ⇒              D
q C D m = (proj₁ ∘ eureka) ◁ (proj₂ ∘ eureka)
 where
  eureka : (s : C projS) → IFunc.obj ⟦ D ⟧ (C projP $$ s)
  eureka s =  m (s , idd)

\end{code}

By naturality this must be the unique inverse to the extesion of a container
morphism given above.

\end{proof}

%format η^C = η ^C
%format >>=^C = >>= ^C
%format _>>=^C_ = _ >>=^C _

As with |IFunc|, we can equip |ICont| with a relative monadic structure:

\begin{code}

η^C : ∀ {I} → I → ICont I
η^C i = ⊤ ◁ λ _ i′ → i ≡ i′

_>>=^C_ : ∀ {I J} → (I → ICont J) → ICont I → ICont J
_>>=^C_ {I} H (S ◁ P) =  let  T = H projS* ;  Q = H projP* 
                         in   (IFunc.obj ⟦ S ◁ P ⟧ T) ◁
                                split s & f tilps j !* ↦ Σ (Σ I (P s)) (split i & p tilps ↦ Q i (f i p) j !m !s) !m !s  

\end{code}

\begin{proposition}

The triple |(ICont , η^C , _>>=^C_)| is a relative monad and, furthermore, this 
structure is preserved under |⟦_⟧_| 

\end{proposition}

\begin{proof}

Again, given |F : ICont I|, |G : I → ICont J|, |H : J → ICont K|:
\begin{align}
|H i|                 &\quad& \approx^{\text{\tiny{C}}} &&\quad& |H >>=^C (η^C i)|   \\
|F|                   && \approx^{\text{\tiny{C}}} &&& |η^C >>=^C F|                 \\
|H >>=^C (G >>=^C F)| && \approx^{\text{\tiny{C}}} &&& |(λ i → H >>=^C (G i)) >>=^C F| 
\end{align}

Here we work up to container isomorphism, given by a pair of a proof that that 
the sets of shapes are isomorphic and a family of proofs that all the position
sets are isomorphic (Equivalently, two mutually inverse container morphisms). 
  

\end{proof}

%format Δ^C = Δ ^C
%format Π^C = Π ^C
%format Σ^C = Σ ^C

As with indexed functors, the re-indexing |Δ^C| is defined by composition, and 
has left and right adjoints |Σ^C| and |Π^C|:

\begin{code}

Δ^C : ∀ {I J K} → (J → K) → ICont* I K → ICont* I J
Δ^C f F = F ∘ f 

Σ^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Σ^C {J} f C k =  (Σ J λ j → f j ≡ k × (C j) projS) ◁ 
                     split j & eq & s tilps ↦ C projP* $$ j $$ s !m !s
 
Π^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Π^C {J} f C k =  ((j : J) → f j ≡ k → (C j) projS) ◁ 
                     λ s i → Σ J λ j → Σ (f j ≡ k) λ eq → (C j) projP $$ (s j eq)$$ i 

\end{code}

\begin{proposition}
|Σ^F| and |Π^F| are left and right adjoint to re-indexing (|Δ^F|), and 
are preserved under |⟦_⟧_|.
\end{proposition}

%format ✧ = "\lozenge"

%format ⟩C = ] ^C
%format ⟩C*  = ] "^{\text{\tiny{C}}^{\star}}"
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format _⟨_⟩C* = _ ⟨ _ ⟩C*
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 

%format PI = P "^{" I "}"
%format PJ = P "^{" J "}" 

Before we build the initial algebras of, it will help to define their partial
application. 

\begin{code}

_⟨_⟩C : ∀ {I J} → ICont (I ⊎ J) → ICont* J I → ICont J
_⟨_⟩C {I} {J} (S ◁ P) D = 
  let  PI  : S  → I  → Set            ;  PI  s  i  = P s (inj₁ i) 
       PJ  : S  → J  → Set            ;  PJ  s  j  = P s (inj₂ j) 
       T   : I → Set                  ;  T      i  = (D i) projS
       Q   : (i : I) → T i → J → Set  ;  Q      i  = (D i) projP
  in   IFunc.obj ⟦ S ◁ PI ⟧ T ◁ (split s & f tilps j !* ↦ PJ s j ⊎ (Σ I λ i → Σ (PI s i) λ p → Q i (f i p) j) !m !s)

\end{code}

The composite container has shapes given by an shape |s : S| and an assigment of |T| 
shapes to |PI s| positions. Positions are then a choice between 
a |J|-indexed position, or a pair of an |I|-indexed position, and a |Q| position
\emph{underneath} the appropriate |T| shape. 

%if style==code

\begin{code}

_⟨_⟩C* : ∀ {I J K} → ICont* (I ⊎ J) K → ICont* J I →  ICont* J K
_⟨_⟩C* C D k = (C k) ⟨ D ⟩C

\end{code}

%endif

As with indexed functors, this construction is functorial in its second 
argument, and lifts container morphisms in this way:

\begin{code}

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* J I} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  split s & f tilps ↦ (s , λ i p → (γ i) projf $$ (f i p)) !m !s) ◁ 
     split s & f tilps j !* ↦ [ inj₁ , (split i & p & q tilps ↦ inj₂ (i , p , (γ i) projr $$ (f i p) $$ j $$ q) !m !s) ] !m !s 

\end{code}



\section{Initial Algebras of Indexed Containers}

We will now examine how to construct the initial algebra of a container of the form |F : ICont* (I ⊎ J) I|. The shapes of such a container are an |I|-indexed family of |Set|s and the positions are in |(i : I) → S i → I ⊎ J → Set|; we will treat these position as two separate entities, those positions indexed by |I| (|PI : (i : I) → S i → I → Set|) and those by |J| (|PJ : (i : I) → S i → I → Set|).

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

This mirrors the construction for plain containers, where we can view ordinary |W| types as the initial algebra of a container functor.

Positions are given by paths through such a tree, terminated by a non-recursive |PJ|:

\begin{code}

data Path  {I J : Set} (S : I → Set)  
           (PI  : (i : I) → S i → I  → Set) 
           (PJ  : (i : I) → S i → J  → Set) 
           : (i : I) → WI S PI i → J → Set where
  here   : ∀ {i s f j} →         PJ   i s j    → Path S PI PJ i   (sup (s , f)) j
  there  : ∀ {i s f j} i′ (p :   PI   i s i′)  → Path S PI PJ i′  (f i′ p) j 
                                               → Path S PI PJ i   (sup (s , f)) j  

\end{code}

This exchoes the partial application construction where positions were given by a |PJ| position at the top level, or a pair of a |PJ| position and a sub |Q| position. Here the |Q| positions are recursive |Path| positions. Indeed we can mediate between a |Path| view of the position sets and a partial applicaton syle position:

\begin{code}

Path' : ∀ {I J} S (PI : (i : I) → S i → I  → Set) → (PJ : (i : I) → S i → J  → Set) (i : I) →  WI S PI i → J → Set
Path' {I} S PI PJ i (sup (s , f)) j = PJ i s j ⊎ (Σ I λ i′ → Σ (PI i s i′) λ p → Path S PI PJ i′ (f i′ p) j)

path : ∀ {I J S PI PJ} {i : I} {x : WI S PI i} {j : J} → Path S PI PJ i x j → Path' S PI PJ i x j
path (here p)        = inj₁ p
path (there i′ p q)  = inj₂ (i′ , (p , q))

\end{code}

%format μ = "\mu"
%format μ^C = μ ^C

We can now give the object part of the patrametrized intial algebra of a container, given by:

\begin{code}

μ^C : {I J : Set} → ICont* (I ⊎ J) I → ICont* J I
μ^C {I} {J} F = 
  let  S = F projS*  
       PI  : (i : I) → S i → I  → Set ;  PI  i s i′  = F projP* $$ i $$ s $$ (inj₁ i′) 
       PJ  : (i : I) → S i → J  → Set ;  PJ  i s j   = F projP* $$ i $$ s $$ (inj₂ j)
  in   WI S PI ◁* Path S PI PJ
\end{code}

%format in^C = "\Varid{in}" ^C
%format fold^C = fold ^C

The algebra map is a container morphism from the partial aplication of |F| and its parametrised initial algebra, to the initial algebra, given by the algebra map of |WI| (|sup|) and our mediation funtion |path|:

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) I) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F i = sup ◁ λ _ _ p → path p 

\end{code}

\begin{code}
 
fold^C : ∀ {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} {F} G m i = ffold i ◁ rfold i 
    where  S = F projS*  
           PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = F projP* $$ i $$ s $$ (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = F projP* $$ i $$ s $$ (inj₂ j)
           Q = G projP*
           ffold = WIfold (m projf*)
           rfold :  (i : I) (s : WI S PI i) (j : J) → Q i (ffold i s) j → Path S PI PJ i s j
           rfold i (sup (s , f)) j p  with m projr* $$ i $$ (s , _) $$ j $$ p
           rfold i (sup (s , f)) j p  | inj₁ x               = here x
           rfold i (sup (s , f)) j p  | inj₂ (i′ , (q , y))  = there i′ q (rfold i′ (f i′ q) j y)

\end{code}

\section{Strictly Positive Types}

\section{Conclusions}


\bibliographystyle{plain}
\bibliography{paper}

\end{document}
