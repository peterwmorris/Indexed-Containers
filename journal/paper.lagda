%if style==code

\begin{code}

{-# OPTIONS --type-in-type #-}

module paper where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality

infixl 20  _$$_

unc : {A : Set} {B : A → Set} {C : Σ A B → Set} →
      ((x : A) → (y : B x) → C (x , y)) →
      ((p : Σ A B) → C p)
unc = uncurry

ids : ∀ {A} → A → A
ids = id 

idt : ∀ {A} → A → A
idt = id 

infixr 102 ↦_!m

↦_!m : ∀ {A} → A → A
↦_!m = id 

infixr 103 split_!s

split_!s : ∀ {A} → A → A
split_!s = id 

infixr 101 unc
infixr 102 ids
infixr 102 idt

syntax unc (λ x → t) = x & t
syntax ids (λ x → t) = x tilps t 
syntax idt (λ x → t) = x !* t 

_$$_ : ∀ {A : Set} {B : A → Set} →
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


%format -*-> = "\mathbin{\dot{\rightarrow}}"
%format -**-> = "\mathbin{\dot{\rightarrow}}"
%format _-*->_ = _ "\dot{\rightarrow}" _
%format _-**->_ = _ "\dot{\rightarrow}" _
%format _⊚_ = _ "\dot{\circ}" _ 
%format ⊚ = "\mathbin{\dot{\circ}}" 
%format idd = "\dot{" id "}"

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

Fam : Set → Set
Fam I = I → Set

\end{code}

%endif

An |I|-indexed functor is then a functor from |Fam I| to |Set|, given by:

\begin{code}

record IFunc (I : Set) : Set where
  field
    obj : (A : Fam I) -> Set
    mor : ∀ {A B} -> (A -*-> B) -> obj A -> obj B

\end{code}

Such that both |idd| is mapped to |id| and |_⊚_| to |_∘_| under the action of 
|mor|. We adopt the convention that the projections |obj| and |mor| are silent, 
\emph{i.e.} depending on the context |F :  IFunc I| can stand for either the 
functors action on objects, or on morphisms.

%format ^F = "^{\text{\tiny F}}"
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

Note, however, that since |IFunc : Seti → Setsi| it cannot be a true monad. 
Instead, we can describe it as a monad relative\cite{relmonads} to the lifting 
|↑ : Seti → Setsi| which is trivially a functor.

%format * = "^{\star}" 
%format IFunc* = IFunc * 
%format obj* = obj *
%format mor* = mor *

The opposite of the Kliesli category associated with |IFunc| has objects 
|I , J : Set| and morphisms given by |J|-indexed families of |I|-indexed 
functors. We denote this notion of indexed functor |IFunc*|: 

\begin{code}

IFunc* : (I J : Set) → Set 
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
|F′ n X = F (1+ n) X|. Or simply |F′ = Δ^F (1+) F|.

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

We can employ the |Σ^F| construction to buld a functor whose fixed point is 
|Fin| where we want a solution to the equation 
|F′ n X = Σ Nat λ m → n ≡ 1+ m × ⊤ + F m X| or |F′ = Σ^F (1+) F|. |Π^F| is less
obviously useful, but is necessary to be able to construct infinitely branching 
trees. We also note that finite co-products and 
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
\mbox{|mor* F A|}  \ar[r]^{\;\mbox{|α|}} 
\ar[d]_{\mbox{|mor* F f|}} & \mbox{|A|} \ar[d]^{\mbox{|a|}}\\
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
_⟨_⟩M :  ∀ {I J}  (F : IFunc (I ⊎ J)) {G H : IFunc* I J} → 
                  (  ∀ {A} → obj*            G      A  -*-> obj*                  H      A) →  
                     ∀ {A} → IFunc.obj (F ⟨  G ⟩F)  A  →          IFunc.obj (F ⟨  H ⟩F)  A 
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

_⟨_⟩M* :  ∀ {I J K}  (F : IFunc* (I ⊎ J) K) {G H : IFunc* I J} → 
                     (  ∀ {A} → obj*       G       A  -*-> obj*       H       A) →  
                        ∀ {A} → obj* (F ⟨  G ⟩F*)  A  -*-> obj* (F ⟨  H ⟩F*)  A 
_⟨_⟩M* F {G} {H} γ = λ k → _⟨_⟩M  (F k) {G} {H} γ  

\end{code}

A parametrized algebra |F : IFunc* (I ⊎ J) I| is, then, a indexed-functor 
|G : IFunc J I| and a natural transformation
|α : ∀ {A} → F ⟨ G ⟩F* A -*-> G A|. A morphism between two such algebras 
|(G , α)| and |(H , β)| is a natural transformation |γ : ∀ {A} → G A -*-> H A| 
such that the follow diagram commutes:

\[
\xymatrix{
\mbox{|F ⟨ G ⟩F*|}  \ar[r]^{\quad\mbox{|α|}} 
\ar[d]_{\mbox{|F ⟨ γ ⟩M*|}} & \mbox{|G|} \ar[d]^{\mbox{|γ|}}\\
\mbox{|F ⟨ H ⟩F*|} \ar[r]^{\quad\mbox{|β|}} & \mbox{|H|}}
\]

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

\begin{code}

record ICont (I : Set) : Set where
  constructor _◁_
  field
    S : Set
    P : S → I → Set

⟦_⟧ : ∀ {I} → ICont I → IFunc I
⟦_⟧ {I} (S ◁ P) = 
  record  {  obj  = λ A  → Σ S (λ s → (i : I) → P s i → A i)
          ;  mor  = λ m  → split s & f tilps ↦ (s , m ⊚ f) !m !s }

ICont* : (I J : Set) → Set
ICont* I J = J → ICont I

_◁*_ : ∀ {I J} → (S : I → Set) → (P : (i : I) → S i → J → Set) → ICont* J I
S ◁* P = λ i → S i ◁ P i

⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ C ⟧* = λ j → ⟦ C j ⟧ 

\end{code}

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

%format ⇒ = "\Rightarrow"
%format _⇒_ = _ ⇒ _
%format ⇒* = ⇒ *
%format _⇒*_ = _ ⇒ * _
%format ⟧⇒ = ⟧ "\mbox{$\!^{\Rightarrow}$}"
%format ⟦_⟧⇒ = ⟦ _ ⟧⇒
%format ⟧⇒* = ⟧ "\mbox{$\!^{\Rightarrow^{\!\star}}$}"
%format ⟦_⟧⇒* = ⟦ _ ⟧⇒*

\begin{code}

record _⇒_ {I} (C D : ICont I) : Set where
  constructor _◁_
  field 
    f : C projS → D projS
    r : (s : C projS) → (D projP $$ (f s)) -*-> (C projP $$ s)

⟦_⟧⇒_ : ∀ {I} {C D : ICont I} (m : C ⇒ D) {A : I → Set} → IFunc.obj ⟦ C ⟧ A → IFunc.obj ⟦ D ⟧ A
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ⊚ r s

_⇒*_ : ∀ {J I} (C D : ICont* I J) → Set 
_⇒*_ {J} C D = (j : J) → C j ⇒ D j 

⟦_⟧⇒* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) {A : I → Set} → obj* ⟦ C ⟧* A -*-> obj* ⟦ D ⟧* A
⟦ m ⟧⇒* j x = ⟦ m j ⟧⇒ x 

\end{code}

%format projf  = "\!." f
%format projr  = "\!." r

%if style == code 

\begin{code}

_projf :  ∀ {I} {C D : ICont I} (m : C ⇒ D) → C projS → D projS
_projf = _⇒_.f

_projr : ∀ {I} {C D : ICont I} (m : C ⇒ D) (s : C projS) → (D projP $$ (m projf $$ s)) -*-> (C projP $$ s)
_projr = _⇒_.r

\end{code}

%endif

%format ^C = "^{\text{\tiny C}}"
%format η^C = η ^C
%format >>=^C = >>= ^C
%format _>>=^C_ = _ >>=^C _

\begin{code}

η^C : ∀ {I} → I → ICont I
η^C i = ⊤ ◁ λ _ i′ → i ≡ i′

_>>=^C_ : ∀ {I J} → (I → ICont J) → ICont I → ICont J
_>>=^C_ {I} H (S ◁ P) =  let  T = H projS* ;  Q = H projP* 
                         in   (IFunc.obj ⟦ S ◁ P ⟧ T) ◁
                                split s & f tilps j !* ↦ Σ (Σ I (P s)) (split i & p tilps ↦ Q i (f i p) j !m !s) !m !s  

\end{code}

%format Δ^C = Δ ^C
%format Π^C = Π ^C
%format Σ^C = Σ ^C

|Δ^C| has left and right adjoints:

\begin{code}

Σ^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Σ^C {J} f C k =  (Σ J λ j → f j ≡ k × (C j) projS) ◁ 
                     split j & p & s tilps ↦ C projP* $$ j $$ s !m !s
 
Π^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Π^C {J} f C k =  ((j : J) → f j ≡ k → (C j) projS) ◁ 
                     λ s i → Σ J λ j → Σ (f j ≡ k) λ p → (C j) projP $$ (s j p)$$ i 

\end{code}

%format ✧ = "\lozenge"

%format ⟩C = ] ^C
%format ⟩C*  = ] "^{\text{\tiny{C}}^{\star}}"
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format _⟨_⟩C* = _ ⟨ _ ⟩C*
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 

%format PI = P "^{" I "}"
%format PJ = P "^{" J "}" 
\begin{code}

✧   : ∀  {I J S} {T : I → Set} (Q : (i : I) → T i → J → Set) 
         (PI : S → I → Set) (PJ : S → J → Set) →
         IFunc.obj ⟦ S ◁ PI ⟧ T → J → Set
✧  {I} Q PI PJ (s , f) j = PJ s j ⊎ Σ I λ i → Σ (PI s i) λ p → Q i (f i p) j

_⟨_⟩C : ∀ {I J} → ICont (I ⊎ J) → ICont* J I → ICont J
_⟨_⟩C {I} {J} (S ◁ P) D = 
  let  PI  : S  → I  → Set            ;  PI  s  i  = P s (inj₁ i) 
       PJ  : S  → J  → Set            ;  PJ  s  j  = P s (inj₂ j) 
       T   : I → Set                  ;  T      i  = (D i) projS
       Q   : (i : I) → T i → J → Set  ;  Q      i  = (D i) projP
  in   IFunc.obj ⟦ S ◁ PI ⟧ T ◁ ✧ Q PI PJ


_⟨_⟩C* : ∀ {I J K} → ICont* (I ⊎ J) K → ICont* J I →  ICont* J K
_⟨_⟩C* C D k = (C k) ⟨ D ⟩C


_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* J I} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  split s & f tilps ↦ (s , λ i p → (γ i) projf $$ (f i p)) !m !s) ◁ 
     split s & f tilps j !* ↦ [ inj₁ , (split i & p & q tilps ↦ inj₂ (i , p , (γ i) projr $$ (f i p) $$ j $$ q) !m !s) ] !m !s 

\end{code}



\section{Initial Algebras of Indexed Containers}

\begin{code}

data WI {I : Set} (S : I → Set) (PI : (i : I) → S i → I → Set) : I → Set where
  sup : obj* ⟦ S ◁* PI ⟧* (WI S PI)  -**-> WI S PI 

WIfold :  ∀ {I} {X : I → Set} {S : I → Set} {PI : (i : I) → S i → I → Set} →
          (obj* ⟦ S ◁* PI ⟧* X) -*-> X → WI S PI -*-> X
WIfold f i (sup (s , g)) = f i (s , λ i′ p → WIfold f i′ (g i′ p))

Path :  {I J : Set} (S : I → Set)  (PI  : (i : I) → S i → I  → Set) 
                                   (PJ  : (i : I) → S i → J  → Set) 
        (i : I) → WI S PI i → J → Set 
Path S PI PJ i (sup (s , f)) j = ✧ (Path S PI PJ) (PI i) (PJ i) (s , f) j  

\end{code}

%format μ = "\mu"
%format μ^C = μ ^C

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

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) I) → (F ⟨ μ^C F ⟩C*) ⇒* μ^C F
in^C F i = sup ◁ (λ _ _ p → p) 

fold^C : ∀ {I J} {F : ICont* (I ⊎ J) I} (G : ICont* J I) → F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} {F} G m i = ffold i ◁ rfold i 
    where  S = F projS*  
           PI  :  (i : I) → S i → I  → Set ;  PI  i s i′  = F projP* $$ i $$ s $$ (inj₁ i′) 
           PJ  :  (i : I) → S i → J  → Set ;  PJ  i s j   = F projP* $$ i $$ s $$ (inj₂ j)
           Q = G projP*
           ffold = WIfold (λ i → (m i) projf) 
           rfold :  (i : I) (s : WI S PI i) (j : J) → Q i (ffold i s) j → Path S PI PJ i s j
           rfold i (sup (s , f)) j p  with (m i) projr $$ (s , _) $$ j $$ p
           rfold i (sup (s , f)) j p  | inj₁ x               = inj₁ x
           rfold i (sup (s , f)) j p  | inj₂ (i′ , (q , y))  = inj₂ (i′ , q , rfold i′ (f i′ q) j y)


\end{code}

\section{Strictly Positive Types}

\section{Conclusions}


\end{document}
