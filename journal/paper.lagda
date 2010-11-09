%if style==code

\begin{code}

{-# OPTIONS --type-in-type #-}

module paper where

open import Data.Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality


\end{code}

%endif

\documentclass[a4paper]{article}

%include lhs2TeX.fmt
%include agda.fmt

%format → = "\rightarrow"
%format ∀ = "\forall{}"
%format λ = "\lambda" 
%format ∘ = "\ensuremath{\mbox{$\circ$}}"

%format ⊎ = "\uplus"
%format inj₁ = inl
%format inj₂ = inr

%format Σ = "\Sigma"
%format × = "\times"
%format proj₁ = "\pi_{0}"
%format proj₂ = "\pi_{1}"

%format ≡ = "\equiv"

%format forall = "\forall{}"
%format -*-> = "\dot{\rightarrow}"
%format _-*->_ = _ -*-> _

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

\begin{code}

_-*->_ : {I : Set} -> (A B : I -> Set) -> Set
_-*->_ {I} A B = (i : I) -> A i -> B i

\end{code}

\subsection{Containers}

\section{Indexed Functors}

%if style==code

\begin{code}

module IFunc where

\end{code}

%endif

%format IFunc.obj = "\!"
%format IFunc.mor = "\!"

\begin{code}

 record IFunc (I : Set) : Set where
   field
     obj : (A : I -> Set) -> Set
     mor : forall {A B} -> (A -*-> B) -> obj A -> obj B

 \end{code}

%format ^F = "^{F}"
%format η = "\eta"
%format η^F = η ^F
%format >>=^F = >>= ^F
%format _>>=^F_ = "\_" >>=^F "\_" 

\begin{code}

 η^F : ∀ {I} → I → IFunc I
 η^F i = record { obj = λ A → A i; mor = λ f → f i }

 _>>=^F_ : ∀ {I J} → (I → IFunc J) → IFunc I → IFunc J
 H >>=^F F = 
   record  {  obj  =  λ A  → IFunc.obj F (λ i  → IFunc.obj  (H i)  A  )
           ;  mor  =  λ f  → IFunc.mor F (λ i  → IFunc.mor  (H i)  f  ) }

\end{code}

We adopt the convention that the projections |obj| and |mor| are silent, \emph{i.e.} depend on the context |F :  IFunc I| can stand for either the functions actions on objects, or on morphisms.

%format * = "^{\star}" 
%format IFunc* = IFunc * 
%format obj* = obj *
%format mor* = mor *

\begin{code}

 IFunc* : (I J : Set) → Set 
 IFunc* I J = J → IFunc I 

 obj* : ∀ {I J} → IFunc* I J → (I → Set) → J → Set
 obj* F A j    = IFunc.obj (F j) A

 mor* :  ∀ {I J A B} (F : IFunc* I J) → A -*-> B → obj* F A -*-> obj* F B
 mor* F m j  = IFunc.mor (F j) m 

\end{code}

Again, we will omit calls to |obj*| and |mor*| when inferrable from the context in which they appear.

%format obj* = "\!"
%format mor* = "\!"



%format Π = "\Pi"
%format Π^F = Π ^F
%format Σ^F = Σ ^F


\begin{code}

 Σ^F : ∀ {I J K} → (J → K) → IFunc* I J → IFunc* I K
 Σ^F {J = J} f F k = 
   record  {  obj  =  λ A → Σ J λ j → f j ≡ k × obj* F A j 
           ;  mor  =  λ m → < proj₁ ,  < proj₁ ∘ proj₂ , mor* F m _ ∘ proj₂ ∘ proj₂ > >   }
 
 Π^F : ∀ {I J K} → (J → K) → IFunc* I J → IFunc* I K
 Π^F {J = J} f F k = 
   record  {  obj  =  λ A → (j : J) → f j ≡ k → obj* F A j 
           ;  mor  =  λ m f j p → mor* F m j (f j p) }
\end{code}

%format ⟨ = [
%format ⟩F = ] ^F
%format _⟨_⟩F = "\_" ⟨ "\_" ⟩F

\begin{code}

 _⟨_⟩F : ∀ {I J} → IFunc (I ⊎ J) → IFunc* I J →  IFunc I
 F ⟨ G ⟩F  = 
  record  {  obj  =  λ A  → IFunc.obj F [ A  , obj*  G A  ]
          ;  mor  =  λ f  → IFunc.mor F [ f  , mor*  G f  ] }

\end{code}



\section{Indexed containers}

\section{Initial Algebras of Indexed Containers}

\section{Strictly Positive Types}

\section{Conclusions}


\end{document}
