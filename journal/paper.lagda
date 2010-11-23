%if style==code

\begin{code}

{-# OPTIONS --type-in-type #-}

module paper where

open import Data.Unit
open import Data.Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality

infixl 0  _$$_

_$$_ : ∀ {A : Set} {B : A → Set} →
      ((x : A) → B x) → ((x : A) → B x)
f $$ x = f x

\end{code}

%endif

%format $$ = "\!" 

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

%format -*-> = "\mathbin{\dot{\rightarrow}}"
%format _-*->_ = _ "\dot{\rightarrow}" _
%format _⊚_ = _ "\dot{\circ}" _ 
%format ⊚ = "\mathbin{\dot{\circ}}" 

\begin{code}
_-*->_ : {I : Set} -> (A B : I -> Set) -> Set
_-*->_ {I} A B = (i : I) -> A i -> B i

_⊚_ : {I : Set} {A B C : I → Set} → B -*-> C → A -*-> B → A -*-> C
f ⊚ g = λ i → (f i) ∘ (g i)
\end{code}

\subsection{Containers}

\section{Indexed Functors}

%if style==code

\begin{code}



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

%format ^F = "^{\text{\tiny F}}"
%format η = "\eta"
%format η^F = η ^F
%format >>=^F = >>= ^F
%format _>>=^F_ = _ >>=^F _

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

%format obj* = 
%format mor* = 

%format Π = "\Pi"
%format Π^F = Π ^F
%format Σ^F = Σ ^F


\begin{code}

Σ^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Σ^F {J} f F k = 
   record  {  obj  =  λ A → Σ J λ j → f j ≡ k × obj* F A j 
           ;  mor  =  λ m →  uncurry λ j → uncurry λ p x → (j , (p , mor* F m j x))  }
 
Π^F : ∀ {J I K} → (J → K) → IFunc* I J → IFunc* I K
Π^F {J} f F k = 
   record  {  obj  =  λ A → (j : J) → f j ≡ k → obj* F A j 
           ;  mor  =  λ m f j p → mor* F m j (f j p) }
\end{code}

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

_⟨_⟩M :  ∀ {I J}  (F : IFunc (I ⊎ J)) {G H : IFunc* I J} → 
                  (  {A : I → Set} → obj*            G      A  -*-> obj*                  H      A) →  
                     {A : I → Set} → IFunc.obj (F ⟨  G ⟩F)  A  →          IFunc.obj (F ⟨  H ⟩F)  A 
F ⟨ γ ⟩M = IFunc.mor F [ (λ _ a → a) , γ ] 

\end{code}

\[
\xymatrix{
\mbox{|F ⟨ G ⟩F|}  \ar[r]^{\quad\mbox{|α|}} 
\ar[d]_{\mbox{|F ⟨ γ ⟩M|}} & \mbox{|G|} \ar[d]^{\mbox{|γ|}}\\
\mbox{|F ⟨ H ⟩F|} \ar[r]^{\quad\mbox{|β|}} & \mbox{|H|}}
\]

\section{Indexed containers}

%format ◁ = "\lhd"
%format _◁_ = "\_\mbox{$\lhd$}\_"
%format ICont* = ICont *
%format ⟧* = ⟧ *
%format ICont.S = _ "." S
%format ICont.P = _ "." P
%format projS  = "\!." S
%format projP  = "\!." P


\begin{code}

record ICont (I : Set) : Set where
  constructor _◁_
  field
    S : Set
    P : S → I → Set

⟦_⟧ : ∀ {I} → ICont I → IFunc I
⟦_⟧ {I} (S ◁ P) = 
  record  {  obj  = λ A  → Σ S (λ s → (i : I) → P s i → A i)
          ;  mor  = λ m  → uncurry (λ s f → (s , m ⊚ f)) }

ICont* : (I J : Set) → Set
ICont* I J = J → ICont I

⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ C ⟧* = λ j → ⟦ C j ⟧ 

\end{code}

%if style == code 

\begin{code}

_projS : ∀ {I} → ICont I → Set
_projS = ICont.S

_projP : ∀ {I} → (C : ICont I) → ICont.S C → I → Set
_projP = ICont.P

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
η^C i = ⊤ ◁ λ _ i' → i ≡ i'

_>>=^C_ : ∀ {I J} → (I → ICont J) → ICont I → ICont J
_>>=^C_ {I} H (S ◁ P) =    (IFunc.obj ⟦ S ◁ P ⟧ (ICont.S ∘ H)) ◁
                           uncurry (λ s f j → Σ  (Σ I λ i → P s i) (uncurry (λ i p → (H i) projP $$ (f i p) $$ j))) 

\end{code}

%format Π^C = Π ^C
%format Σ^C = Σ ^C

\begin{code}

Σ^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Σ^C {J} f C k =  (Σ J λ j → f j ≡ k × (C j) projS) ◁ 
                     uncurry λ j → uncurry λ p s i → (C j) projP $$ s $$ i
 
Π^C : ∀ {J I K} → (J → K) → ICont* I J → ICont* I K
Π^C {J} f C k =  ((j : J) → f j ≡ k → (C j) projS) ◁ 
                     λ s i → Σ J λ j → Σ (f j ≡ k) λ p → (C j) projP $$ (s j p)$$ i 

\end{code}

%format ⟩C = ] ^C
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 

%format PI = P "^{" I "}"
%format PJ = P "^{" J "}" 
\begin{code}

_⟨_⟩C : ∀ {I J} → ICont (I ⊎ J) → ICont* I J →  ICont I
_⟨_⟩C {I} {J} (S ◁ P) D = 
  let  PI  : S  → I  → Set  ;  PI  = λ s → P s ∘ inj₁ 
       PJ  : S  → J  → Set  ;  PJ  = λ s → P s ∘ inj₂ 
  in   IFunc.obj ⟦ S ◁ PJ ⟧ (ICont.S ∘ D) ◁ 
       uncurry λ s f i → PI s i ⊎ Σ J λ j → Σ (PJ s j) λ p → (D j) projP $$ (f j p) $$ i

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* I J} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (uncurry λ s f → (s , λ j p → (γ j) projf $$ (f j p))) ◁ 
  uncurry (λ s f i → [ inj₁ , (uncurry λ j → uncurry λ p q → inj₂ (j , (p , ((γ j) projr $$ (f j p) $$ i $$ q)))) ]) 
\end{code}



\section{Initial Algebras of Indexed Containers}

\begin{code}

data WI {I : Set} (S : I → Set) (P : (i : I) → S i → I → Set) : I → Set where
  sup : ∀ {i} → (s : S i) → (P i s -*-> WI S P) → WI S P i


data Path 


\end{code}

\section{Strictly Positive Types}

\section{Conclusions}


\end{document}
