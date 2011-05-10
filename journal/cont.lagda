%if style == newcode 

\begin{code}

module cont where

open import Product
open import Function

open import common
open import tt
open import func

\end{code}

%endif

\subsection{Containers}

%format ◁ = "\lhd"
%format _◁_ = _ ◁ _
%format Func.obj = "\!"
%format Func.mor = "\!"

The initial algebra semantics is useful to provide a generic
analysis of inductive types exploiting generic concepts such as
constructors and functorial map. However, it cannot say whether such inductive
types actually exist, and it falls short of providing a systematic
characterisation of generic operations such as equality or the
zipper~\cite{huet:zipper,conor:derivative}. 

In previous
work, \cite{alti:cont-tcs,alti:fossacs03}, we have proposed the notion of a container
type: A (unary) container is given by a set of shapes |S| and a
family of positions |P| assigning, to each shape, the set
of positions where data can be stored in a data structure of that
shape.

\begin{code}
record Cont : Set₁ where
  constructor _◁_ 
  field 
    S : Set
    P : S → Set
\end{code}

Every container |S ◁ P|  gives rise to a functor:
\begin{code}
⟦_⟧ : Cont → Func
⟦ S ◁ P ⟧ = record  { obj  = λ A → Σ* s ∶ S *Σ (P s → A)
                    ; mor  = λ m → split s & f tilps ↦ (s , m ∘ f)  !m !s 
                    }

\end{code}

For example the list functor is a container, its shapes are given by the natural numbers (representing the list's length) and the positions for a shape |n : ℕ| are given by a finite set of size |n|. 

%format projSh = "\!." S
%format projPo = "\!." P

%if style == newcode

\begin{code}

_projSh : Cont → Set
_projSh (S ◁ P) = S

_projPo : (C : Cont) → C projSh → Set
_projPo (S ◁ P) = P

\end{code}

%endif

%format ⇒ = "\Rightarrow"
%format _⇒_ = _ ⇒ _
%format ⟧⇒ = ⟧ "\mbox{$\!^{\Rightarrow}$}"
%format ⟦_⟧⇒ = ⟦ _ ⟧⇒

We define morphisms of containers, this can be derived from the specification that embedding should be full and faithful using the Yoneda lemma:

\begin{code}

record _⇒_ (C D : Cont) : Set where
  constructor _◁_
  field
    f : C projSh → D projSh 
    r : (s : C projSh) → D projPo $$ (f s) → C projPo $$ s

⟦_⟧⇒ : ∀ {C D} → C ⇒ D → ∫ A ** (Func.obj ⟦ C ⟧ A → Func.obj ⟦ D ⟧ A)
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ∘ r s  

\end{code}

The category of containers is a full and faithful sub-category of the functor category. We have also shown that the category of containers is cartesian closed (\cite{txa:cie10}, and is closed under formation of co-products.

Container functors have initial algebras, indeed these are exactly the |W| types we know well from Type-Theory, which we can be equivalently defined to be:

%format WW = W

\begin{code}

data WW (S : Set) (P : S → Set) : Set where
  sup : Func.obj ⟦ S ◁ P ⟧ (WW S P) → WW S P
  
\end{code}

%format μ = "\mu"

However, we have also shown that for |n|-ary containers (containers with |n| position sets), it is possible to define a \emph{parameterised} initial algebra construction |μ : ∀ {n} → Cont (suc n) → Cont n|. This allows us to model a broad range of nested and mutual types as containers.

