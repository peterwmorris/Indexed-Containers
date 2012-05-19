%if style == newcode 

\begin{code}

module cont where

open import Product
open import Function

open import common
open import tt

\end{code}

%endif

\subsection{Containers in a Nutshell}

%format ◁ = "\lhd"
%format _◁_ = _ ◁ _
%format Func.obj = "\!"
%format Func.mor = "\!"

Initial algebra semantics is useful for providing a generic analysis
of inductive types based upon concepts such as constructors,
functorial map and structured recursion operators. However, it cannot
say whether inductive types actually exist, and it falls short of
providing a systematic characterisation of generic operations such as
equality or the zipper~\cite{huet:zipper,conor:derivative}. To address
this problem, we proposed in previous work to consider only a certain
class of functors, namely those arising from
containers~\cite{alti:cont-tcs,alti:fossacs03}. Since indexed
containers build upon containers, we recall the salient information
about containers. A (unary) container is given by a set of shapes |S|
and a family of positions |P| assigning, to each shape, the set of
positions where data can be stored in a data structure of that shape.

\begin{code}
record Cont : Set₁ where
  constructor _◁_ 
  field 
    S : Set
    P : S → Set
\end{code}

This shapes and positions metaphor is very useful in developing
intuitions about containers. For example, every container |S ◁ P|
gives rise to a functor which maps a set |A| to the the set of pairs
consisting of a choice of a shape |s : S| and a function assigning to
every position |p : P s| for that shape, an element of |A| to be
stored at that position. This intuition is formalised by the following
definition.

\begin{code}
⟦_⟧ : Cont → Func
⟦ S ◁ P ⟧ = record  { obj  = λ A → Σ* s ∶ S *Σ (P s → A)
                    ; mor  = λ m → λ { (s , f) → (s , m ∘ f) } 
                    }

\end{code} For example the list functor arises from a container whose
shapes are given by the natural numbers (representing the list's
length) and the positions for a shape |n : ℕ| are given by |Fin
n|. This reflects the fact that a list of length |n : ℕ| has |Fin n|
locations or positions where data may be stored.

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

The motivation for containers was to find a representation of well
behaved functors. Since natural transformations are the semantic
representation of polymorphic functions, it is also natural to seek a
representation of natural transformations in the language of
containers. We showed in our previous work that a natural
transformation between two functors arising as containers can be
represented as morphisms between containers as follows.

\begin{code}

record _⇒_ (C D : Cont) : Set where
  constructor _◁_
  field
    f : C projSh → D projSh 
    r : (s : C projSh) → D projPo $$ (f s) → C projPo $$ s
\end{code}


As promised, such container morphisms represent natural
transformations as the following definition shows:

\begin{code}

⟦_⟧⇒ : ∀ {C D} → C ⇒ D → ∫ A ** (Func.obj ⟦ C ⟧ A → Func.obj ⟦ D ⟧ A)
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ∘ r s  

\end{code} Rather surprisingly we were able to prove that the
representation of natural transformations as container morphisms is a
bijection, that is every natural transformation between functors
arising from containers is uniquely represented as a container
morphism.  Technically, this can be stated by saying that Containers
and their morphisms form a category which is a full and faithful
sub-category of the functor category. We have also shown that the
category of containers is cartesian closed (\cite{tax:cie10}, and is
closed under formation of co-products, products and a number of other
constructions. Most important of these is the fact that container
functors (ie functors arising from containers) have initial algebras. Indeed,
these are exactly the |W| types we know well from Type-Theory,
which we can be equivalently defined to be:

%format WW = W

\begin{code}

data WW (S : Set) (P : S → Set) : Set where
  sup : Func.obj ⟦ S ◁ P ⟧ (WW S P) → WW S P
  
\end{code}

%format μ = "\mu"

However, we have also shown that for |n|-ray containers (containers
with |n| position sets), it is possible to define a
\emph{parameterised} initial algebra construction |μ : ∀ {n} → Cont
(suc n) → Cont n|. This allows us to model a broad range of nested and
mutual types as containers. Further details can be found in the paper
on containers cited above.

