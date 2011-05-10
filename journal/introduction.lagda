%if style == code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module introduction where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.HeterogeneousEquality
-- open import Data.List
open import Function

open import common
open import tt


\end{code}

%endif

\section{Introduction}




\noindent Inductive datatypes are a central feature of modern Type Theory
(e.g. COQ~\cite{CIC}) or functional programming (e.g. 
Haskell\footnote{Here we shall view Haskell as an approximation of strong
  functional programming as proposed by Turner \cite{sfp} and ignore
non-termination.})

Examples include the natural numbers al Peano:
\begin{code}

data ℕ : Set where
  zero  : ℕ
  suc   : (n : ℕ) → ℕ

\end{code}
the set of lists indexed by any given set:
\begin{code}

data List (A : Set) : Set where
  []   :               List A
  _∷_  : A → List A →  List A

\end{code}
and the set of  de Bruijn $\lambda$-terms:
\begin{code}

data Lam : Set where
  var  : (n : ℕ)      → Lam
  app  : (f a : Lam)  → Lam
  lam  : (t : Lam)    → Lam

\end{code}

%format Fℕ = F "_{" ℕ "}"
%format FList = F "_{" List "}"
%format FLam = F "_{" Lam "}"

\noindent An elegant way to formalize and reason about inductive types
is to model them as the initial algebra of an endofunctor, we can
define the siganture functors cirresponding to each of the examples above:

\begin{code}

Fℕ : Set → Set
Fℕ X = ⊤ ⊎ X

FList : (A : Set) → Set → Set
FList A X = ⊤ ⊎ (A × X) 

FLam : Set → Set
FLam X = ℕ ⊎ (X × X) ⊎ X

\end{code}

This perspective has been very
successful in providing a generic approach to programming with and
reasoning about inductive types, e.g. see the \emph{Algebra of
Programming} \cite{BirdDeMoor:AlgProp}.

While the theory of inductive types is well developed, we often want
to have a finer, more expressive, notion of types, for example to
ensure the absence of run time errors --- access to arrays out of
range or access to an undefined variable in the previous example of
$\lambda$-terms. 

To model this we move to the notion of an inductive
family in Type Theory. A family is a type indexed by another already
given type. The first example is the family of finite sets |Fin| which
assigns to any natural number |n| a set |Fin n| which has exactly
|n| elements. |Fin| can be used where in conventional reasoning we
assume any finite set, e.g. when dealing with a finite address apace or
a finite set of variables. The inductive definition of |Fin| refines
the type of natural numbers:
\begin{code}

data Fin : ℕ → Set where
  zero  : ∀ {n}              → Fin (suc n)
  suc   : ∀ {n} (i : Fin n)  → Fin (suc n)

\end{code}

In the same fashion we can refine the type of lists to the type of
vectors which are additionally indexed by a number indicating the
length of the vector:

\begin{code}

data Vec (A : Set) : ℕ → Set where
  []   :                                 Vec A zero
  _∷_  : ∀ {n} (a : A) (as : Vec A n) →  Vec A (suc n)

\end{code}

Using |Fin| and |Vec| instead of |Nat| and |List| enables us to write
a total projection function projecting the nth element out of vector:
\begin{code}
_!!_ : {A : Set} → List A → ℕ → Maybe A
[] !! n            = nothing
(a ∷ as) !! zero   = just a
(a ∷ as) !! suc n  = as !! n  
\end{code}
Note, that a corresponding function |_!!_ : {A : Set} → List A → ℕ →
A| is not definable in a total langauge like Agda.

Finally we can define the notion of a well-scoped lambda term with
|ScLam| which assigns to a natural number |n| the set of $\lambda$-terms
with at most |n| free variables |ScLam n|. DeBruijn variables are now
modelled by elements of |Fin n| replacing |Nat| in the previous,
unindexed definition of $\lambda$-terms |Lam|.

\begin{code}

data ScLam (n : ℕ) : Set where
  var  : (i : Fin n)          → ScLam n
  app  : (f a : ScLam n)      → ScLam n
  lam  : (t : ScLam (suc n))  → ScLam n

\end{code}

\noindent
Importantly, the constructor
|lam| reduces the number of \emph{free} variables by one --- by
binding one. 
Inductive families may be mutually defined, for example the scoped
versions of  $\beta$ (|NfLam|)
normal forms and neutral $\lambda$-terms (|NeLam|): 
\begin{code}

mutual

  data NeLam (n : ℕ) : Set where
    var  : (i : Fin n)                  → NeLam n
    app  : (f : NeLam n) (a : NfLam n)  → NeLam n 

  data NfLam (n : ℕ) : Set where
    lam  : (t : NfLam (suc n))          → NfLam n
    ne   : (t : NeLam n)                → NfLam n

\end{code}

%format FFin = F "_{" Fin "}"
%format FVec = F "_{" Vec "}"
%format FScLam = F "_{" ScLam "}"

The initial algebra semantics of inductive types can be extended to
model inductive families by replacing functors on the category |Set|
with functors on the category of families indexed by a given type - in
the case of $\lambda$-terms this indexing type was |Nat|. The objects
of the category of families indexed over a type |I : set| are
|I|-indexed families, i.e. functions of type |I → Set|, and a
morphism between |I|-indexed families |A, B : I → Set| is given by a
family of maps |f : (i : I) -> A i -> B i|
Indeed, this category
is easily seen to be isomorphic to the slice category $|Set|/ |I|$ but
the chosen representation is more convenient type-theoretically. Using
$\Sigma$-types and equality types from Type Theory, we can define the
following endofunctors |FFin|, |FVec| and |FLam|
on the category of families
over |Nat| whose initial algebras are |Fin| and |Lam|, respectively:

\begin{code}

FFin : (ℕ → Set) → ℕ → Set
FFin X n = Σ ℕ λ m → (n ≡ suc m) × (⊤ ⊎ X m)

FVec : (A : Set) → (ℕ → Set) → ℕ → Set
FVec A X n = n ≡ zero ⊎ Σ ℕ λ m → (n ≡ suc m) × (A × X m)

FScLam : (ℕ → Set) → ℕ → Set
FScLam X n = Fin n ⊎ (X n × X n) ⊎ (X ∘ suc) n

\end{code}

The equality type expresses the focussed character of the
constructors for |Fin|. 

\begin{code}

FNe : (ℕ → Set) → (ℕ → Set) → ℕ → Set
FNe X Y n = Fin n ⊎ (X n ⊎ Y n)

FNf : (ℕ → Set) → (ℕ → Set) → ℕ → Set
FNf X Y n = (Y ∘ suc) n ⊎ X n

\end{code} 

\todo{Discuss mutual case.}

%format ι = "\iota"
%format σ = "\sigma"
%format τ = "\tau"
%format Γ = "\Gamma"

%format ->- = "\Rightarrow"
%format _->-_ = _ ->- _

This approach extends uniformly to more complicated examples such as
the family of typed $\lambda$-terms, using lists of types  to
represent typing contexts:
\begin{code}

data Ty : Set where
  ι  : Ty
  _->-_   : (σ τ : Ty) → Ty

data Var (τ : Ty) : List Ty → Set where
  zero  : ∀ {Γ}                  → Var τ (τ ∷ Γ)
  suc   : ∀ {σ Γ} (i : Var τ Γ)  → Var τ (σ ∷ Γ)

data STLam (Γ : List Ty) : Ty → Set where
  var  : ∀ {τ}    (i : Var τ Γ)            → STLam Γ τ
  app  : ∀ {σ τ}  (f : STLam Γ (σ ->- τ)) 
                  (a : STLam Γ σ)          → STLam Γ τ
  lam  : ∀ {σ τ}  (t : STLam (σ ∷ Γ) τ)    → STLam Γ (σ ->- τ) 

\end{code}

\noindent
Types like this can be used to implement a tag-free, terminating
evaluator~\cite{bsn}. To obtain the corresponding functors
is a laborious but straightforward exercise.

\todo{Expand here?}

\noindent
Inductive families are the backbone of
dependently typed programming as present in Epigram or
Agda~\cite{Agda}. Coq also supports the definition of inductive families
but programming with them is rather hard --- a situation which has been
improved by the new \texttt{Program} tactic~\cite{sozeau}. 
More recently, the implementation of Generalized Algebraic Datatypes 
(GADTs)~\cite{Hinze:GADT} 
allows |Fin| and |Lam| to be encoded in Haskell:
\begin{verbatim}
data Fin a where 
  FZero :: Fin (Maybe a)
  FSucc :: Fin a -> Fin (Maybe a)

data Lam a where 
  Var :: Fin a -> Lam a
  App :: Lam a -> Lam a -> Lam a
  Abs :: Lam (Maybe a) -> Lam a
\end{verbatim}
Here \texttt{Fin} and \texttt{Lam} are indexed by types instead of
natural numbers; The type constructor \texttt{Maybe} serves as a type level
copy of the |succ| constructor for natural numbers.
Note that \texttt{Lam} is actually just a nested datatype 
\cite{alti:csl99} while \texttt{Fin} exploits the full power of
GADTs because the range of the constructors is constrained.

\subsection{Overview over the paper}
\label{sec:overview-over-paper}

We develop our type theoretic and categorical background in section
\ref{sec:background} and also summarize the basic definitions of
non-indexed containers. In section \ref{sec:ifunc} we develop the
concept of an indexed functor, showing that this is a relative monad
and presenting basic constructions on indexed functors including the
definition of a parametrized initial algebra. In section
\ref{sec:icont} we devlop the basic theory of indexed containers and
relate them to indexed functors. Subsequently in section
\ref{sec:initalg} we construct initial algebras of indexed containers
assuming the existence of indexed W-types, this can be dualized to
showing the existence of terminal coalgebras from indexed M-types 
\ref{sec:termcoalg}. Both requirements, indexed W-types and indexed
M-types can be derived from ordinary W-types, this is shown in section
\ref{sec:w-enough}. Finally, we define a syntax from strictly positive
families and interpret this using indexed containers \ref{sec:spf}.

\subsection{Related work}
\label{sec:related-work}

\noindent We introduce the notion of indexed container which
generalizes containers allowing us to represent inductive
families. This is a further step from \emph{dependent polynomial
  functors} \cite{HylandGambino} representing endofunctors on a slice
category. Indexed containers as introduced in the present paper allow us
to represent functors between different slices and capture also mutual
and nested inductive definitions.

While Hyland and Gambino \cite{HylandGambino} show that dependent polynomial 
functors always
have initial algebras, we show that indexed containers are closed under 
parametrized initial algebras. Hence we can apply the fixpoint
construction several times. The flexibility of indexed
containers allows us to also establish closure under the adjoints of
reindexing. This leads directly to a grammar for strictly positive
families, which itself is an instance of a strictly positive family 
(section \ref{sec:spf}) --- see also our previous work \cite{alti:cats07,alti:jcats07}.

Containers are related to Girard's normal functors \cite{GirardNormal} which
themselves are a special case of Joyal's analytic functors
\cite{JoyalA:fonaes} --- those that allow only finite sets of positions.
Fiore, Gambino, Hyland and Winskel's work on generalized species
\cite{fiore2008ccb} considers those concepts in a more generic setting ---
th e precise relation of this work to indexed containers remains to be
explored.

Perhaps the earliest publication related to indexed containers
occurs in Petersson and Synek's paper
\cite{PS89} from 1989. They present rules extending Martin-L{\"o}f's
type theory with a set constructor for `tree sets' : families of
mutually defined inductive sets, over a fixed index set.

Inspired in part by Petersson and Synek's constructor,
Hancock, Hyvernat and Setzer \cite{hancock-apal06} applied indexed (and unindexed)
containers, under the name `interaction structures' to the task of
modelling imperative interfaces such as command-response interfaces in
a number of publications. 

This paper is an expanded and revised version of the LICS paper by the
first and 3rd author \cite{lics}. In the present paper we have
integrated the Agda formalisation in the main development, which in
many instances required extending it. We have made explicit the use of
relative monads which was only hinted at in the conference version
based on the recent work on relative monads \cite{relmon}. We have
also dualized the development to terminal coalgebras which required
the type of paths to be defined inductively instead of recursively as
done in the conference paper (section \ref{sec:termcoalg}).  We
have also formalized the derivation of indexed W-types from ordinary
W-types (section \ref{wifromw}. The derivation of M-types from W-types
(section \ref{sec:mfromw})
was already given in \cite{C-CSPTs} is revisited here exploiting the
indexed W-type derived previously. moreover the development is formalized in
Agda. 

\todo{What did I miss?}
