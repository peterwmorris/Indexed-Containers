%if style == code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module introduction where

open import Data.Unit
open import Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.HeterogeneousEquality
-- open import Data.List
open import Function

open import common
open import tt


\end{code}

%endif

%format Σ* = "(\!"
%format ∶ = :
%format *Σ = "\!)" × 


\section{Introduction}


\noindent Inductive datatypes are a central feature of modern Type Theory
(e.g. Coq~\cite{CIC}) or functional programming (e.g. 
Haskell\footnote{Here we shall view Haskell as an approximation of strong
  functional programming as proposed by Turner \cite{sfp} and ignore
non-termination.}). Examples include the natural numbers a la Peano:
\footnote{We are using Agda to represent constructions in Type Theory. Indeed, 
the source of this document is a literate Agda file which is available online, 
\cite{alti:ic-code}. For an overview over Agda see \cite{agda-wiki}, in particular the 
tutorials and the reference manual which explain how to read the code included in this paper.}

\begin{code}

data ℕ : Set where
  zero  : ℕ
  suc   : (n : ℕ) → ℕ

\end{code}
the set of lists indexed by a given set:
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
is to model them as the initial algebra of an endofunctor.
\footnote{This requires a type theory with an extensional propositional equality.}
We can
define the signature functors corresponding to each of the above examples
as follows:

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
to have a finer, more expressive, notion of type. This allows us, for
example, to ensure the absence of runtime errors such as access to
arrays out of range or access to undefined variables in the previous
example of $\lambda$-terms. To model such finer types, we move to the
notion of an inductive family in Type Theory. A family is a type
indexed by another, already given, type. Our first example of an
inductive family is the family of finite sets |Fin| which assigns to
any natural number |n| a type |Fin n| which has exactly |n|
elements. |Fin| can be used where, in conventional reasoning, we
assume a finite set, e.g. when dealing with a finite address space or
a finite set of variables. The inductive definition of |Fin| refines
the type of natural numbers: 

\begin{code}

data Fin : ℕ → Set where
  zero  : ∀ {n}              → Fin (suc n)
  suc   : ∀ {n} (i : Fin n)  → Fin (suc n)

\end{code}

In the same fashion we can refine the type of lists to the type of
vectors which are indexed by a number indicating the
length of the vector:

\begin{code}

data Vec (A : Set) : ℕ → Set where
  []   :                                 Vec A zero
  _∷_  : ∀ {n} (a : A) (as : Vec A n) →  Vec A (suc n)

\end{code}

Notice how using the inductive family |Vec| instead of
|List| enables us to write a total projection
function projecting the $n$th element out of vector: 

\begin{code} 
_!!_ : {A : Set} → {n : ℕ} → Vec A n → Fin n → A 
[]        !! () 
(a ∷ as)  !! zero  = a 
(a ∷ as)  !! suc n = as !! n 

\end{code} 

In contrast, the corresponding function |_!!_ : {A : Set} → List A → ℕ →
A| is not definable in a total language like Agda.

Finally, we can define the family of a well-scoped lambda terms
|ScLam| which assigns to a natural number |n| the set of $\lambda$-terms
with at most |n| free variables |ScLam n|. DeBruijn variables are now
modeled by elements of |Fin n| replacing |Nat| in the previous,
unindexed definition of $\lambda$-terms |Lam|.

\begin{code}

data ScLam (n : ℕ) : Set where
  var  : (i : Fin n)          → ScLam n
  app  : (f a : ScLam n)      → ScLam n
  lam  : (t : ScLam (suc n))  → ScLam n

\end{code}

\noindent
Importantly, the constructor
|lam| reduces the number of \emph{free} variables by one. 
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
with functors on the category of families indexed by a given type --- in
the case of all our examples so far this indexing type was |Nat|. The objects
of the category of families indexed over a type |I : Set| are
|I|-indexed families of sets, i.e. functions of type |I → Set|, and a
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
FFin X n = Σ* m ∶ ℕ *Σ  (n ≡ suc m) × (⊤ ⊎ X m)

FVec : (A : Set) → (ℕ → Set) → ℕ → Set
FVec A X n = n ≡ zero ⊎ (Σ* m ∶ ℕ *Σ (n ≡ suc m) × (A × X m))

FScLam : (ℕ → Set) → ℕ → Set
FScLam X n = Fin n ⊎ (X n × X n) ⊎ (X ∘ suc) n

\end{code}

The equality type expresses the focussed character of the constructors
for |Fin|. The mutual definition of |NeLam| and |NfLam| can be
represented by two binary functors:

%format FNe = F "_{" NeLam "}"
%format FNf = F "_{" NfLam "}"

\begin{code}

FNe : (ℕ → Set) → (ℕ → Set) → ℕ → Set
FNe X Y n = Fin n ⊎ (X n × Y n)

FNf : (ℕ → Set) → (ℕ → Set) → ℕ → Set
FNf X Y n = (Y ∘ suc) n ⊎ X n

\end{code} 

We can construct |NeLam| and |NfLam| as follows:
first we define a parametrized initial algebra |NeLam' : (ℕ → Set) → ℕ
→ Set| so that |NeLam' Y| is the initial algebra of |λ X → FNe X Y|
and then |NfLam| is the initial algebra of |λ Y → FNf (NeLam' Y) Y|.
Symmetrically we derive |NeLam|. Compare this with the encoding in
section \ref{sec:spf}.

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

\noindent Types like this can be used to implement a tag-free,
terminating evaluator~\cite{bsn}. Obtaining the corresponding functors
is a laborious but straightforward exercise.  As a result of examples
such as the above, inductive families have become the backbone of
dependently typed programming as present in Epigram or
Agda~\cite{Agda}. Coq also supports the definition of inductive
families but programming with them is rather hard --- a situation
which has been improved by the \texttt{Program}
tactic~\cite{sozeau}. 


Indexed containers are designed to provide the mathematical and
computational infrastructure required to program with inductive
families. The remarkable fact about indexed containers, and the fact
which underpins their practical usefulness, is that they offer an
exceedingly compact way to encapsulate all the information inherent
within the definition of functors such as |FFin|, |FVec| and |FScLam|,
|FNe| and |FNf| and hence within the associated inductive
families |Fin|, |Vec|, |ScLam|, |NeLam| and |NfLam|.  The second
important thing about indexed containers is that not only can they be
used to represent functors, but the canonical constructions on
functors can be internalised to become constructions on the indexed
containers which represent those functors. As a result, we get a compositional
combinator language for inductive families as opposed to simply a
syntactic definitional format for inductive families. 



\subsection{Related work}
\label{sec:related-work}

This paper is an expanded and revised version of the LICS paper by the
first and 4th author \cite{alti:lics09}. In the present paper we have
integrated the Agda formalisation in the main development, which in
many instances required extending it. We have made explicit the use of
relative monads which was only hinted at in the conference version,
based on recent work \cite{alti:fossacs10}. We
have also dualized the development to terminal coalgebras which
required the type of paths to be defined inductively instead of
recursively as done in the conference paper (section
\ref{sec:termcoalg}).  We have also formalized the derivation of
indexed W-types from ordinary W-types (section \ref{wifromw}). The
derivation of M-types from W-types (section \ref{sec:mfromw}) was
already given in \cite{alti:cont-tcs} and is revisited here exploiting the
indexed W-type derived previously. Moreover the development is fully
formalized in Agda.

Indexed containers are intimately related to \emph{dependent
polynomial functors} \cite{HylandGambino}, see also the comprehensive
notes \cite{kock2009notes}.  Indeed, at a very general level one could
think of indexed containers as the type theoretic version of dependent
polynomials and vice versa. However, the different needs of
programmers from category theorists has taken our development of
indexed containers in a different direction from that of dependent
polynomials. In this vein an important contribution is the Agda
implementation of our ideas which makes our work more useful to
programmers than the categorical work on dependent polynomials.  We
also focus on syntactic constructions such using indexed containers to
model mutual and nested inductive definitions. As a consequence we
show that indexed containers are closed under parametrized initial
algebras and coalgebras and reduce the construction of parameterised
final coalgebras to that of initial algebras. Hence we can apply both
the initial algebra and final coalgebra construction several
times. The flexibility of indexed containers allows us to also
establish closure under the adjoints of reindexing. This leads
directly to a grammar for strictly positive families, which itself is
an instance of a strictly positive family (section \ref{sec:spf}) ---
see also our previous work \cite{alti:cats07,alti:jcats07}. This
generalizes previous results on strictly positive datatypes by Dybjer
\cite{dybjer1997representing} which have been further developed in
\cite{alti:cont-tcs}.

Containers are related to Girard's normal functors \cite{GirardNormal}
which themselves are a special case of Joyal's analytic functors
\cite{JoyalA:fonaes} --- those that allow only finite sets of
positions. Fiore, Gambino, Hyland and Winskel's work on generalized
species \cite{fiore2008ccb} considers those concepts in a more generic
setting --- the precise relation of this work to indexed containers
remains to be explored but it appears that generalised species can be
thought of as indexed containers closed under quotients.

Perhaps the earliest publication related to indexed containers occurs
in Petersson and Synek's paper \cite{PS89} from 1989. They present
rules extending Martin-L{\"o}f's type theory with a set constructor
for `tree sets' : families of mutually defined inductive sets, over a
fixed index set. Indeed, Petersson-Synek trees are semantically
equivalent to the |WI|-type we define in section 5 --- the difference
is that |WI|-types represent positions as a family indexed over the
output positions while the tree type use a set of positions together
with a function which assigns the output position. This is an
instance of Grothendieck's well known inverse image construction.
Inspired in part by Petersson and Synek's constructor, Hancock,
Hyvernat and Setzer \cite{hancock-apal06} applied indexed (and
unindexed) containers under the name `interaction structures' to the
task of modelling imperative interfaces such as command-response
interfaces in a number of publications.  The construction of
|WI|-types from |W|-types in section \ref{sec:w-enough} is related to
the reduction of indexed induction-recursion to induction-recursion in
\cite{dybjer2001indexed} and the construction of initial algebras in
\cite{gambino2004wellfounded}. 
The use of $\omega$-limits to construct
final coalgebras in the same section is folklore, e.g. see Adamek
\cite{adamek1995greatest} and Lindstr\"om \cite{lindstroem89}.
%Halln\"{a}s \cite{hallnas1987intensional}
% and Aczel and Mendler  \cite{aczel1989final}.

The implementation of Generalized Algebraic Datatypes 
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
natural numbers; The type constructor \texttt{Maybe} serves as a type
level copy of the |succ| constructor for natural numbers.  Note that
\texttt{Lam} is actually just a nested datatype \cite{alti:csl99}
while \texttt{Fin} exploits the full power of GADTs because the range
of the constructors is constrained. The problem with using GADTs to
model inductive families is, however, that the use of type level
proxies for say, natural numbers, means that computation must be
imported to the type level. This is a difficult problem and probably
limits the use of GADTs as a model of inductive families.

Since the publication of the LICS paper, indexed containers have been used 
as a base for the generic definition of datatypes for Epigram 2 \cite{chapman2010gentle},
and to develop the theory of ornaments \cite{mcbride2010ornamental}.
In recent work it has been shown that indexed containers are sufficient
to express all \emph{small} inductive-recursive definitions \cite{alti:tlca13-small-ir}

\subsection{Overview over the paper}
\label{sec:overview-over-paper}

We develop our type theoretic and categorical background in section
\ref{sec:background} and also summarize the basic definitions of
non-indexed containers. In section \ref{sec:ifunc} we develop the
concept of an indexed functor, showing that this is a relative monad
and presenting basic constructions on indexed functors including the
definition of a parametrized initial algebra. In section
\ref{sec:icont} we develop the basic theory of indexed containers and
relate them to indexed functors. Subsequently in section
\ref{sec:initalg} we construct parametrized initial algebras of indexed containers
assuming the existence of indexed W-types, this can be dualized to
showing the existence of parametrized terminal coalgebras of indexed
containers from indexed M-types 
in section \ref{sec:termcoalg}. Both requirements, indexed W-types and indexed
M-types can be derived from ordinary W-types, this is shown in section
\ref{sec:w-enough}. Finally, we define a syntax from strictly positive
families and interpret this using indexed containers in section \ref{sec:spf}.

The source of this paper is a literate Agda file, that is we have
formally verified the constructions using Agda. There are some
exceptions: propositions 1 - 5 are only done on paper and
|MIext|, that bisimilarity of |MI| trees implies extensional equality
is postulated instead of proven. We also have omitted the functor laws
and naturality laws from the formal development --- we never rely on
assuming that something is a functor or a natural
transformation. These laws are of a particular simple form for indexed
containers and hence we implicitly prove them when needed, e.g. in
proposition 10. The propositions which do rely on these assumptions,
e.g. proposition 3, are only done on paper. The reason for these
omissions is that the purpose of the paper is to introduce indexed
containers and a complete formalisation of these more elementary
results would have introduced significant technical complications
distracting from our central purpose.

\subsection*{Acknowledgements}
\label{sec:acknowledgements}

We would like to thank the anonymous referees for useful comments and
suggestions and Frederik Forsberg for help with proofreading.

