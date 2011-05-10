
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module tt where

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

_≡_ : {l : Level} {A : Set l} → A → A → Set
a ≡ b = a ≅ b

\end{code}

%endif

\subsection{Type Theory}

\newcommand{\prodd}{\ensuremath{\mathaccent\cdot{\prod}}}

%format ∫ = "\prodd"
%format ** = "."
%format Setop = Set "^{" op "}"
%format ->> = →

%if style==newcode

\begin{code}
EndS : ∀ {l l'} {T : Set l} → (F : T → Set l') → Set (l ⊔ l')
EndS {T = T} F = {X : T} → F X


syntax EndS (λ X → F) = ∫ X ** F 

Setop : Set₁
Setop  = Set 
\end{code}

%endif

%format Σ* = "(\!"
%format ∶ = :
%format *Σ = "\!)" × 

%format Σ′ = Σ
%format π₀ = "\pi_0"
%format π₁ = "\pi_1"

Our constructions are all developed in Agda, and so we adopt its syntax, but we will take certain liberties with its type-theory. 

We have $\Pi$-types, denoted |(a : A) → B a| and $\Sigma$-types, which we write as: |Σ* a ∶ A *Σ B a|. In fact this is sugar for the record type:

\begin{code}

record Σ′ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀

\end{code}

We will, however assume that the type-theory we work in has $\Sigma$-types as primative, and has no native support for data-types. 
Instead, we only have |W|-types, the empty-type |⊥|, the unit type |tt : ⊤| and the booleans |true , false : Bool|. 

A type theory has |W| types if it has a type former |W : (S : Set) (P : S → Set) → Set| with a constructor |sup| and an eliminator |wrec|:

\begin{code}

data W (S : Set) (P : S → Set) : Set where
  sup : Σ* s ∶ S *Σ (P s → W S P) → W S P

wrec :  {S : Set} {P : S → Set} (Q : W S P → Set) 
        (x : W S P)
        (m :  (s : S) (f : P s → W S P) 
              (h : (p : P s) → Q (f p)) 
              → Q (sup (s , f)))
        → Q x
wrec Q (sup (s , f)) m = m s f (λ p → wrec Q (f p) m)

\end{code}

\noindent
As a notational convenience, we will continue to define extra Agda data-types
in the rest of the paper, but in the end we will show how each of these can
be reduced to a theory that contains only |W|. For compactness, and
readability we will also define functions using Agda's pattern matching
syntax, rather than encoding them using |wrec|, all of these definitions can 
be reduced to terms which only use |wrec|.

We'll also require a notion of propositional equality. To simplyfy the presentation of some definitions later on, we will employ a heterogeneous equality.
This can be defined in Agda via a data-type:

%format ≅′ = ≅
%format _≅′_ = _≅_
%format ≡′ = ≡
%format _≡′_ = _≡_
%format subst′ = subst

\begin{code}

data _≅′_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅′ x

subst′ : {A : Set} (P : A → Set) {x y : A} → x ≅′ y → P x → P y
subst′ P refl p = p  

\end{code}

Most of the time our equalities will be homogeneous, however, so we introduce a short hand for this:

\begin{code}

_≡′_ : {A : Set} → A → A → Set 
a ≡ b = a ≅ b

\end{code}

It is also known that homogeneous and heterogeneous equality have the same 
strength, so all the definitions employing our equality could also be encoded in
a theory with only homogeneous equality.

This is an intensional equality, but we want to work in a setting with extensional type-theory, so we extend the propositional equality with this extensionality axiom:

%if style == newcode

\begin{code}

module EXT {l l'} {A : Set l} {B : A → Set l'} where

\end{code}

%endif

\begin{code}

  postulate ext :  {f g : (a : A) → B a} → 
                   ((a : A) → f a ≡ g a) → f ≡ g

  ext⁻¹ :  {f g : (a : A) → B a} → 
           f ≡ g → ((a : A) → f a ≡ g a)
  ext⁻¹ refl a = refl

\end{code}

This creates non-canonical elements of |_≅_|, \emph{i.e.} closed terms in
equality types which are not |refl|. In order to deal with these
non-canonical elements, we also rely on axiom |K|, or the uniqueness of
identity proofs:

%if style == newcode

\begin{code}

open EXT public

module uip {l} {A : Set l} where

\end{code}

%endif

%format UIP≡ = UIP

\begin{code}

  UIP≡ : {a b : A} {p : a ≅ b} {q : a ≅ b} → p ≅ q
  UIP≡ {p = refl} {q = refl} = refl

\end{code}

%if style == newcode

\begin{code}

  UIP : {A : Set l} {a : A} {B : Set l} {b : B} {p : a ≅ b} {q : a ≅ b} → p ≅ q
  UIP {p = refl} {q = refl} = refl

open uip public

\end{code}

%endif

With these ingredients we obtain a theory which corresponds to
extensional Type Theory \cite{hofmann1996conservativity}.

We are going to use type theoretic versions of certain category theoretic
concepts. For example we represent functors by packing up their definition as
an Agda record. An endo functor on set, is given by:

\begin{code}

record Func : Set₁ where
  obj  : Set → Set
  mor  : ∀ {A B} → (A → B) → obj A → obj B

\end{code}

It would also be possible to pack up the functor laws as extra fields in these 
records. 

We use ends |End| to capture natural transformations.
Given a bifunctor |F : Setop → Set → Set|, an element of |∫ X ** F X X| is
equivalent to an element of |f : {X : Set} → F X X|, along with a proof:

\[ \mbox{|{A B : Set} (g : A → B) → F g B (f {B}) ≡ F A g (f {A})|} \]

\noindent
The natural transformations between functors |F| and |G| are ends |∫ X ** F X
→ G X|. We will often ignore the presence of the proofs, and 
use such ends directly as polymorphic functions.

In this setting, the Yoneda lemma can be stated as follows, for any functor |F|:

\[\mbox{| F X ≅ ∫ Y ** (X → Y) → F Y |}\]

we will make use of this fact later on.

Finally, for readability we will elide certain artifacts in Agda's syntax,
for instance the quantification of implicit arguments when their types can be
inferred from the context. We will often leave out record projections 
from notions such as |Func|, allowing the functor to stand for both its action 
on object and morphism, just as would happen in the category theory 
literature. The reader should be reassured that the paper is a
literate agda file, available from the final author's webpage.
