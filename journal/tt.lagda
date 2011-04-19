
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module tt where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Data.Product as Prod
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


Our contructions are all developed in Agda, and so we adopt its syntax, but we will take certain liberties with it's type-theory. For, instance we need to work in a setting with extensional type-theory, so we extend the propositional equality with this extensionality axiom:

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

This obviously creates non-canonical elements of |_≅_|, but does not make our theory unsound.

%if style == newcode

\begin{code}

open EXT public

module uip {l} {A : Set l} where

\end{code}

%endif

We also use the principle of uniqueness of identity types, to simplyfy some of our constructions:

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

Instead of having all of Agda's data-types we assume that we only have |W|-types. A type theory has |W| types if it has a type former |W : (S : Set) (P : S → Set) → Set| with a constructor |sup| and an eliminator |wrec|:

\begin{code}

data W (S : Set) (P : S → Set) : Set where
  sup : (Σ S λ s → P s → W S P) → W S P

wrec :  {S : Set} {P : S → Set} (Q : W S P → Set) 
        (x : W S P)
        (m :  (s : S) (f : P s → W S P) 
              (h : (p : P s) → Q (f p)) 
              → Q (sup (s , f)))
        → Q x
wrec Q (sup (s , f)) m = m s f (λ p → wrec Q (f p) m)

\end{code}

\noindent
We will continue to define extra Agda data-types in the rest of the paper, but in the end we will show how each of these can be reduced to a theory that contains only |W|. For compactness, and readablity we will also define functions using Agda's pattern matching syntax, rather than encoding them using wrec, it is an unstated lemma that each of these definitions can be reduced to terms which only use |wrec|,

We are going to use type theory versions of certain category theoretic concepts 
For instance, we use ends |End| to capture natural transformations.
Given a bifunctor |F : Setop → Set → Set|, an element of |∫ X ** F X X| is
equivalent to an element of |f : {X : Set} → F X X|, along with a proof:

\[ \mbox{|{A B : Set} (g : A → B) → F g B (f {B}) ≡ F A g (f {A})|} \]


\noindent
The natural transformations between functors |F| and |G| are
ends |∫ X ** F X → G X|. We will often ignore the presence of the proofs, and 
use such ends directly as polymorphic functions.

In this setting, the Yoneda lemma can be stated as follows, for any functor |F|:

\[\mbox{| F X ≅ ∫ Y ** (X → Y) → F Y |}\]

we will make use of this fact later on.

Finally, for readability we will elide certain artifacts in Agda's syntax, for instance the quantification of implicit arguments when their types can be inferred from the context. The reader should be reassured that the paper is a literate agda file, available from the final author's webpage.