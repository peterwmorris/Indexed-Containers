
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
open import Relation.Binary.PropositionalEquality
open import Coinduction
open import Data.Nat hiding (_⊔_)
open import Relation.Nullary

open import common

\end{code}

%endif

\subsection{Type Theory}

\newcommand{\prodd}{\ensuremath{\mathaccent\cdot{\prod}}}

%format ∫ = "\prodd"
%format ** = "."
%format Setop = Set "^{" op "}"

%if style==newcode

\begin{code}
EndS : ∀ {l l'} {T : Set l} → (F : T → Set l') → Set (l ⊔ l')
EndS {T = T} F = {X : T} → F X


syntax EndS (λ X → F) = ∫ X ** F

Setop : Set₁
Setop  = Set 
\end{code}

%endif


Our contructions are all developed in Agda, and so we adopt it's type-theory and
syntax. With the following extra pieces of notation:

\begin{code}

postulate ext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g

ext⁻¹ : {A : Set} {B : A → Set} {f g : (a : A) → B a} → f ≡ g → ((a : A) → f a ≡ g a)
ext⁻¹ refl a = refl

data W (S : Set) (P : S → Set) : Set where
  sup : (s : S) (f : P s → W S P) → W S P

\end{code}

We are going to use type theory versions of certain category theoretic concepts 
For instance, we use ends |End| to capture natural transformations.
Given a bifunctor |F : Setop → Set → Set|, an element of |∫ X ** F X X| is
equivalent to an element of |f : {X : Set} → F X X|, along with a proof:

\[ \mbox{|{A B : Set} (g : A → B) → F g B (f {B}) ≡ F A g (f {A})|} \]


\noindent
The natural transformations between functors |F| and |G| are
ends |∫ X ** F X → G X|. We will often ignore the presence of the proofs, and 
use such ends directly as polymorphic functions.

In this setting, the Yoneda lemma can be stated as follows:

\[\mbox{| F X ≅ ∫ Y ** (X → Y) → F Y |}\]

we will make use of this fact later on.
