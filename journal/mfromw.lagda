
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module mfromw where

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
open import tt
open import cont

\end{code}

%endif

\subsubsection{|M| from |W|}
Since we have shown that both |WI| and |MI| types can be reduced to their 
non-indexed counterparts, it only remains to show that |M| types can be, reduced
to |W| types. This is a result from \cite{C-CSPTs}, though in the setting of 
indexed |WI| types, we can give a better intuition.

We begin by costructing a counterpart to |W| but which is \emph{cut-off}
at a known depth:

\begin{code}

data WM (S : Set) (P : S → Set) : ℕ → Set where
  wm⊥ : WM S P zero
  sup : ∀ {n} → ⟦ S ◁ P ⟧ (WM S P n) → WM S P (suc n)

\end{code}

\noindent
This is itself encodable as an indexed |WI| type, and by the result above, a |W|
type:

%if style == newcode

\begin{code}

{-

\end{code}

%endif

\begin{code}

WM′ : (S : Set) (P : S → Set) → ℕ → Set
WM′ S P = WI S′ P′
  where
    S′ : ℕ → Set
    S′ zero = ⊤
    S′ (suc n) = S
    P′ : (n : ℕ) → S′ n → ℕ → Set 
    P′ zero _ _ = ⊥
    P′ (suc m) s n with m ≟ n 
    P′ (suc .n) s n | yes refl = P s
    P′ (suc m) s n | no ¬p = ⊥

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif

\noindent
We can truncate any given tree of depth greater than 1:

\begin{code}

trunc : ∀ {S P} → {n : ℕ} → WM S P (suc n) → WM S P n
trunc {n = zero} (sup (s , f)) = wm⊥
trunc {n = suc n} (sup (s , f)) = sup (s , trunc ∘ f)

\end{code}

\noindent
We then say that an |M| type is an infinitie sequence of approximations, cut off
at sucessively lower depths, with the property that truncating any tree results 
in the previous tree in the sequence:

\begin{code}

M : (S : Set) (P : S → Set) → Set
M S P = Σ  (  (n : ℕ) → WM S P n) λ f → 
              (n : ℕ) → trunc (f (suc n)) ≡ f n

\end{code}

\noindent
Building an algebra map, (|sup|) for this encoding of |M| is straight-forward, 
the difficulty is in constructing the co-algebra map (|sup⁻¹|):

\begin{code}

ssup⁻¹ :  {S : Set} {P : S → Set} → M S P → ⟦ S ◁ P ⟧ (M S P)

\end{code}

\noindent
We have to produce a top level shape, but in theory we have an infinite choice
of candidates. We know, though, that all these shapes must 
be equal, so our choice doesn't matter.

\begin{code}

ssup⁻¹ (wm , t) with wm 1 
... | sup (s , f) = s , λ p → ((λ n → {!wm !}) , {!!})

\end{code}

\noindent
\textbf{Question: How much do we show of the proof that this is inverse to |sup|? It's pretty ugly.} 

A path to a position in such an infinite tree is a choice of a particular 
finite approximation, and a path through that tree. Since all paths are finite, 
this is all we need to complete the construction of |ν^C|, above, by only using 
|W| types.
