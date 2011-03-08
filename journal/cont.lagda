%if style == newcode 

\begin{code}

module cont where

open import Data.Product

\end{code}

%endif

\subsection{Containers}

%format ◁ = "\lhd"
%format _◁_ = _ ◁ _


\begin{code}

record Cont : Set₁ where
  constructor _◁_ 
  field 
    S : Set
    P : S → Set

⟦_⟧ : Cont → Set → Set
⟦ S ◁ P ⟧ X = Σ S λ s → P s → X

\end{code}