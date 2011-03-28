
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

In category therory, an $\omega$-chain, is an infinite diagram:

\[
\xymatrix{
|A|_{0} &
\ar[l]_{|a|_{0}}
|A|_{1} &
\ar[l]_{|a|_{1}}
|A|_{2} &
\cdots &
|A|_{n-1} &
\ar[l]_{|a|_{n-1}} 
|A|_{n} &
\ar[l]_{|a|_{n}} 
|A|_{n+1} &
\cdots} 
\]

In type-theroy, we can represent such a chain, as a pair of functions:

\begin{code}

Chain : Set₁
Chain = Σ (ℕ → Set) λ A → (n : ℕ) → A (suc n) → A n

\end{code}

The limit of a chain is an object |X| and family of projections 
$\pi_{n} \in \mbox{|X|} → \mbox{|A|}_{n}$ such that in the following diagram, 
all the small triangles commute:

\[
\xymatrix{
|A|_{0} &
\ar[l]_{|a|_{0}}
|A|_{1} &
\ar[l]_{|a|_{1}}
|A|_{2} &
\cdots &
|A|_{n-1} &
\ar[l]_{|a|_{n-1}} 
|A|_{n} &
\ar[l]_{|a|_{n}} 
|A|_{n+1} &
\cdots
\\
\\
& & & & 
|X|
\ar[uullll]_{\pi_{0}}
\ar[uulll]_{\pi_{1}}
\ar[uull]_{\pi_{2}}
\ar[uu]_{\pi_{n-1}}
\ar[uur]_{\pi_{n}}
\ar[uurr]_{\pi_{n+1}}
&&&\\
} 
\]

It is also required that the limit is the least object with these properties 
(or cone). 
Again, we can encode the limit of a chain, its projections, and this universal 
property in type theory:

%format π = "\pi"

\begin{code}

LIM : Chain → Set
LIM (A , a) = Σ ((n : ℕ) → A n) λ f → ((n : ℕ) → a n (f (suc n)) ≡ f n)

π : {c : Chain} → (n : ℕ) → LIM c → proj₁ c n
π n (f , p) = f n

comm : {c : Chain} (n : ℕ) (l : LIM c) → proj₂ c n (π {c} (suc n) l) ≡ π {c} n l
comm n (f , p) = p n

univ : {c : Chain} {X : Set} (pro : (n : ℕ) → X → proj₁ c n) 
       (com : (n : ℕ) (x : X) → proj₂ c n (pro (suc n) x) ≡ pro n x) →
       X → LIM c
univ pro com x = (λ n → pro n x) , (λ n → com n x)

\end{code}

Given a functor $|F|$, we can build a chain:

\[
\xymatrix{
|⊤| &
\ar[l]_{}
|F| |⊤| &
\ar[l]_{|F| |!|}
|F|^{2} |⊥| &
\ar[l]_{|F|^{2} |!|}
|F|^{3} &
\cdots &
} 
\]

We know from Asperti and Longo \cite{AspertiLongo} that if |F| is 
$\omega$-continuous, \emph{i.e.} that for any chain $(A, a)$:

| F (LIM (A, a)) ≅ LIM ((F ∘ A), (F ∘ a) |

\noindent
then the limit of the chain above will be the terminal co-algebra of |F|. We 
want to build |M|-types, which we know to be the terminal co-algebras of 
container functors. In order, then to build |M|-types, we must construct 
iteration of container functors (to build the chain) and show that all container
functors are $\omega$ continuous.

Since we only need to build iterations of container functors applied to the 
initial object |⊤|, we build that directly. We define the following variation 
of |W|, cut off at a know depth:

\begin{code}

data WM (S : Set) (P : S → Set) : ℕ → Set where
  wm⊤ : WM S P zero
  sup : ∀ {n} → ⟦ S ◁ P ⟧ (WM S P n) → WM S P (suc n)

\end{code}

\noindent
It should be obvious that |WM zero| is indeed initial in |Set| and that |⟦ S ◁ P ⟧ (WM S P n) ≅ WM S P (suc n)|, so this is the thing we want.  


Note that |WM| is itself encodable as an indexed |WI| type, and by the result 
above, a |W| type:

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
We can truncate any given tree of depth greater than 1, this amounts to the 
iteration of the morphism part of the container functor applied to the unique 
moprhism into the terminal object:

\begin{code}

trunc : ∀ {S P} → (n : ℕ) → WM S P (suc n) → WM S P n
trunc zero (sup (s , f)) = wm⊤
trunc (suc n) (sup (s , f)) = sup (s , trunc n ∘ f)

\end{code}

So now we can build the chain of finitie itererations of a container functor:

\begin{code}

M-chain : (S : Set) (P : S → Set) → Chain
M-chain S P = WM S P , trunc

\end{code}

\begin{proposition}
All container functors are $\omega$-continuous. That is, they preserve 
$\omega$-limits.
\end{proposition}

\begin{proof}
We want to build the isomorphism 
| F (LIM (A, a)) ≅ LIM ((F ∘ A), F ∘ a | in the case that |F|
is a container functor. However, the function from left to right is uniquely 
given by the universal property of |LIM| for all functors |F : Set → Set|. 
To show this we build the cone for |F (LIM (A , a))|:


\[
\xymatrix{
|F| |A|_{0} &
\ar[l]_{|F| |a|_{0}}
|F| |A|_{1} &
\ar[l]_{|F| |a|_{1}}
|F| |A|_{2} &
\cdots &
|F| |A|_{n-1} &
\ar[l]_{|F| |a|_{n-1}} 
|F| |A|_{n} &
\cdots
\\
\\
& & &  
|F (LIM (A , a))|
\ar[uulll]^{|F| \pi_{0}}
\ar[uull]_{|F| \pi_{1}}
\ar[uul]_{|F| \pi_{2}}
\ar[uur]_{|F| \pi_{n-1}}
\ar[uurr]_{|F| \pi_{n}}
&&&\\
} 
\]

\noindent
The small triangles in the diagram above obviously commute, so there exists a 
unique morphism from |F (LIM (A , a))| into 
|LIM ((F ∘ A), F  ∘ a)|.
All that remains then, is to construct an inverse to this unique morphism, in 
the case that |F ≡ ⟦ S ◁ P ⟧ |, that is we must build a function:

%if code == newstyle

\begin{code}

module imp (S : Set) (P : S → Set) (A : ℕ → Set) (a : (n : ℕ) → A (suc n) → A n) where

\end{code}

%endif

%format ω-cont = "\omega" -cont

\begin{code} 
  ω-cont :  LIM  (  (  λ n → Σ S λ s → P s → A n)
                 ,     λ n → split s & f tilps ↦  (s , a n ∘ f) !m !s
                 ) 
          → (Σ S λ s → P s → (LIM (A , a)))
\end{code}

Note that the shape picked at every point along the chain must be the same, in 
order to make the diagrams commute, thus although it seems like there is an 
infinite choice of shapes, they must all be the same. This is the key insight
into constructing this function.

%if style == newcode

\begin{code}

  ω-cont = {!!}

\end{code}

%endif

\end{proof}

We now entitled to derive |M| types from |W| by defining:

\begin{code}

M : (S : Set) (P : S → Set) → Set
M S P = LIM (M-chain S P)

\end{code}