
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module mfromw where

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
open import tt
open import cont
open import func

\end{code}

%endif

\subsection*{|M| from |W|}
\label{sec:mfromw}

Since we have shown that both |WI| and |MI| types can be reduced to their
non-indexed counterparts, it only remains to show that |M| types can be,
reduced
to |W| types. This is a result from our previous work on
containers~\cite{alti:cont-tcs}, though in the setting of indexed |WI| types,
we can give a better intuition.

In category theory, an $\omega$-chain, is an infinite diagram:

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
Chain = Σ* A ∶ (ℕ → Set) *Σ ((n : ℕ) → A (suc n) → A n)

\end{code}

The limit of a chain is an object |X| and family of projections 
$\pi_{n} \in \mbox{|X|} → \mbox{|A|}_{n}$ such that in the following diagram, 
all the small triangles commute:

\[
\xymatrix{
|A|_{|0|} &
\ar[l]_{|a|_{|0|}}
|A|_{1} &
\ar[l]_{|a|_{|1|}}
|A|_{2} &
\cdots &
|A|_{n-|1|} &
\ar[l]_{|a|_{n-1}} 
|A|_{n} &
\ar[l]_{|a|_{n}} 
|A|_{n+|1|} &
\cdots
\\
\\
& & & & 
|X|
\ar[uullll]_{\pi_{|0|}}
\ar[uulll]_{\pi_{|1|}}
\ar[uull]_{\pi_{|2|}}
\ar[uu]_{\pi_{n - |1|}}
\ar[uur]_{\pi_{n}}
\ar[uurr]_{\pi_{n + |1|}}
&&&\\
} 
\]

It is also required that the limit is the terminal cone with this property. 
Again, we can encode the limit of a chain, its projections, and this universal 
property in type theory:

%format π = "\pi"

\begin{code}

LIM : Chain → Set
LIM (A , a) = Σ* f ∶ ((n : ℕ) → A n) *Σ ((n : ℕ) → a n (f (suc n)) ≡ f n)

π : {c : Chain} → (n : ℕ) → LIM c → proj₁ c n
π n (f , p) = f n

comm : {c : Chain} (n : ℕ) (l : LIM c) → proj₂ c n (π {c} (suc n) l) ≡ π {c} n l
comm n (f , p) = p n

univ : {c : Chain} {X : Set} (pro : (n : ℕ) → X → proj₁ c n) 
       (com : (n : ℕ) (x : X) → proj₂ c n (pro (suc n) x) ≡ pro n x) →
       X → LIM c
univ pro com x = (λ n → pro n x) , (λ n → com n x)

\end{code}

Given a functor |F|, we can build a chain:

\[
\xymatrix{
|⊤| &
\ar[l]_{|!|}
|F| |⊤| &
\ar[l]_{|F| |!|}
|F|^{|2|} |⊤| &
\ar[l]_{|F|^{|2|} |!|}
|F|^{|3|} |⊤| &
\cdots &
} 
\]

%format om = "\!^{\omega}"
%format _om = _ om 
%format en = "\!^{" n "}"
%format sen = "\!^{" suc n "}"

\noindent
For the moment denote this chain |F om = ((λ n → F en ⊤) , λ n → F en !)|. 
We know from Asperti and Longo \cite{aspertilongo} that if |F| is 
$\omega$-continuous, \emph{i.e.} that for any chain |(A , a)|:

| F (LIM (A, a)) ≅ LIM ((F ∘ A), (F ∘ a)) |

\noindent
then the limit of |F om| will be the terminal co-algebra of |F|. 

To see this we first observe that we there is an isomorphism between the limit of a chain, and the limit of any of its \emph{tails}:

\begin{code}

tail : Chain → Chain
tail (A , a) = (A ∘ suc , a ∘ suc)

tailLIM : (c : Chain) → LIM c → LIM (tail c)
tailLIM (A , a) (f , p) = f ∘ suc , p ∘ suc

tailLIM⁻¹ : (c : Chain) → LIM (tail c) → LIM c
tailLIM⁻¹ (A , a) (f , p) = f′ , p′ 
  where f′ : (n : ℕ) → A n
        f′ zero = a _ (f zero)
        f′ (suc n) = f n
        p′ : (n : ℕ) → a _ (f n) ≅ f′ n
        p′ zero = refl
        p′ (suc n) = p n
 
\end{code}

\noindent 
We also note that the tail of |F om| is |((λ n → F (F en ⊤)) , λ n → F (F en !))|, which allows us to construct the isomorphism between |F (LIM F om)| and 
|LIM F om|:

\begin{align*}
&&& |F (LIM F om)| & \\
&\cong&& | LIM (F ∘ (λ n → F en ⊤) , F ∘ (λ n → F en !)) | & \{\mbox{|F| is $\omega$-continuous}\} \\
&\equiv&& | LIM ((λ n → F (F en ⊤)) , (λ n → F (F en !))) | & \{\mbox{definition}\}\\
&\cong&& | LIM F om | & \{\mbox{ |tailLIM | }\} \\
\end{align*}


This isomorphism is witnessed from right to left by the co-algebra map |out|.
To show that the co-algebra is terminal, we employ the universal property of
|LIM|. Given a co-algebra for |α : X → F X| we construct an |F om| cone:

\[
\xymatrix{
|⊤| &
\ar[l]_{|!|}
|F| |⊤| &
\ar[l]_{|F| |!|}
|F|^{2} |⊤| &
\ar[l]_{|F|^{|2|} |!|}
|F|^{3} |⊤| &
\cdots & \\
|X| 
\ar[u]_{|!|}
\ar[r]_{|f|} &
|F| |X| 
\ar[u]_{|F| |!|}
\ar[r]_{|F| |f|} &
|F|^{2} |X|
\ar[u]_{|F|^{|2|} |!|} 
\ar[r]_{|F|^{|2|} |f|} &
|F|^{3} |X|
\ar[u]_{|F|^{|3|} |!|} 
 &
\cdots \\
}
\]

We want to build |M|-types, which we know to be the terminal co-algebras of 
container functors. In order to do this, we must construct 
iteration of container functors (to build the chain) and show that all container
functors are $\omega$ continuous.

Since we only need to build iterations of container functors applied to the 
terminal object |⊤|, we build that directly. We define the following variation 
of |W|, cut off at a know depth:

\begin{code}

data WM (S : Set) (P : S → Set) : ℕ → Set where
  wm⊤ : WM S P zero
  sup : ∀ {n} → Func.obj ⟦ S ◁ P ⟧ (WM S P n) → WM S P (suc n)

\end{code}

\noindent
It should be obvious that |WM zero| is indeed terminal in |Set| and that 
|⟦ S ◁ P ⟧ (WM S P n) ≅ WM S P (suc n)|, so upto to isomorphism, this just the 
thing we need to construct |⟦ S ◁ P ⟧|$^{\omega}$.

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
morphism into the terminal object:

\begin{code}

trunc : ∀ {S P} → (n : ℕ) → WM S P (suc n) → WM S P n
trunc zero (sup (s , f)) = wm⊤
trunc (suc n) (sup (s , f)) = sup (s , trunc n ∘ f)

\end{code}

So now we can build the chain of finite iterations of a container functor:

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
| F (LIM (A, a)) ≅ LIM ((F ∘ A), F ∘ a) | in the case that |F|
is a container functor. However, the function from left to right is uniquely 
given by the universal property of |LIM| for all functors |F : Set → Set|. 
To show this we build the cone for the chain |((F ∘ A), F ∘ a)|:


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
  ω-cont :  LIM  (  (  λ n → Σ* s ∶ S *Σ (P s → A n))
                 ,     λ n → split s & f tilps ↦  (s , a n ∘ f) !m !s
                 ) 
          → Σ* s ∶ S *Σ (P s → (LIM (A , a)))
\end{code}

Note that the shape picked at every point along the chain must be the same, in 
order to make the diagrams commute. This is the key insight
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
