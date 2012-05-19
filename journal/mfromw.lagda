
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module mfromw where

open import Level hiding (zero; suc)
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
open import tt hiding (Func)
open import cont

\end{code}

%endif

\subsection*{|M| from |W|}
\label{sec:mfromw}

Since we have shown that both |WI| and |MI| types can be reduced to
their non-indexed counterparts, we can finish the reduction of the
logical theory of indexed containers to |W|-types by showing that |M|
types can be reduced to |W| types. This is a result from our previous
work on containers~\cite{alti:cont-tcs}, though in the setting of
indexed |WI| types, we can give a better explanation. Before tackling
this question directly, we first introduce the basic definitions
pertaining to final coalgebras and our implementation of them within
Agda.

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

\noindent
In type-theory, we can represent such a chain as a pair of functions:

\begin{code}

Chain : Set₁
Chain = Σ* A ∶ (ℕ → Set) *Σ ((n : ℕ) → A (suc n) → A n)

\end{code}

\noindent
A cone for a chain is an object |X| and family of projections 
$\pi_{n} \in \mbox{|X|} → \mbox{|A|}_{n}$ such that, in the following diagram, 
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

\noindent
The limit of a chain is the cone which is terminal amongst all cones
for that chain. This terminality condition is called the universal
property of the limit. We can encode the limit of a chain, including its
projections and its universal property as follows:

%format π = "\pi"

\begin{code}

LIM : Chain → Set
LIM (A , a) =  Σ* f ∶ ((n : ℕ) → A n) *Σ 
                ((n : ℕ) → a n (f (suc n)) ≡ f n)

π : {c : Chain} → (n : ℕ) → LIM c → proj₁ c n
π n (f , p) = f n

comm :  {c : Chain} (n : ℕ) (l : LIM c) → 
        proj₂ c n (π {c} (suc n) l) ≡ π {c} n l
comm n (f , p) = p n

univ :  {c : Chain} {X : Set} (pro : (n : ℕ) → X → proj₁ c n) 
        (com :  (n : ℕ) (x : X) → 
                proj₂ c n (pro (suc n) x) ≡ pro n x) →
        X → LIM c
univ pro com x = (λ n → pro n x) , (λ n → com n x)

\end{code}


\noindent
We are interested in certain $\omega$-chains which can be constructed
from a functor |F| as follows (where |!| is the unique morphism from
any object into the terminal object |⊤|):

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
%format ≈ = "\approx"

\noindent
For the moment denote this chain |F om = ((λ n → F en ⊤) , λ n → F en !)|. 
We know from Asperti and Longo \cite{aspertilongo} that if |F| is 
$\omega$-continuous, \emph{i.e.} that for any chain |(A , a)|:

| F (LIM (A, a)) ≈ LIM ((F ∘ A), (F ∘ a)) |

\noindent then the limit of |F om| will be the terminal co-algebra of
|F|. To see this we first observe that we there is an isomorphism
between the limit of a chain, and the limit of any of its
\emph{tails}: 

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
&\approx&& | LIM (F ∘ (λ n → F en ⊤) , F ∘ (λ n → F en !)) | & \{\mbox{|F| is $\omega$-continuous}\} \\
&\equiv&& | LIM ((λ n → F (F en ⊤)) , (λ n → F (F en !))) | & \{\mbox{definition}\}\\
&\approx&& | LIM F om | & \{\mbox{ |tailLIM | }\} \\
\end{align*}

\noindent
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

\noindent
We now turn to the specific task at hand, namely the construction of
|M|-types from |W|-types, that is the capacity to construct final
coalgebras of container functors from the capacity to construct the
initial algebras of container functors.  In order to do this, we must
construct the iteration of container functors (to build the chain) and
show that all container functors are $\omega$-continuous. Since we
only need to build iterations of container functors applied to the
terminal object |⊤|, we build that directly. We define the following
variation of |W|, cut off at a known depth: 

\begin{code}

data WM (S : Set) (P : S → Set) : ℕ → Set where
  wm⊤ : WM S P zero
  sup : ∀ {n} → Func.obj ⟦ S ◁ P ⟧ (WM S P n) → WM S P (suc n)

\end{code}

\noindent 
Note that |WM| is itself encodable as an indexed |WI| type
(and, by the final result in section~\ref{wifromw}, a |W| type):

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
Our candidate for the final coalgebra of |⟦ S ◁ P ⟧| is, then, the limit of the chain |WM S P|, along with 
the truncation of a tree of depth |suc n| to one of depth |n|.
This truncation
is achieved by the repeated application of the morphism part of the
container functor to the unique morphism into the terminal object. Or, more concretely:

\begin{code}

trunc : ∀ {S P} → (n : ℕ) → WM S P (suc n) → WM S P n
trunc zero (sup (s , f)) = wm⊤
trunc (suc n) (sup (s , f)) = sup (s , trunc n ∘ f)

\end{code}

\noindent
Now we can build the chain of finite iterations of a container
functor whose limit will form the final coalgebra of the container
functor.

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
|F| |A|_{2} &\cdots &
|F| |A|_{n-1} &
\ar[l]_{|F| |a|_{n-1}} 
|F| |A|_{n} &
\!\!\!\!\!\cdots
\\
\\
& & & \!\!\!\!\!\!\!\!\!\!|F (LIM (A , a))|\!\!\!\!\!\!\!\!\!\!
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
                 ,     λ n → λ { (s , f) → (s , a n ∘ f) } ) 
          → Σ* s ∶ S *Σ (P s → (LIM (A , a)))
\end{code}

\noindent
Note that the shape picked at every point along the chain that we a given must 
be the same, in order to make the diagrams commute. This is the key insight
into constructing this function:

\begin{code}

  ω-cont (f , p) = 
   (  proj₁ (f zero) ,  λ x →  
    (  λ n →  proj₂ (f n) (subst P (f₀≡ n) x))
    ,  λ n →  begin 
         a n (proj₂ (f (suc n)) (subst P (f₀≡ (suc n)) x)) 
        ≅⟨ ext≅⁻¹ (cong (P ∘ proj₁) (p n)) (λ≅ _ →≅ refl)
              (cong proj₂ (p n)) 
              (begin 
                  subst P (f₀≡ (suc n)) x 
                ≅⟨ subst-removable P (f₀≡ (suc n)) x ⟩ 
                  x 
                ≅⟨ sym (subst-removable P (f₀≡ n) x) ⟩ 
                  subst P (f₀≡ n) x ∎)⟩ 
         proj₂ (f n) (subst P (f₀≡ n) x) ∎ )
    where  f₀≡ : (n : ℕ) → (proj₁ (f 0)) ≡ (proj₁ (f n))
           f₀≡ zero = refl
           f₀≡ (suc n) = trans (f₀≡ n) (sym (cong proj₁ (p n)))
           open ≅-Reasoning
\end{code}

\end{proof}

Now, since we have established that |M-chain| is isomorphic to the chain of iterations of container functors, and that all container functors are $\omega$-continuous, we know that the terminal co-algebra of a container functor must be the limit of its |M-chain|:

\begin{code}

M : (S : Set) (P : S → Set) → Set
M S P = LIM (M-chain S P)

\end{code}

In this section we have established that we can derive |WI| types from |W| (and by duality we argue |MI| types from |M|) and also |M| types from |W|, by these results we can reduce all the constructions in this paper to the setting of extensional Type-Theory with |W| types, or equivalently, {\em any} Martin-L\"{o}f category. That is to say, in the move from containers to indexed containers, we require no extra structure in our underlying Type-Theory,

