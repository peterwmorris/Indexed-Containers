
%if style == newcode

\begin{code}

{-# OPTIONS --universe-polymorphism --no-termination-check #-}

module spf where

open import Level
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Sum as Sum
open import Product as Prod
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Coinduction
open import Data.Nat hiding (_⊔_)
open import Relation.Nullary

open import common
open import tt
open import ifunc
open import icont
open import initalg
open import termcoalg

\end{code}

%endif

\section{Strictly Positive Families}

%format ^T = "^{\text{\tiny T}}"

%format η^T = η ^T

%format Δ^T = Δ ^T
%format Π^T = Π ^T
%format Σ^T = Σ ^T
%format μ^T = μ ^T
%format ν^T = ν ^T

%format SPFm = SPF
%format ISPTm = ISPT

%format >>=^T = >>= ^T
%format _>>=^T_ = _ >>=^T _

%format ⟦_⟧^T = ⟦ _ ⟧ ^T
%format ⟧^T = ⟧ ^T
%format ^T* = "^{\text{\tiny T}\star}"
%format ⟦_⟧^T* = ⟦ _ ⟧ ^T*
%format ⟧^T* = ⟧ ^T* 


We now give a syntax for defining indexed strictly positive types and strictly positive families:

\begin{code}

mutual
  SPF : (I J : Set) → Set₁
  SPF I J = J → ISPT I

  data ISPT (I : Set) : Set₁ where
    η^T :          (i : I)                    → ISPT I
    Δ^T : ∀ {J K}  (f : J → K) (F : SPF I K)  → SPF I J
    Σ^T : ∀ {J K}  (f : J → K) (F : SPF I J)  → SPF I K
    Π^T : ∀ {J K}  (f : J → K) (F : SPF I J)  → SPF I K
    μ^T : ∀ {J}    (F : SPF (I ⊎ J) J)        → SPF I J 
    ν^T : ∀ {J}    (F : SPF (I ⊎ J) J)        → SPF I J 

\end{code}

%if style == newcode 

\begin{code}

open DelSigPi

\end{code}

%endif

We intend to interpret terms in this syntax as indexed functors, in order to interpret |μ^T| and |ν^T| we need to go first via indexed containers, which we know to be closed under ther formation of these fixed-points:

\begin{code}

mutual 
  ⟦_⟧^T* : ∀ {I J} → SPF I J → ICont* I J
  ⟦ F ⟧^T* = λ* λ j → ⟦ F j ⟧^T

  ⟦_⟧^T : ∀ {I} → ISPT I → ICont I
  ⟦ η^T i ⟧^T      = η^C i
  ⟦ Δ^T f F j ⟧^T  = un* $$ Δ^C f ⟦ F ⟧^T* $$ j
  ⟦ Σ^T f F k ⟧^T  = un* $$ Σ^C f ⟦ F ⟧^T* $$ k
  ⟦ Π^T f F k ⟧^T  = un* $$ Π^C f ⟦ F ⟧^T* $$ k
  ⟦ μ^T F j ⟧^T    = un* $$ μ^C ⟦ F ⟧^T* $$ j 
  ⟦ ν^T F j ⟧^T    = un* $$ ν^C ⟦ F ⟧^T* $$ j 

\end{code}

We can equip this syntax with a substitution operation, |_>>=^T_|:

%format ISPTmap = ISPT

\begin{code}

mutual 

  ISPTmap : ∀ {I J} → (I → J) → ISPT I → ISPT J
  ISPTmap γ t = t >>=^T (η^T ∘ γ)

  _>>=^T_ : ∀ {I J} → ISPT I → SPF J I → ISPT J
  η^T i      >>=^T F = F i
  Δ^T f G j  >>=^T F = Δ^T f (λ k → G k >>=^T F) j
  Σ^T f G k  >>=^T F = Σ^T f (λ j → G j >>=^T F) k
  Π^T f G k  >>=^T F = Π^T f (λ j → G j >>=^T F) k
  μ^T G j    >>=^T F = μ^T (λ k → G k >>=^T [  (ISPTmap inj₁ ∘ F) , (η^T ∘ inj₂) ]) j
  ν^T G j    >>=^T F = ν^T (λ k → G k >>=^T [  (ISPTmap inj₁ ∘ F) , (η^T ∘ inj₂) ]) j

\end{code}

As defined above this doesn't pass Agda's termination check, due to deriving the |ISPT| from the monad instance. If we define the map of the functor directly the whole thing obviously terminates, at the expense of having to show the two definitions of the map for |ISPT| agree.

%if style == newcode

\begin{code}

monadlaw1 : ∀ {I} (F : ISPT I) → F ≅ F >>=^T η^T 
monadlaw1 (η^T i) = refl
monadlaw1 (Δ^T f F j) = cong (λ F → Δ^T f F j)  (ext λ k → monadlaw1 (F k))
monadlaw1 (Σ^T f F k) = cong (λ F → Σ^T f F k)  (ext λ j → monadlaw1 (F j))
monadlaw1 (Π^T f F k) = cong (λ F → Π^T f F k)  (ext λ j → monadlaw1 (F j))
monadlaw1 (μ^T F j) = cong (λ F → μ^T F j) (ext (λ j → trans (monadlaw1 (F j)) (cong (λ G → F j >>=^T G) (ext [ (λ _ → refl) , (λ _ → refl) ]))))
monadlaw1 (ν^T F j) = cong (λ F → ν^T F j) (ext (λ j → trans (monadlaw1 (F j)) (cong (λ G → F j >>=^T G) (ext [ (λ _ → refl) , (λ _ → refl) ]))))

monadlaw2 :  ∀ {I J K} (F : ISPT I) (G : SPF J I) (H : SPF K J) →
             ((F >>=^T G) >>=^T H) ≡ (F >>=^T λ i → G i >>=^T H)
monadlaw2 (η^T i) G H = refl 
monadlaw2 (Δ^T f F j) G H = cong (λ F → Δ^T f F j) (ext (λ k → monadlaw2 (F k) G H))
monadlaw2 (Σ^T f F k) G H = cong (λ F → Σ^T f F k) (ext (λ j → monadlaw2 (F j) G H))
monadlaw2 (Π^T f F k) G H = cong (λ F → Π^T f F k) (ext (λ j → monadlaw2 (F j) G H))
monadlaw2 (μ^T F j) G H = cong (λ F → μ^T F j) (ext (λ j → trans (monadlaw2 (F j) _ _) (cong (λ G → F j >>=^T G) (ext [ (λ i → trans (monadlaw2 (G i) _ _) (sym (monadlaw2 (G i) _ _))) , (λ _ → refl) ]))))
monadlaw2 (ν^T F j) G H = cong (λ F → ν^T F j) (ext (λ j → trans (monadlaw2 (F j) _ _) (cong (λ G → F j >>=^T G) (ext [ (λ i → trans (monadlaw2 (G i) _ _) (sym (monadlaw2 (G i) _ _))) , (λ _ → refl) ]))))


\end{code}

%endif

\begin{proposition} 
|(ISPT , η^T , _>>=^T_)| is a \emph{relative monad} on the 
lifting functor |↑ : Seti → Setsi|. Moreover, this structure is preserved under the translation to containers |⟦_⟧^T|.
\end{proposition}

\begin{proof}
To prove the structure is a relative 
monad we observe that the following equlities hold:

For |F : ISPT K|, |G : SPF J K|, |H : ISPT I J|:
\begin{align}
|H j|                 &\quad& \equiv &&\quad& |(η^T j) >>=^T H|               \\
|F|                   && \equiv &&& |F >>=^T η^F|                 \\
|(F >>=^T G) >>=^T F| && \equiv &&& |F >>=^T (λ k → (G k) >>=^T H)| 
\end{align}

The first is by definition, and the others follow by induction on |F|. 
To show that the structure is preserved by |⟦_⟧^T| it is sufficient to show that for all |F : ISPT J| and |G : SPF I J| there exist mutually inverse container 
morphisms |bindpres| and |bindpres⁻¹|:

%if style == newcode

\begin{code}

module blah {I J : Set} (F : ISPT J) (G : SPF I J) where

{-

\end{code}

%endif

\begin{code}

  bindpres    :  (⟦ F >>=^T G ⟧^T)         ⇒ (⟦ F ⟧^T >>=^C ⟦ G ⟧^T*)
  bindpres⁻¹  :  (⟦ F ⟧^T >>=^C ⟦ G ⟧^T*)  ⇒ (⟦ F >>=^T G ⟧^T) 

\end{code}



%if style == newcode

\begin{code}

bindpres : ∀ {I J} → (F : ISPT J) (G : SPF I J) → (⟦ F >>=^T G ⟧^T) ⇒ (⟦ F ⟧^T >>=^C ⟦ G ⟧^T*)
bindpres (η^T i) G = 
  (  λ s → _ , (λ i′ eqi → subst (λ i' → ⟦ G i' ⟧^T projS) eqi s)) 
  ◁  λ s i′ → split ieq & p tilps ↦ subst₂′ (λ i' s' → ICont.P ⟦ G i' ⟧^T s' i′) (sym (proj₂ ieq)) (subst-removable (λ i' → ICont.S ⟦ G i' ⟧^T) (proj₂ ieq) s) p !m !s
bindpres (Δ^T f F j) G = bindpres (F (f j)) G
bindpres (Σ^T f F j) G = split j & jeq & s tilps ↦ (j , (jeq , {!!})) , {!!} !m !s ◁ {!!}
bindpres (Π^T f F j) G = {!!}
bindpres (μ^T F j) G = {!!}

-}

\end{code}

%endif

\end{proof}

%format F0 = F "_{0}"
%format F2 = F "_{2}"

%format ⊥^T = ⊥ ^T
%format ⊤^T = ⊤ ^T

%format +^T = "\mathbin{" ⊎ ^T "}"
%format _+^T_ = _ ⊎ ^T _

%format ×^T = "\mathbin{" × ^T "}"
%format _×^T_ = _ × ^T _

%format _≡^T_ = "\mathbin{" ≡ ^T "}"
%format _≡^T_ = _ ≡^T _

%format ⊥^T* = ⊥ ^T
%format ⊤^T* = ⊤ ^T

%format +^T* = "\mathbin{" ⊎ ^T "}"
%format _+^T*_ = _ ⊎ ^T _

%format ×^T* = "\mathbin{" × ^T "}"
%format _×^T*_ = _ × ^T _

We define disjoint union and cartesian product just as we did in the functor and container universes:

\begin{code}

⊥^T : ∀ {I} → ISPT I
⊥^T = Σ^T {J = ⊥} {K = ⊤} _ (λ ()) _  

_+^T_ : ∀ {I} → (F G : ISPT I) → ISPT I 
F +^T G = Σ^T {K = ⊤} _ (λ b → if b then F else G) _

⊤^T : ∀ {I} → ISPT I
⊤^T = Π^T {J = ⊥} {K = ⊤} _ (λ ()) _  

_×^T_ : ∀ {I} → (F G : ISPT I) → ISPT I 
F ×^T G = Π^T {K = ⊤} _ (λ b → if b then F else G) _

\end{code}

%if style == newcode

\begin{code}

⊥^T* : ∀ {I J} → SPF I J
⊥^T* j = ⊥^T  

_+^T*_ : ∀ {I J} → (F G : SPF I J) → SPF I J
(F +^T* G) j = F j +^T G j

⊤^T* : ∀ {I J} → SPF I J
⊤^T* j = ⊤^T  

_×^T*_ : ∀ {I J} → (F G : SPF I J) → SPF I J
(F ×^T* G) j = F j ×^T G j

\end{code}

%endif

%format TFin = T "_{" Fin "}"
%format TVec = T "_{" Vec "}"
%format TScLam = T "_{" ScLam "}"

\begin{code}

TFin : SPF ⊥ ℕ
TFin = μ^T (Σ^T suc (⊤^T* +^T* (η^T ∘ inj₂)))

TVec : SPF ⊤ ℕ
TVec =  μ^T   (     Σ^T {J = ⊤} (λ _ → zero) (λ _ → ⊤^T) 
              +^T*  Σ^T suc (λ n → η^T (inj₁ _) ×^T η^T (inj₂ n)))

TScLam : SPF ⊥ ℕ
TScLam = μ^T  (     (η^T ∘ inj₂)
              +^T*  (((η^T ∘ inj₂) ×^T* (η^T ∘ inj₂))
              +^T*  Δ^T suc (η^T ∘ inj₂)))
\end{code}
