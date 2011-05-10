
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module icont where

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
open import ifunc

\end{code}

%endif

\section{Indexed containers}
\label{sec:icont}

%format _◁_ = "\_\mbox{$\lhd$}\_"
%format ICont* = ICont *
%format ⟧* = ⟧ *
%format ◁* = ◁ *
%format _◁*_ = _ ◁* _
%format ICont.S = _ "." S
%format ICont.P = _ "." P
%format projS  = "\!." S
%format projP  = "\!." P
%format projS*  = projS 
%format projP*  = projP 
%format $* = "\!\!"
%format λ* = "\!\!"

An |I|-indexed container is given by a set of shapes, and an |I|-indexed \emph{family} of positions:

\begin{code}

record ICont (I : Set) : Set₁ where
  constructor _◁_
  field
    S : Set
    P : S → I → Set

\end{code}

The extension of such a container is an |IFunc I|:

\begin{code}

⟦_⟧ : ∀ {I} → ICont I → IFunc I
⟦_⟧ {I} (S ◁ P) = 
  record  {  obj  = λ A  → Σ* s ∶ S *Σ (P s -*-> A)
          ;  mor  = λ m  → split s & f tilps ↦ (s , m ⊚ f) !m !s }

\end{code}

As with |IFunc| we can extend this notion to doubly indexed containers, where
an |ICont* I J| is a function from |J| to |ICont I|:

\begin{code}
record ICont* (I J : Set) : Set₁ where
  constructor _◁*_
  field
    S : J → Set
    P : (j : J) → S j → I → Set


⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ S ◁* P ⟧* i = ⟦ S i ◁ P i ⟧


\end{code}

We will denote the two projections for an |ICont| postfix as |_ projS| and
|_ projP|. 

%if style == code 

\begin{code}

_projS : ∀ {I} → ICont I → Set
_projS = ICont.S

_projP : ∀ {I} → (C : ICont I) → ICont.S C → I → Set
_projP = ICont.P

_projS* : ∀ {I J} → ICont* J I → I → Set
_projS* C = ICont*.S C 

_projP* : ∀ {I J} → (C : ICont* J I) → (i : I) → ICont*.S C i → J → Set
_projP* C = ICont*.P C

_$*_ : ∀ {I J} → ICont* I J → J → ICont I
(S ◁* P) $* j = S j ◁ P j

λ* : ∀ {I J} → (J → ICont I) → ICont* I J
λ* F = (λ j → (F j) projS) ◁* (λ j → (F j) projP)

\end{code}

%endif

%format ^C = "^{\text{\tiny C}}"
%format ^C* = "^{\text{\tiny C}^{\star}}"
%format ⇒ = "\Rightarrow" ^C
%format _⇒_ = _ ⇒ _
%format ⇒* = "\Rightarrow" ^C*
%format _⇒*_ = _ "\Rightarrow" ^C* _
%format ⟧⇒ = ⟧ "\mbox{$\!^{\Rightarrow}$}"
%format ⟦_⟧⇒ = ⟦ _ ⟧⇒
%format ⟧⇒* = ⟧ "\mbox{$\!^{\Rightarrow^{\!\star}}$}"
%format ⟦_⟧⇒*_ = ⟦ _ ⟧⇒* _

\noindent
We can establish what denotes a morphism between a container |S ◁ P : ICont I|
and functor |F : IFunc I|, simply by expanding the definition and employing 
the following derivation:

\begin{align*}
                & |⟦ S ◁ P ⟧ ⇒^F F| & \\
  \equiv  \;    & |∫ X ** Σ* s ∶ S *Σ (P s -*-> X) → F X| & \{\mbox{by definition}\} \\
  \approx  \;    & |∫ X ** (s : s) → (P s -*-> X) → F X| & \{\mbox{currying}\} \\
  \approx   \;    & |(s : S) → ∫ X ** (P s -*-> X) → F X| & \{\mbox{commuting end and pi} \} \\
  \approx   \;    & |(s : S) → F (P s)| & \{\mbox{Yoneda}\} \\
\end{align*}

\noindent
If |F| is also an indexed container |T ◁ Q| then we have:

\begin{align*}
           & |⟦ S ◁ P ⟧ ⇒^F ⟦ T ◁ Q ⟧| \\
 \approx \;  & |(s : S) → Σ* t ∶ T * *Σ (Q t -*-> P s)| \\
 \approx \;  & |Σ* f ∶ S → T *Σ ((s : S) → Q (f s) -*-> P s)|
\end{align*}
 
We will use this last line as the definition for container morphisms, captured by 
this record type:  

\begin{code}

record _⇒_ {I} (C D : ICont I) : Set₁ where
  constructor _◁_
  field 
    f : C projS → D projS
    r : (s : C projS) → (D projP $$ (f s)) -*-> (C projP $$ s)

\end{code}

\noindent
We witness one side of the isomorphism between container morphisms and natural 
transformations:

\begin{code}

⟦_⟧⇒ : ∀ {I}  {C D : ICont I} (m : C ⇒ D)  → 
              ∫ A ** IFunc.obj ⟦ C ⟧ A  ->> IFunc.obj ⟦ D ⟧ A
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ⊚ r s

\end{code}

\begin{proposition}

The functor |(⟦_⟧_ , ⟦_⟧⇒_)| in |[ ICont I , IFunc I ]| is full and faithful.

\end{proposition}

\begin{proof}

By construction.

%%\begin{code}
%%
%%q : {I : Set} (C D : ICont I) → ({A : I → Set}  → IFunc.obj ⟦  C ⟧ A  → IFunc.%%obj ⟦  D ⟧ A) 
%%                                                →              C      ⇒       %%       D
%%q C D m = (proj₁ ∘ eureka) ◁ (proj₂ ∘ eureka)
%% where
%%  eureka : (s : C projS) → IFunc.obj ⟦ D ⟧ (C projP $$ s)
%%  eureka s =  m (s , idd)
%%
%%\end{code}
%%
%%By naturality this must be the unique inverse to the extesion of a container
%%morphism given above.
%%

\end{proof}

We can lift this functor to the doubly indexed variant:

\begin{code}

record _⇒*_ {I J} (C D : ICont* I J) : Set₁ where
  constructor _◁*_
  field 
    f : C projS* -*-> D projS*
    r : {j : J} (s : C projS* $$ j) → (D projP* $$ j $$ (f j s)) -*-> (C projP* $$ j $$ s)


⟦_⟧⇒* : ∀  {I J} {C D : ICont* I J} (m : C ⇒* D) → 
           ∫ A ** (obj* ⟦ C ⟧* A  -*-> obj* ⟦ D ⟧* A)
⟦ f ◁* r ⟧⇒* j = ⟦ (f j) ◁ r ⟧⇒  

\end{code}

%format projf  = "\!." f
%format projr  = "\!." r
%format projf*  = "\!." f 
%format projr*  = "\!." r 
%format un*  = "\!"  

%if style == code 

\begin{code}

un* : ∀ {I J} → ICont* I J → J → ICont I
un* (S ◁* P) j = S j ◁ P j

_projf :  ∀ {I} {C D : ICont I} (m : C ⇒ D) → C projS → D projS
_projf = _⇒_.f

_projr : ∀ {I} {C D : ICont I} (m : C ⇒ D) (s : C projS) → (D projP $$ (m projf $$ s)) -*-> (C projP $$ s)
_projr = _⇒_.r

_projf* :  ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) → C projS* $$ j → D projS* $$ j
_projf* m j = _⇒*_.f m j 

_projr* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) (s : C projS* $$ j) → (D projP* $$ j $$ (m projf* $$ j $$ s)) -*-> (C projP* $$ j $$ s)
_projr* m j = _⇒*_.r m  

\end{code}

%endif

%format η^C = η ^C
%format >>=^C = >>= ^C
%format _>>=^C_ = _ >>=^C _

As with |IFunc|, we can equip |ICont| with a relative monadic structure:

\begin{code}

η^C : ∀ {I} → I → ICont I
η^C i = ⊤ ◁ λ _ i′ → i ≡ i′

_>>=^C_ : ∀ {I J} → ICont I → ICont* J I → ICont J
_>>=^C_ {I} (S ◁ P) (T ◁* Q) =  
     (IFunc.obj ⟦ S ◁ P ⟧ T) 
  ◁  split s & f tilps j !* ↦ Σ  (Σ* i ∶ I *Σ P s i) (split i & p tilps ↦ Q i (f i p) j !m !s) !m !s  

\end{code}

%format ≈^C = "\approx^{\text{\tiny{C}}}"

\begin{proposition}

The triple |(ICont , η^C , _>>=^C_)| is a relative monad.

\end{proposition}

\begin{proof}

Instead of proving this directly, we observe that the |η^C| and |_>>=^C_|
are preserved under |⟦_⟧_|, i.e.:

\begin{align*}
|⟦ η^C i ⟧| && \approx &&& |η^F i| \\
|⟦ C >>=^C D ⟧| && \approx &&& |⟦ C ⟧* >>=^F ⟦ D ⟧| \\
\end{align*}

Which follow from the extensionality of our propositional equality, the 
associativity of |Σ| and the terminality of |⊤|. By the full and faithful 
nature of the embedding into |IFunc| we can then reuse the result that
|(IFunc , η^F , _>>=^F_)| is a relative monad.

\end{proof}

%format Δ^C = Δ ^C
%format Π^C = Π ^C
%format Σ^C = Σ ^C

As with indexed functors, the re-indexing |Δ^C| is defined by composition, and 
has left and right adjoints |Σ^C| and |Π^C|:

%if style == newcode 

\begin{code}

module DelSigPi {I J K : Set} where

\end{code}

%endif

\begin{code}

  Δ^C : (J → K) → ICont* I K → ICont* I J
  Δ^C f F = λ* λ k → F $* (f k) 

  Σ^C : (J → K) → ICont* I J → ICont* I K
  Σ^C f (S ◁* P) = λ* λ k →  
       (Σ* j ∶ J *Σ (f j ≡ k × S j)) 
    ◁  split j & eq & s tilps ↦ P j s !m !s
 
  Π^C : (J → K) → ICont* I J → ICont* I K
  Π^C f (S ◁* P) =  λ* λ k →  
       ((j : J) → f j ≡ k → S j)
    ◁  λ s i → Σ* j ∶ J *Σ (Σ* eq ∶ f j ≡ k *Σ P j (s j eq) i) 

\end{code}

%if style == newcode 

\begin{code}

open DelSigPi

\end{code}

%endif

\begin{proposition}
|Σ^C| and |Π^C| are left and right adjoint to re-indexing (|Δ^C|).
\end{proposition}

\begin{proof}

Again we appeal to the full and faithfulness of |⟦_⟧_| and show instead that
the embedding into |IFunc| preserves these constructions. That, is we want to show that the following three statements hold:

\begin{align*}
|⟦ Σ^C f F j ⟧| && \approx &&& |Σ^F f ⟦ F ⟧* j| \\
|⟦ Δ^C f F j ⟧| && \equiv &&& |Δ^F f ⟦ F ⟧* j| \\
|⟦ Π^C f F j ⟧| && \approx &&& |Π^F f ⟦ F ⟧* j| \\
\end{align*}

These can be proved simply by employing the associativity of |Σ|.

\end{proof}

%format ✧ = "\lozenge"

%format ⟩C = ] ^C
%format ⟩C*  = ] "^{\text{\tiny{C}}^{\star}}"
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format _⟨_⟩C* = _ ⟨ _ ⟩C*
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 

%format PI = P "^{" I "}"
%format PJ = P "^{" J "}" 

Before we build the initial algebras of indexed containers, it will help to 
define their partial application. 

\begin{code}

_⟨_⟩C : ∀ {I J} → ICont (I ⊎ J) → ICont* I J → ICont I
_⟨_⟩C {I} {J} (S ◁ P) (T ◁* Q) = 
  let  PI  : S  → I  → Set            ;  PI  s  i  = P s (inj₁ i) 
       PJ  : S  → J  → Set            ;  PJ  s  j  = P s (inj₂ j) 
  in   IFunc.obj ⟦ S ◁ PJ ⟧ T ◁     
            (split s & f tilps i !* ↦ PI s i 
         ⊎  (Σ* j ∶ J *Σ (Σ* p ∶ PJ s j *Σ Q j (f j p) i)) !m !s)

\end{code}

\noindent
The composite container has shapes given by a shape |s : S| and an assignment
of |T| shapes to |PJ s| positions. Positions are then a choice between a
|I|-indexed position, or a pair of an |J|-indexed position, and a |Q|
position \emph{underneath} the appropriate |T| shape. 

%if style==code

\begin{code}

_⟨_⟩C* : ∀ {I J K} → ICont* (I ⊎ J) K → ICont* I J →  ICont* I K
_⟨_⟩C* C D = λ* λ k → (C $* k) ⟨ D ⟩C

\end{code}

%endif

\noindent
As with indexed functors, this construction is functorial in its second 
argument, and lifts container morphisms in this way:

\begin{code}

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* I J} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  split s & f tilps ↦ (s , λ j p → γ projf* $$ j $$ (f j p)) !m !s) ◁ 
     split s & f tilps i !* ↦ [ inj₁ , (split j & p & q tilps ↦ inj₂ (j , p , γ projr* $$ j $$ (f j p) $$ i $$ q) !m !s) ] !m !s 

\end{code}
