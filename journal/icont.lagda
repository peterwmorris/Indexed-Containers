
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

Following the structure of the previous section, we first define
singly indexed containers which will represent singly indexed
functors, and then we define doubly indexed containers which will
represent doubly indexed functors. To this end, we define an
|I|-indexed container to be given by a set of shapes, and an
|I|-indexed \emph{family} of positions:

\begin{code}

record ICont (I : Set) : Set₁ where
  constructor _◁_
  field
    S : Set
    P : S → I → Set

\end{code}

The above definition shows that an |I|-indexed container is similar to
a container in that it has a set of shapes whose elements can be
thought of as constructors. However, the difference between an
|I|-indexed container and a container lies in the notion of the
positions associated to a given shape. In the case of a container, the positions
for a given shape simply form a set. In the case of an |I|-indexed
container, the positions for a given shape form an |I|-indexed set. If
we think of |I| as a collection of sorts, then not only does
constructor require input to be stored at its positions, but each
of these positions is tagged with an |i : I| and will only store data of sort |i
: I| at that position.  This intuition is formalised by the following
definition which shows how singly indexed containers represent singly
indexed functors

\begin{code}

⟦_⟧ : ∀ {I} → ICont I → IFunc I
⟦_⟧ {I} (S ◁ P) = 
  record  {  obj  = λ A  → Σ* s ∶ S *Σ (P s -*-> A)
          ;  mor  = λ {m (s , f) → (s , m ⊚ f) }
          }

\end{code}

Notice how the extension of an indexed container is very similar to
the extension of a container. In particular, an element of |⟦ S ◁ P ⟧
A| consists of a shape |s : S| and a morphism |P s -*-> A| of
|I|-indexed sets. This latter function assigns to each |i : I|,
and each position |p : P s i| an element of |A i|. If we think
of |I| as a collection of sorts, then this function assigns to each |i
: I|-sorted position, an |i|-sorted piece of data, ie an element of
|A i|. 

Analogously to the generalisation of singly indexed functors to doubly
indexed functors, we can generalise {\bf vs extend} singly indexed
containers to doubly indexed containers. Indeed, a doubly indexed
container, that is an element of |ICont* I J|, is simply a function
from |J| to |ICont I|. Unpacking the definition of such a function
gives us the following definition of a doubly indexed container and
its extension to a doubly indexed functor: {\bf extension of a
container}

\begin{code}
record ICont* (I J : Set) : Set₁ where
  constructor _◁*_
  field
    S : J → Set
    P : (j : J) → S j → I → Set


⟦_⟧* : ∀ {I J} → ICont* I J → IFunc* I J
⟦ S ◁* P ⟧* j = ⟦ S j ◁ P j ⟧


\end{code}



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

%format ^C = "^{\text{\tiny$" C "$}}"
%format ^C* = "^{\text{\tiny$" C "$}^{\star}}"
%format ⇒ = "\Rightarrow" ^C
%format _⇒_ = _ ⇒ _
%format ⇒* = "\Rightarrow" ^C*
%format _⇒*_ = _ "\Rightarrow" ^C* _
%format ⟧⇒ = ⟧ "\mbox{$\!^{\Rightarrow}$}"
%format ⟦_⟧⇒ = ⟦ _ ⟧⇒
%format ⟧⇒* = ⟧ "\mbox{$\!^{\Rightarrow^{\!\star}}$}"
%format ⟦_⟧⇒*_ = ⟦ _ ⟧⇒* _

\noindent We will denote the two projections for an
|ICont| postfix as |_ projS| and |_ projP|. Our methodology of 
reflecting structure on indexed functors as structure on
indexed containers means we must next consider how to reflect
morphisms between indexed functors which can be represented by indexed
containers as morphisms between those indexed containers. We begin by
considering what constitutes a natural transformation between the
extension of an indexed container and an arbitrary indexed functor. We
do this in the singly indexed case as follows:


\begin{align*}
                & |⟦ S ◁ P ⟧ ⇒^F F| & \hspace{1in} (1) \\
  \equiv  \;    & |∫ X ** Σ* s ∶ S *Σ (P s -*-> X) → F X| & \{\mbox{by definition}\} \\
  \approx  \;    & |∫ X ** (s : s) → (P s -*-> X) → F X| & \{\mbox{currying}\} \\
  \approx   \;    & |(s : S) → ∫ X ** (P s -*-> X) → F X| & \{\mbox{commuting end and pi} \} \\
  \approx   \;    & |(s : S) → F (P s)| & \{\mbox{Yoneda}\} \\
\end{align*}


\noindent
Now, if |F| is the extension of an indexed container |T ◁ Q|, we have:

\begin{align*}
           & |⟦ S ◁ P ⟧ ⇒^F ⟦ T ◁ Q ⟧| \hspace{2.2in} (2) \\
 \approx \;  & |(s : S) → Σ* t ∶ T *Σ (Q t -*-> P s)| \\
 \approx \;  & |Σ* f ∶ S → T *Σ ((s : S) → Q (f s) -*-> P s)|
\end{align*}
 
\noindent We will use this last line as the definition for indexed
container morphisms. This definition can be implemented by the
following record type, containing a function on shapes and a family of
contravariant indexed functions on positions:

\begin{code}

record _⇒_ {I} (C D : ICont I) : Set where
  constructor _◁_
  field 
    f : C projS → D projS
    r : (s : C projS) → (D projP $$ (f s)) -*-> (C projP $$ s)

\end{code}

\noindent 
|ICont I| forms a category, with morphisms given by |_⇒_|, the identity and
composition morphisms are given as follows:

%format id^C = id ^C
%format _comp^C_ = _"\circ" ^C _
%format comp^C = "\mathbin{\circ" ^C "}"

\begin{code}

id^C : ∀ {I} {C : ICont I} → C ⇒ C
id^C = id ◁ (λ _ _ → id)

comp^C : ∀ {I} {C D E : ICont I} → D ⇒ E → C ⇒ D → C ⇒ E
comp^C (f ◁ r) (g ◁ q) = (f ∘ g) ◁ (λ s i → q s i ∘ r (g s) i)

\end{code}

\noindent
That |id^C| is the left and right unit of |comp^C|, and that |comp^C| 
is associative follows immediately from the corresponding properties of |id|
and |_∘_|.

We will use a notion of equality for container morphisms that incudes a proof that their shape and position functions are point-wise equal:

%format projf  = "\!." f
%format projr  = "\!." r

%if style==code

\begin{code}

_projf :  ∀ {I} {C D : ICont I} (m : C ⇒ D) → C projS → D projS
_projf = _⇒_.f

_projr : ∀ {I} {C D : ICont I} (m : C ⇒ D) (s : C projS) → (D projP $$ (m projf $$ s)) -*-> (C projP $$ s)
_projr = _⇒_.r

\end{code}

%endif

%format ≡⇒ = "\mathbin{\equiv^{\Rightarrow}}"
%format _≡⇒_ = _ "\equiv^{\Rightarrow}" _

\begin{code}

record _≡⇒_  {I} {C D : ICont I} (m n : C ⇒ D) : Set where
  constructor _◁_
  field
    feq : (s : C projS) → m projf $$ s ≡ n projf $$ s 
    req : (s : C projS) (i : I) (p : D projP $$ (m projf $$ s) $$ i) → 
            m projr $$ s $$ i $$ p ≡ 
              n projr $$ s $$ i $$ subst (λ s' → D projP $$ s' $$ i) (feq s) p

\end{code}

\noindent
In the presence of extensional equality, we can prove that this is equivalent to
the propositional equality on |_⇒_|, but it will prove simpler later to use 
this definition.

%format lhd = _◁_

%if style==code

\begin{code}

postulate ext′ :  ∀ {l l'} {A A' : Set l} {B : A → Set l'} {B' : (a : A') → Set l'}  {f : (a : A) → B a} {g : (a : A') → B' a} → 
                  ((a : A) (a' : A') → a ≅ a' → f a ≅ g a') → f ≅ g

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {D : ∀ x → (y : B x) → C x y → Set d}
          {x y u v s t}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → s ≅ t → f x u s ≅ f y v t
cong₃ f refl refl refl = refl


≡⇒→≡ : ∀ {I} {C D : ICont I} (m n : C ⇒ D) → m ≡⇒ n → m ≡ n
≡⇒→≡ {I} {C} {D} (f ◁ r) (f′ ◁ r′) (feq ◁ req)= cong₂ lhd (ext feq) (ext′ λ s s′ seq → ext′ λ i i′ ieq → ext′ λ p p′ peq → trans (req s i p) (cong₃ r′ seq ieq (trans (subst-removable (λ s' → ICont.P D s' i) (feq s) p) peq)))
  where lhd : (f : C projS → D projS) → ((s : C projS) (i : I) →
                D projP $$ (f s) $$ i → C projP $$ s $$ i) → C ⇒ D
        lhd = _◁_

\end{code}
%endif

We witness the construction of a natural transformation from
an indexed container morphisms as follows:

\begin{code}

⟦_⟧⇒ : ∀ {I}  {C D : ICont I} (m : C ⇒ D)  → 
              ∫ A ** IFunc.obj ⟦ C ⟧ A  ->> IFunc.obj ⟦ D ⟧ A
⟦ f ◁ r ⟧⇒ (s , g) = f s , g ⊚ r s

\end{code}

\noindent
The representation of natural transformations between
indexed functors arising from indexed contianers and morphisms between
the indexed containers themselves is actually a bijection. This
 opens the way to reasoning about natural transformations by
reasoning about indexed container morphisms. Technically, this
bijection is captured by the following statement:

\begin{proposition}

The functor |(⟦_⟧ , ⟦_⟧⇒) : ICont I → IFunc I | is full and faithful.

\end{proposition}

\begin{proof}
The isomorphism is proved in equations (1) and (2).

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

Having dealt with indexed container morphisms in the singly indexed
setting, we now turn to the doubly indexed
setting. First of all, we define the morphisms between two doubly
indexed containers.

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


%format ^C* = "^{\text{\tiny{$" C "$}}\star}"
%format id^C* = id ^C*
%format _comp^C*_ = _"\circ" ^C* _
%format comp^C* = "\mathbin{\circ" ^C* "}"

%format projf*  = "\!." f 
%format projr*  = "\!." r 
%format un*  = "\!" 


%if style == code 

\begin{code}

id^C* : ∀ {I J} {C : ICont* I J} → C ⇒* C
id^C* = (λ j → id) ◁* (λ s i → id)

_comp^C*_ : ∀ {I J} {C D E : ICont* I J} → D ⇒* E → C ⇒* D → C ⇒* E
(f ◁* r) comp^C* (g ◁* q) = (λ j → f j ∘ g j) ◁* (λ s i → q s i ∘ r (g _ s) i) 

\end{code}

%format ≡⇒* = "\mathbin{\equiv^{\Rightarrow^{\star}}}"
%format _≡⇒*_ = _ "\equiv^{\Rightarrow^{\star}}" _

\begin{code}

un* : ∀ {I J} → ICont* I J → J → ICont I
un* (S ◁* P) j = S j ◁ P j


_projf* :  ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) → C projS* $$ j → D projS* $$ j
_projf* m j = _⇒*_.f m j 

_projr* : ∀ {I J} {C D : ICont* I J} (m : C ⇒* D) (j : J) (s : C projS* $$ j) → (D projP* $$ j $$ (m projf* $$ j $$ s)) -*-> (C projP* $$ j $$ s)
_projr* m j = _⇒*_.r m  

record _≡⇒*_  {I} {J} {C D : ICont* I J} (m n : C ⇒* D) : Set where
  constructor _◁*_
  field
    feq : (j : J) (s : C projS* $$ j) → m projf* $$ j $$ s ≡ n projf* $$ j $$ s 
    req : (j : J) (s : C projS* $$ j) (i : I) (p : D projP* $$ j $$ (m projf* $$ j $$ s) $$ i) → 
            m projr* $$ j $$ s $$ i $$ p ≡ 
              n projr* $$ j $$ s $$ i $$ subst (λ s' → D projP* $$ j $$ s' $$ i) (feq j s) p

\end{code}

%endif

%format η^C = η ^C
%format >>=^C = >>= ^C
%format _>>=^C_ = _ >>=^C _

Having defined indexed containers and indexed
containers morphisms as representations of indexed functors and the
natural transfortmations between them, we now turn our attention to
the relative monad structure on indexed functors, reindexing of
indexed functors (and the associated adjoints), and parameterised
inital algebras of indexed functors. Our goal in the rest of this
section is to encode each of these structures within
indexed containers. We begin by showing that, as with |IFunc|, we can
equip |ICont| with a relative monadic structure:

\begin{code}

η^C : ∀ {I} → I → ICont I
η^C i = ⊤ ◁ λ _ i′ → i ≡ i′

_>>=^C_ : ∀ {I J} → ICont I → ICont* J I → ICont J
_>>=^C_ {I} (S ◁ P) (T ◁* Q) =  
     (IFunc.obj ⟦ S ◁ P ⟧ T) 
  ◁  λ {(s , f) j → Σ  (Σ* i ∶ I *Σ P s i) (λ { (i , p) → Q i (f i p) j}) }  

\end{code}

%format ≈^C = "\approx^{\text{\tiny{C}}}"

\begin{proposition}

The triple |(ICont , η^C , _>>=^C_)| is a relative monad.

\end{proposition}

\begin{proof}

Instead of proving this directly, we observe that the |η^C| and |_>>=^C_|
are preserved under the extension functor, and by the full and faithfulness of
|⟦_⟧| we can import the result from |IFunc| into |ICont|:

\begin{align*}
|⟦ η^C i ⟧| && \approx &&& |η^F i| \\
|⟦ C >>=^C D ⟧| && \approx &&& |⟦ C ⟧* >>=^F ⟦ D ⟧| \\
\end{align*}

These facts follow from the extensionality of our propositional
equality, the associativity of |Σ| and the terminality of |⊤|. By the
full and faithful nature of the embedding |⟦_⟧|, we can then reuse the
result that |(IFunc , η^F , _>>=^F_)| is a relative monad to establish
the theorem. 

\end{proof}

%format Δ^C = Δ ^C
%format Π^C = Π ^C
%format Σ^C = Σ ^C

As with indexed functors, the re-indexing functor |Δ^C| on indexed
containers is defined by composition, and it has left and right
adjoints |Σ^C| and |Π^C|. As we shall see, our proof of this fact uses
the full and faithfullness of the embedding of indexed containers as
indexed functors and the fact that reindexing of indexed functors has
left and right adjoints.

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
    ◁  λ { (j , eq , s) → P j s }
 
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

Again we appeal to the full and faithfulness of |⟦_⟧| and show instead
that |⟦_⟧| also preserves these constructions. That, is we want to
show that the following three statements hold:

\begin{align*}
|⟦ Σ^C f F j ⟧| && \approx &&& |Σ^F f ⟦ F ⟧* j| \\
|⟦ Δ^C f F j ⟧| && \equiv &&& |Δ^F f ⟦ F ⟧* j| \\
|⟦ Π^C f F j ⟧| && \approx &&& |Π^F f ⟦ F ⟧* j| \\
\end{align*}

These can be proved simply by employing the associativity of |Σ|.

\end{proof}

%format ✧ = "\lozenge"

%format ⟩C = ] ^C
%format ⟩C*  = ] ^C*
%format _⟨_⟩C = _ ⟨ _ ⟩C
%format _⟨_⟩C* = _ ⟨ _ ⟩C*
%format ⟩CM = ] ^C
%format _⟨_⟩CM = _ ⟨ _ ⟩CM 
%format ⟩CM* = ] ^C*
%format _⟨_⟩CM* = _ ⟨ _ ⟩CM* 

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
            (λ {(s , f) i → PI s i
         ⊎  (Σ* j ∶ J *Σ (Σ* p ∶ PJ s j *Σ Q j (f j p) i))})

\end{code}

\noindent
The composite container has shapes given by a shape |s : S| and an assignment
of |T| shapes to |PJ s| positions. Positions are then a choice between a
|I|-indexed position, or a pair of an |J|-indexed position, and a |Q|
position \emph{underneath} the appropriate |T| shape. 

%if style==newcode

\begin{code}

_⟨_⟩C* : ∀ {I J K} → ICont* (I ⊎ J) K → ICont* I J →  ICont* I K
_⟨_⟩C* C D = λ* λ k → (C $* k) ⟨ D ⟩C

_map⊎_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
       (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
a map⊎ b = λ c -> Data.Sum.map a b c

\end{code}

%endif

%format map⊎ = ⊎


\noindent
As with indexed functors, this construction is functorial in its second 
argument, and lifts container morphisms in this way:

%if style==code

\begin{code}

{-

\end{code}

%endif 

\begin{code}

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* I J} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  λ {(s , f) → (s , λ j p → γ projf* $$ j $$ (f j p))}) ◁ 
     λ {(s , f) i → id map⊎ λ { (j , p , q) → (j , p , γ projr* $$ j $$ (f j p) $$ i $$ q) } } 

\end{code}


%if style==code

\begin{code}

-}

_⟨_⟩CM :  ∀  {I J} (C : ICont (I ⊎ J)) {D E : ICont* I J} → 
                    D      ⇒*        E        
             → C ⟨  D ⟩C   ⇒    C ⟨  E ⟩C  
C ⟨ γ ⟩CM = 
  (  λ {(s , f) → (s , λ j p → γ projf* $$ j $$ (f j p))}) ◁ 
     λ {(s , f) i → id map⊎ (λ jpq → (proj₁ jpq , proj₁ (proj₂ jpq) , (γ projr* $$ proj₁ jpq $$ f (proj₁ jpq) (proj₁ (proj₂ jpq)) $$ i $$ proj₂ (proj₂ jpq) ))) } 


_⟨_⟩CM* :  ∀  {I J K} (C : ICont* (I ⊎ J) K) {D E : ICont* I J} → 
                    D       ⇒*         E        
             → C ⟨  D ⟩C*   ⇒*    C ⟨  E ⟩C*  
C ⟨ γ ⟩CM* = (λ {k (s , f) → (s , λ j p → γ projf* $$ j $$ (f j p))}) ◁* 
              λ { (s , f)  i → (id map⊎ (λ jpq → (proj₁ jpq , proj₁ (proj₂ jpq) , (γ projr* $$ proj₁ jpq $$ f (proj₁ jpq) (proj₁ (proj₂ jpq)) $$ i $$ proj₂ (proj₂ jpq) )))) } 
 
\end{code}

%endif
