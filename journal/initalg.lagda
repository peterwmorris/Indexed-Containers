
%if style==code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module initalg where

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
open import icont

\end{code}

%endif

%format commβ = comm β

\section{Initial Algebras of Indexed Containers}
\label{sec:initalg}

We will now examine how to construct the parameterised initial algebra
of an indexed container of the form |F : ICont* (I ⊎ J) J|. The shapes of such
a container are an |J|-indexed family of |Set|s and the positions are
indexed by |I ⊎ J|; we will treat these position as two separate
entities, those positions indexed by |I| -- the recursive positions --
and those by |J| -- the payload positions.

The shapes of initial algebra we are constructing will be trees with S
shapes at the nodes and which branch over the recursive |PI|
positions. We call these trees \emph{indexed} |W|-types, denoted |WI|,
and they are the initial algebra of the functor |⟦ S ◁ PJ ⟧*|. In
Agda, we can implement the |WI| constructor and its associated 
iteration operator |WIfold| as follows:

\begin{code}

data WI  {J : Set} (S : J → Set) 
         (PJ : (j : J) → S j → J → Set) : J → Set where
  sup : obj* ⟦ S ◁* PJ ⟧* (WI S PJ)  -*-> WI S PJ 



\end{code}

\begin{proposition}
|(WI S PJ , sup)| is the initial object in the category of |⟦ S ◁ PJ ⟧|-algebras.
\end{proposition}

We show this by constructing the iteration operator |WIfold|, a morphism in the 
category of |⟦ S ◁ PJ ⟧|-algebras from our candidate initial algebra to any 
other algebra. Such that the following diagram commutes:

\[
\xymatrix{
\mbox{|obj* ⟦ S ◁* PJ ⟧* (WI S PJ)|}  \ar[rr]^{\quad\mbox{\quad\;\;|sup|}} 
\ar[d]_{\mbox{|mor*  ⟦ S ◁* PJ ⟧* (WIfold α)|}} & 
\quad\;\;&
\mbox{|WI S PJ|} \ar[d]^{\mbox{|WIfold α|}}\\
\mbox{|obj* ⟦ S ◁* PJ ⟧* X|} \ar[rr]^{\quad\mbox{\quad\;\;|α|}} & & \mbox{|X|}}
\]

\noindent
In fact we can use this specification as the definition of |WIfold|:

\begin{code}

WIfold :  ∀  {J} {X : J → Set} {S : J → Set} 
             {PJ : (j : J) → S j → J → Set} →
             obj* ⟦ S ◁* PJ ⟧* X -*-> X → WI S PJ -*-> X
WIfold {S = S} {PJ = PJ} α j (sup ._ x) = α j (mor*  ⟦ S ◁* PJ ⟧* (WIfold α) j x) 

\end{code}

\noindent
We also require that |WIfold| is \emph{unique}, that is we must show that any 
morphism |β| which makes the diagram above commute must be equal to |WIfold α|:

%if style==code

\begin{code}

{-

\end{code}

%endif

\begin{code}

WIfolduniq : ∀  {J} {X : J → Set} {S : J → Set} 
             {PJ : (j : J) → S j → J → Set} 
             (α : obj* ⟦ S ◁* PJ ⟧* X -*-> X) →
             (β : WI S PJ -*-> X) → (β ⊚ sup) ≡ (α ⊚ mor* ⟦ S ◁* PJ ⟧* β) →
             β ≡ WIfold α
WIfolduniq α β commβ  = ext λ j → ext λ { (sup ._ (s , g)) → 
  trans (ext⁻¹ (ext⁻¹ commβ j)  (s , g)) 
    (cong (λ f → α j (s , f)) 
      (ext λ j′ → ext λ x′ →  
         ext⁻¹ (ext⁻¹ (WIfolduniq α β commβ) j′) (g j′ x′))) }  

\end{code}

%if style==code

\begin{code}

-}

sup⁻¹ : {J : Set} {S : J → Set} {PJ : (j : J) → S j → J → Set} 
        {j : J} {C : WI S PJ j → Set} → 
        ((x : obj* ⟦ S ◁* PJ ⟧* (WI S PJ) j) → C (sup j x)) →
        (w : WI S PJ j) → C w
sup⁻¹ m (sup ._ x) = m x

-- annoyingly I'm going to have to leve this other version of uniq here, 
-- because I don't want to redo the proof in initalgok

WIfolduniq : ∀  {J} {X : J → Set} {S PJ} 
             (α : obj* ⟦ S ◁* PJ ⟧* X -*-> X) →
             (β : WI S PJ -*-> X) → 
             ((j : J) (x : obj* ⟦ S ◁* PJ ⟧* (WI {J} S PJ) j) → β j (sup _ x) ≡ α j (proj₁ x , (λ j′ p → β j′ (proj₂ x j′ p)))) →
             ((j : J) (x : WI S PJ j) → β j x ≡ WIfold α j x)
WIfolduniq α β commβ j (sup ._ y) = trans (commβ j y) (cong (λ f → α j (proj₁ y , f)) (ext (λ j′ → ext (λ p → WIfolduniq α β commβ j′ (proj₂ y j′ p)))))

\end{code}

%endif

\noindent This mirrors the construction for plain containers, where we
can view ordinary |W|-types as the initial algebra of a container
functor.  Positions in an indexed |W|-type are given by the paths through
such a tree which terminate in a non-recursive |PI|-position:

\begin{code}

data Path  {I J : Set} (S : J → Set)  
           (PI  : (j : J) → S j → I  → Set) 
           (PJ  : (j : J) → S j → J  → Set) 
           : (j : J) → WI S PJ j → I → Set where
  path : ∀  {j s f i} →     
               PI j s i 
            ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path S PI PJ j′ (f j′ p) i)) 
            → Path S PI PJ j (sup _ (s , f)) i 

\end{code}

\noindent Again this mirrors the partial application construction
where positions were given by a |PJ| position at the top level, or a
pair of a |PJ| position and a sub |Q| position. Here the |Q| positions
are recursive |Path| positions. This reflects the fact that a
|WI|-type can be thought of as iterated partial application.  
We can now use |WI|-types, or
equivalently initial algebras of indexed contianers, to construct the
parametrised initial algebra of an indexed container. Firstly we
construct the carrier of the parameterised initial algebra:

%format μ = "\mu"
%format μ^C = μ ^C


\begin{code}

μ^C : {I J : Set} → ICont* (I ⊎ J) J → ICont* I J
μ^C {I} {J} (S ◁* P) = 
  let  PI  : (j : J) → S j → I  → Set ;  PI  j s i   = P $$ j $$ s $$ (inj₁ i) 
       PJ  : (j : J) → S j → J  → Set ;  PJ  j s j′  = P $$ j $$ s $$ (inj₂ j′)
  in   WI S PJ ◁* Path S PI PJ
\end{code}

%format in^C = "\Varid{in}" ^C
%format fold^C = fold ^C
%format unfold^C = unfold ^C

\noindent Next, we note that the structure map for this
parameterised initial algebra is a container morphism from the partial
application of |F| and its parametrised initial algebra, to the
parameterised initial algebra. This structure map is given by the
constructor |sup| of |WI| and the deconstructor for |Path|:

%if style==code

\begin{code}

pathminusone :  {I J : Set} {S : J → Set}  
                {PI  : (j : J) → S j → I  → Set} 
                {PJ  : (j : J) → S j → J  → Set} 
                → {j : J} → {s : S j} {f : PJ j s -*-> WI S PJ} → {i : I} → Path S PI PJ j (sup _ (s , f)) i →
           PI j s i  ⊎  (Σ J λ j′ → Σ (PJ j s j′) λ p → Path S PI PJ j′ (f j′ p) i)
pathminusone (path p) = p

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F = sup ◁* λ _ _ p → pathminusone p

{-

\end{code}

%endif

\begin{code}

in^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ μ^C F ⟩C* ⇒* μ^C F
in^C F = sup ◁* λ {_ _ (path p) → p} 

\end{code}

\begin{proposition}
|(μ^C F , in^C F)| is initial in the category of parameterised |F|-algebras of indexed containers. Further, by full and faithfulness, |(⟦ μ^C F ⟧* , ⟦ in^C F ⟧⇒*)| willl also be initial in the indexed functor case.
\end{proposition}

To show this we must define an interation operator |fold^C| from the initial 
object. The shape map employs the fold for |WI| directly. For the position map we apply the position map for the algebra, which maps |Q| positions to either a |P| position in the first layer, or a recursive |Q| position --- it is straight forward to recursive employ this prsition map to construct the correspondin |Path| to a |P| position {\em somewhere} in the tree.

%if style == newcode

\begin{code}

-}

Pathfold : ∀  {I J}  (S : J → Set) (PI  :  (j : J) → S j → I  → Set) 
                                   (PJ  :  (j : J) → S j → J  → Set) 
                     (G : ICont* I J) 
                     (f : (i' : J) → Σ (S i') (λ s' → (i0 : J) → PJ i' s' i0 → G projS* $$ i0) → G projS* $$ i')  
                     (r : {j : J}
                          (s' : Σ (S j) (λ s0 → (i' : J) → PJ j s0 i' → G projS* $$ i')) (i' : I)
                          →
                          G projP* $$ j $$ (f j s') $$ i' →
                          PI j (proj₁ s') i' ⊎
                          Σ J
                          (λ j' →
                             Σ (PJ j (proj₁ s') j') (λ p' → G projP* $$ j' $$ (proj₂ s' j' p') $$ i'))) →
              {j : J} (s : WI S PJ j) (i : I) → G projP* $$ j $$ (WIfold f j s) $$ i → Path S PI PJ j s i
Pathfold S PI PJ G f r (sup ._ (s , g)) i p = path (Data.Sum.map id (λ jpq → (proj₁ jpq , (proj₁ (proj₂ jpq) , Pathfold S PI PJ G f r _ _ (proj₂ (proj₂ jpq))))) (r (s , _) i p))


fold^C : ∀  {I J} (F : ICont* (I ⊎ J) J) {G : ICont* I J} → 
            F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} (S ◁* P) {T ◁* Q} (f ◁* r) = ffold ◁* rfold 
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i   = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′  = P j s (inj₂ j′)
           ffold = WIfold f
           rfold :  {j : J} (s : WI S PJ j) 
                    (i : I) → Q j (ffold j s) i → Path S PI PJ j s i
           rfold  = Pathfold S PI PJ (T ◁* Q) f r

{-

\end{code}

%endif


\begin{code}


fold^C : ∀  {I J} (F : ICont* (I ⊎ J) J) {G : ICont* I J} → 
            F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} (S ◁* P) {T ◁* Q} (f ◁* r) = ffold ◁* rfold 
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i   = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′  = P j s (inj₂ j′)
           ffold = WIfold f
           rfold :  {j : J} (s : WI S PJ j) 
                    (i : I) → Q j (ffold j s) i → Path S PI PJ j s i
           rfold (sup (s , g)) i p  = 
             path ((id map⊎ (λ { (j , p , q) → (j , p , rfold _ _ q) })) (r (s , _) i p))

\end{code}

%if style == code

\begin{code} 


-}

postulate dotdotdot : ∀ {l} {A : Set l} → A

\end{code}

%endif


\noindent
We also need to show that the following diagram commutes for any parametrised algebra |( G , α )|:

\[
\xymatrix{
\mbox{|F ⟨ μ^C F ⟩C*|}  \ar[rr]^{\quad\mbox{|in^C F|}} 
\ar[d]_{\mbox{|F ⟨ (fold^C F α) ⟩M*|}} & 
\quad&
\mbox{|μ^C F|} \ar[d]^{\mbox{|fold^C F α|}}\\
\mbox{|F ⟨ G ⟩C*|} \ar[rr]^{\quad\mbox{|α|}} & &\mbox{|G|}}
\]

\noindent
Or, equivalently:


\begin{code}
foldComm : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
              (α : F ⟨ G ⟩C* ⇒* G) →
              (comp^C* (fold^C F α) (in^C F)) ≡
                (comp^C* α (F ⟨ (fold^C F α) ⟩CM*))           
\end{code}


%if style == newcode

\begin{code}

foldComm = dotdotdot

{-

\end{code}

%endif

\noindent
The proof of |foldComm| follows immediately from function extenstionality. All that remains for us to show in order to prove that |(μ^C F , in^C F)| is the initial parametrised |F|-algebra is to show that |fold^C F α| is \emph{unique} for any |α|. That is any morphism |β : μ^C F ⇒* G|, that makes the above diagram commute, must be |fold^C F α|:

\begin{code}
foldUniq : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
              (α : F ⟨ G ⟩C* ⇒* G) (β : μ^C F ⇒* G) → 
              (comp^C* β (in^C F))  ≡ (comp^C* α (F ⟨ β ⟩CM*)) →
              β  ≡ (fold^C F α)
\end{code}

\noindent
That the shape maps of |β| and |fold^C F α| agree follows from the uniqueness of |WIfold|; while the proof that the position maps agree follows the same inductive structure as |rfold| in the definition of |fold^C|. 

%if style == newcode

\begin{code}

-}

\end{code}

\begin{code}


module Pathkk {I J : Set} (S : J → Set)  
        (PI  : (j : J) → S j → I  → Set) 
        (PJ  : (j : J) → S j → J  → Set) (i : I) where


  PathS : Σ J (WI S PJ) → Set
  PathS (j , sup ._ (s , f)) = PI j s i ⊎ Σ J (PJ j s)
  PathP : (iw : Σ J (WI S PJ)) (s : PathS iw) → Σ J (WI S PJ) → Set
  PathP (j , sup ._ (s , f)) (inj₁ p) (j′ , w′) = ⊥
  PathP (j , sup ._ (s , f)) (inj₂ (j′′ , p)) (j′ , w′) = 
          (j′′ ≡ j′) × (f j′′ p ≅ w′)

  Pathk : (j : J) → WI S PJ j → Set 
  Pathk j w = WI PathS PathP (j , w) 

open Pathkk

{-

pathk : {I J : Set} {S : J → Set}  
           {PI  : (j : J) → S j → I  → Set} 
           {PJ  : (j : J) → S j → J  → Set} 
           → {j : J} → {s : S j} {f : PJ j s -*-> WI S PJ} → {i : I} → 
           PI j s i  ⊎  (Σ J λ j′ → Σ (PJ j s j′) λ p → Pathk S PI PJ i j′ (f j′ p))        → Pathk S PI PJ i j (sup (s , f)) 
pathk (inj₁ p) = sup (inj₁ p , λ j ())
pathk {I} {J} {S} {PI} {PJ} {j} {s} {f} {i} (inj₂ (j′′ , (q , r))) = sup ((inj₂ (j′′ , q)) , sub) 
  where sub : (jw : Σ J (WI S PJ)) →
                 (j′′ ≡ proj₁ jw) × (f j′′ q ≅ proj₂ jw) → Pathk S PI PJ i (proj₁ jw) (proj₂ jw) 
        sub (j′ , w′) (eqj , eqw) = subst (WI _ _) (cong₂ _,_ eqj eqw) r 

-}

\end{code}

%endif
