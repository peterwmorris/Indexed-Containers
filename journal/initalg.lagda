
%if style==code

\begin{code}

{-# OPTIONS --universe-polymorphism #-}

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

%format β = "\beta"
%format commβ = comm β

\section{Initial Algebras of Indexed Containers}
\label{sec:initalg}

We will now examine how to construct the parameterised initial algebra
of an indexed container of the form |F : ICont* (I ⊎ J) J|. The shapes of such
a container are an |J|-indexed family of |Set|s and the positions are
indexed by |I ⊎ J|; we will treat these position as two separate
entities, those positions indexed by |J| -- the recursive positions --
and those by |I| -- the payload positions.

The shapes of the initial algebra we are constructing will be trees with S
shapes at the nodes and which branch over the recursive |PJ|
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

\begin{proof}

We show this by constructing the iteration operator |WIfold|, a morphism in the 
category of |⟦ S ◁ PJ ⟧|-algebras from our candidate initial algebra to any 
other algebra such that the following diagram commutes:

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

%if style==code

\begin{code}
{-# NO_TERMINATION_CHECK #-}
\end{code}
%endif

\begin{code}

WIfold :  ∀        {J} {S X : J → Set} {PJ} →  
             obj*  ⟦ S ◁* PJ ⟧* X -*-> X → 
                   WI S PJ  -*-> X 
WIfold {S = S} {PJ = PJ} α j (sup ._ x) = 
   α j (mor*  ⟦ S ◁* PJ ⟧* (WIfold α) j x) 

\end{code}

\noindent
We also require that |WIfold| is \emph{unique}, that is we must show that any 
morphism |β| which makes the diagram above commute must be equal to |WIfold α|:

\begin{code}

WIfoldUniq : ∀  {J} {X : J → Set} {S : J → Set} 
                {PJ : (j : J) → S j → J → Set} 
                (α : obj* ⟦ S ◁* PJ ⟧* X -*-> X) 
                (β : WI S PJ -*-> X) → 
                ((j : J) (s : obj* ⟦ S ◁* PJ ⟧* (WI S PJ) j) → 
                  (β j (sup j s)) ≡ (α j (mor* ⟦ S ◁* PJ ⟧* β j s))) →
                (j : J) (x : WI S PJ j) → β j x ≡ WIfold α j x
WIfoldUniq α β commβ j (sup .j (s , g)) = begin
    β j (sup j (s , g))
  ≅⟨ commβ j (s , g) ⟩ 
    α j (s , (λ j′ p′ → β j′ (g j′ p′))) 
  ≅⟨ cong  (λ f → α j (s , f)) 
           (λ≡ j′ →≡ λ≡ p′ →≡ WIfoldUniq α β commβ j′ (g j′ p′)) ⟩ 
    α j (s , (λ j′ p′ → WIfold α j′ (g j′ p′)))
  ∎
 where open ≅-Reasoning

\end{code}

\noindent
The above definition proves that |β| and |WIfold α| are pointwise equal, by employing |ext| we can show that |WIfoldUniq′| implies that they are extensionally equal.

\end{proof}

%if style==code

\begin{code}

sup⁻¹ : {J : Set} {S : J → Set} {PJ : (j : J) → S j → J → Set} 
        {j : J} {C : WI S PJ j → Set} → 
        ((x : obj* ⟦ S ◁* PJ ⟧* (WI S PJ) j) → C (sup j x)) →
        (w : WI S PJ j) → C w
sup⁻¹ m (sup ._ x) = m x

\end{code}

%endif

This proof mirrors the construction for ordinary containers, where we
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

pathh : ∀ {I J : Set} (S : J → Set)  
          (PI  : (j : J) → S j → I  → Set) 
          (PJ  : (j : J) → S j → J  → Set) 
          {j s f i} →               
               PI j s i 
            ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path S PI PJ j′ (f j′ p) i)) 
           → Path S PI PJ j (sup _ (s , f)) i 
pathh S PI PJ  x = path x

\end{code}



\noindent Again this mirrors the partial application construction
where positions were given by a |PI| position at the top level, or a
pair of a |PJ| position and a recursive |Path| position. This reflects the fact that a
|WI|-type can be thought of as iterated partial application.  
We can now use |WI|-types, or
equivalently initial algebras of indexed containers, to construct the
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
|(μ^C F , in^C F)| is initial in the category of parameterised |F|-algebras of indexed containers. Further, by full and faithfulness, |(⟦ μ^C F ⟧* , ⟦ in^C F ⟧⇒*)| will also be initial in the indexed functor case.
\end{proposition}

To show this we must define an operator |fold^C| from the
initial algebra to an arbitrary algebra.
The shape map employs the fold for |WI| directly. For the position map we apply the position map for the algebra, which maps |Q| positions to either a |P| position in the first layer, or a recursive |Q| position --- it is straightforward to recursively employ this position map to construct the corresponding |Path| to a |P| position {\em somewhere} in the tree.

%if style == newcode

\begin{code}

-}

rfold : ∀  {I J}  (S : J → Set) (PI  :  (j : J) → S j → I  → Set) 
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
rfold S PI PJ G f r (sup ._ (s , g)) i p = path ((id map⊎ (λ jpq → (proj₁ jpq , (proj₁ (proj₂ jpq) , rfold S PI PJ G f r _ _ (proj₂ (proj₂ jpq)))))) (r (s , _) i p))


fold^C : ∀  {I J} (F : ICont* (I ⊎ J) J) {G : ICont* I J} → 
            F ⟨ G ⟩C* ⇒* G → μ^C F ⇒* G
fold^C {I} {J} (S ◁* P) {T ◁* Q} (f ◁* r) = ffold ◁* rfold'
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i   = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′  = P j s (inj₂ j′)
           ffold = WIfold f
           rfold' :  {j : J} (s : WI S PJ j) 
                    (i : I) → Q j (ffold j s) i → Path S PI PJ j s i
           rfold'  = rfold S PI PJ (T ◁* Q) f r

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
           rfold (sup ._ (s , g)) i p  = 
             path ((id map⊎ (λ jpq →  (  _ , proj₁ (proj₂ jpq)
                                      ,  rfold _ _ (proj₂ (proj₂ jpq))))) (r (s , _) i p))

\end{code}

%if style == code

\begin{code} 

-}

\end{code}

%endif


\noindent
We also need to show that the following diagram commutes for any parametrised F-algebra |( G , α )|:

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
              (fold^C F α comp^C* in^C F) ≡⇒*
                (α comp^C* F ⟨ (fold^C F α) ⟩CM*)           
foldComm {F} G α = (λ j x → refl)  ◁* (λ j x i p → refl ) 
\end{code}


\noindent
All that remains for us to show in order to prove that |(μ^C F , in^C F)| is the initial parametrised |F|-algebra is to show that |fold^C F α| is \emph{unique} for any |α|. That is any morphism |β : μ^C F ⇒* G|, that makes the above diagram commute, must be |fold^C F α|:

%format αf = α f
%format αr = α r
%format βf = β f
%format βr = β r

\savecolumns

\begin{code}

foldUniq : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
              (α : F ⟨ G ⟩C* ⇒* G) (β : μ^C F ⇒* G) → 
              (β comp^C* in^C F)  ≡⇒* (α comp^C* F ⟨ β ⟩CM*) →
              β ≡⇒* (fold^C F α)
foldUniq  {I} {J} {S ◁* P} (T ◁* Q) 
          (αf ◁* αr) (βf ◁* βr) (feq ◁* req) = 
    WIfoldUniq αf βf feq ◁* rfoldUniq
  where 
    PI  :  (j : J) → S j → I  → Set ;  PI  j s i   = P j s (inj₁ i) 
    PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′  = P j s (inj₂ j′)
\end{code}

\noindent
That the shape maps of |β| and |fold^C F α| agree follows from the uniqueness of |WIfold|; while the proof that the position maps agree follows the same inductive structure as |rfold| in the definition of |fold^C|. 
\footnote{Some parts of the Agda proof are hidden and denoted by $\dots$.}
%if style == code



\begin{code}
    open ≅-Reasoning   
    rfold′′ :  (j : J) (y : Σ (S j) (λ s → (i' : J) → PJ j s i' → WI S PJ i'))
               (i : I) (f : (j : J) → WI S PJ j → T j) 
               (r :  (j' : J) (p' : PJ j (proj₁ y) j') → Q j' (f j' (proj₂ y j' p')) i → Path S PI PJ j' (proj₂ y j' p') i)
               (p : Q j (αf j (proj₁ y , (λ j' p' → f j' (proj₂ y j' p')))) i) →
               Path S PI PJ j (sup j y) i
    rfold′′ j y i f r p = path ((id map⊎ (λ jpq →
                                proj₁ jpq ,
                                proj₁ (proj₂ jpq) ,
                                r (proj₁ jpq) (proj₁ (proj₂ jpq)) (proj₂ (proj₂ jpq)) ))
                     (αr (proj₁ y , (λ j' p' → f j' (proj₂ y j' p'))) i p))
    elide : {A : Set} → A → A ; elide = id
    celide : {A : Set} → A → A ; celide = id
\end{code}

%endif

%format (elide (x)) = "\dots"
%format (celide (x)) = cong "\dots"

\restorecolumns

\begin{code}

    rfoldUniq :  (j : J) (s : WI S PJ j) (i : I)
                 (p : Q j (βf j s) i) → 
                 βr s i p ≅ 
                   rfold S PI PJ (T ◁* Q) αf αr s i 
                    (subst (λ s → Q j s i) 
                      (WIfoldUniq αf βf feq j s) p)
    rfoldUniq j (sup ._ y) i p with req j y i p
    rfoldUniq j (sup ._ y) i p | reqjyip with βr (sup j y) i p 
    rfoldUniq j (sup ._ y) i p | reqjyip | path q = begin 
             path q -- |βr (sup j y) i p|
            ≅⟨ cong path reqjyip ⟩ 
             path ((id map⊎ (λ jpq →  (  proj₁ jpq , proj₁ (proj₂ jpq) 
                                      ,  βr (proj₂ y (proj₁ jpq) (proj₁ (proj₂ jpq))) i
                                          (proj₂ (proj₂ jpq)))))
                   (αr (proj₁ y , (λ j' p' → βf j' (proj₂ y j' p'))) i
                    (subst (λ s' → Q j s' i) (feq j y) p)))



            ≅⟨ (celide(cong₃ (rfold′′ j y i) (λ≡ j′ →≡ λ≡ s′ →≡ WIfoldUniq αf βf feq j′ s′))) (λ≅ j′ →≅ λ≅ p′ →≅ λ≅ q′ →≅ begin
                  βr (proj₂ y _ _) _ _ 
                 ≅⟨ rfoldUniq _ (proj₂ y _ _) i _ ⟩ 
                  rfold S PI PJ (T ◁* Q) αf αr (proj₂ y _ _) i 
                   (subst (λ s → Q _ s i) 
                    (WIfoldUniq αf βf feq _ (proj₂ y _ _)) _) 
                 ≅⟨ (elide(cong₃ (λ j p → rfold S PI PJ (T ◁* Q) αf αr {j} (proj₂ y j p) i) j′ p′ (trans (subst-removable (λ s → Q _ s i) (WIfoldUniq αf βf feq _ (proj₂ y _ _)) _) q′))) ⟩ 
                  rfold S PI PJ (T ◁* Q) αf αr (proj₂ y _ _) i _ ∎) (elide(trans (subst-removable (λ s → Q j s i) (feq j y) p) (sym (subst-removable (λ s → Q j s i) (WIfoldUniq αf βf feq _ (sup _ y)) p)))) ⟩ 
             path ((id map⊎ (λ jpq →  (  proj₁ jpq , proj₁ (proj₂ jpq) 
                                      ,  rfold S PI PJ (T ◁* Q) αf αr
                                          (proj₂ y (proj₁ jpq) (proj₁ (proj₂ jpq))) i  
                                          (proj₂ (proj₂ jpq)))))
                    (αr (proj₁ y , (λ j p → WIfold αf j (proj₂ y j p))) i
                     (subst (λ s → Q j s i)
                      (WIfoldUniq αf βf feq _ (sup _ y)) p)))      
            ≅⟨ refl ⟩
             rfold S PI PJ (T ◁* Q) αf αr (sup _ y) i 
                (subst (λ s → Q _ s i) 
                 (WIfoldUniq αf βf feq _ (sup _ y)) p) ∎


\end{code}




