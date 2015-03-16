
%if style==code

\begin{code}

{-# OPTIONS --universe-polymorphism --no-termination-check #-}

module termcoalg where

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

\section{Terminal Coalgebras of Indexed Containers}
\label{sec:termcoalg}

Dually to the initial algebra construction outlined above, we can also show
that indexed containers are closed under parameterised terminal coalgebras.
We proceed in much the same way as before, by first constructing the dual of
the indexed |W|-type, which we refer to as an indexed |M|-type. As you might
expect this is in fact the plain (as opposed to parametrized) terminal
coalgebra of an indexed container:

%format ∞ = "\infty"
%format ♯ = "\sharp"
%format ♭ = "\flat"
%format ν = "\nu"
%format ν^C = ν ^C
%format out^C = out ^C

\begin{code}

data MI  {I : Set} (S : I → Set) 
         (PI : (i : I) → S i → I → Set) : I → Set where
  sup : obj* ⟦ S ◁* PI ⟧* (λ i → ∞ (MI S PI i))  -**-> MI S PI 

sup⁻¹ : ∀  {I S} {PI : (i : I) → S i → I → Set} →
           MI S PI -**-> obj* ⟦ S ◁* PI ⟧* (MI S PI)
sup⁻¹ (sup (s , f)) = s , λ i p → ♭ (f i p)

\end{code}

%format supm = sup

%if style == newcode

\begin{code}

supm :  {I : Set} {S : I → Set} 
        {PI : (i : I) → S i → I → Set} →
        obj* ⟦ S ◁* PI ⟧* (λ i → ∞ (MI S PI i))  -**-> MI S PI
supm = sup

unsup : {I : Set} {S : I → Set} {PI : (i : I) → S i → I → Set} → 
          {P : (i : I) → MI S PI i → Set} → ({i : I} (sf : Σ* s ∶ S i *Σ ((i′ : I) → PI i s i′ → ∞ (MI S PI i′))) → P i (sup sf)) → {i : I} → (x : MI S PI i) → P i x
unsup f (sup x) = f x

sup' : ∀ {I S PI} → obj* ⟦ S ◁* PI ⟧* (MI {I} S PI)  -**-> MI S PI 
sup' (s , f) = sup (s , (λ i x → ♯ (f i x)))

\end{code}

%endif

\noindent
Here, we employ Agda's approach to coprogramming (e.g. see
\cite{txa:mpc2010g}), where we mark (possibly) infinite subtrees with
|∞|. The type |∞ A| is a suspended computation of type |A|, and |♯ : A → ∞ A| delays
a value of type |A| and |♭ : ∞ A → A| forces a computation. A simple syntactic 
test then ensures that co-recursive programs 
are total --- recursive calls must be immediately {\em guarded} by a |♯| 
constructor. 
% \footnote{Agda's approach to coinduction has some issues when using nested inductive-coinductive definition which we avoid here, e.g. see \cite{altenkirch2010termination}}.
% This technology is 
% at an experimental stage.
 
The equality between infinite objects will be bi-simulation, for instance |MI|.
Types are bi-similar if they have the same node shape, and all their sub-trees 
are bi-similar:

%format _≈MI_ = _ "\approx^{" MI "}" _
%format ≈MI = "\mathbin{\approx^{" MI "}}" 

\begin{code}

data _≈MI_ {J S PJ} {j : J} : (x y : MI S PJ j) → Set where
  sup : ∀ {s f g} → (∀  {j′} (p : PJ j s j′) → 
                        ∞  (♭ (f j′ p)  ≈MI  ♭ (g j′ p))) → 
                           sup (s , f)  ≈MI  sup (s , g)

\end{code}

It is simple to show that this bi-simulation is an equivalence relation. 

%if style==code

\begin{code}

≈MIrefl : ∀ {J S PJ} {j : J} {x : MI S PJ j} → x ≈MI x
≈MIrefl {x = sup (s , f)} = sup (λ p → ♯ ≈MIrefl)

≈MIsym : ∀ {J S PJ} {j : J} {x y : MI S PJ j} → x ≈MI y → y ≈MI x
≈MIsym (sup pr) = sup (λ p → ♯ (≈MIsym (♭ (pr p))))

≈MItrans : ∀ {J S PJ} {j : J} {x y z : MI S PJ j} → 
             x ≈MI y → y ≈MI z → x ≈MI z
≈MItrans (sup pr) (sup qr) = sup (λ p → ♯ (≈MItrans (♭ (pr p)) (♭ (qr p)))) 

\end{code}

%endif

\begin{proposition} 
|(MI S PJ , sup⁻¹)| is the terminal object in the category of 
|⟦ S ◁* PJ ⟧|-coalgebras.
\end{proposition}

We must construct a co-iteration operator |MIunfold|, a morphism in the category 
of |⟦ S ◁* PJ ⟧|-coalgebras to our candidate terminal coalgebra from any other 
coalgebra such that the following diagram commutes:

\[
\xymatrix{
\mbox{|X|}
\ar[rr]^{\mbox{|α|\quad\quad}}
\ar[d]_{\mbox{|MIunfold α|}} & \quad\;\; &
\mbox{|obj* ⟦ S ◁* PJ ⟧* X|}
\ar[d]^{\mbox{|mor*  ⟦ S ◁* PJ ⟧* (MIunfold α)|}}
\\
\mbox{|MI S PJ|}
\ar@@<1ex>[rr]^{\mbox{|sup⁻¹|\quad\;\;}}
& &
\mbox{|obj* ⟦ S ◁* PJ ⟧* (MI S PJ)|} 
\ar@@<1ex>[ll]^{\mbox{|sup|\phantom{|⁻¹|}\quad\;\;}}
}
\]

\noindent
The following definition of |MIunfold|  makes the diagram commute
up-to bisimulation.

\begin{code}

MIunfold :  ∀  {J S PJ} {X : J → Set} →
             X -*-> obj* ⟦ S ◁* PJ ⟧* X → X -*-> MI S PJ 
MIunfold α j x with α j x
MIunfold α j x | s , f = sup (s , λ j′ p → ♯ MIunfold α j′ (f j′ p))

\end{code}

We also require that |MIunfold| is unique, {\em i.e.} any morphism
that makes the diagram above commute should be provably equal (again upto bi-simulation) to |MIunfold α|. To state this property we need to lift the bi-simulation |_≈MI_| through the extension of an indexed container, to say what is it for two elements in the extension to be bi-similar:

%format _⟦⟧MI=_ = _ "\approx^{" ⟦ _ ⟧ MI  "}" _
%format ⟦⟧MI= = "\mathbin{\approx^{" ⟦ _ ⟧ MI "}}" 



\begin{code}

_⟦⟧MI=_ : ∀  {J : Set} {S : J → Set} 
             {PJ : (j : J) → S j → J → Set} {j : J} → 
             (x y : obj* ⟦ S ◁* PJ ⟧* (MI S PJ) j) → Set
_⟦⟧MI=_ {J} {S} {PJ} {j} (s , f) (s′ , f′) = 
  Σ (s ≡ s′) λ eq →  {j′ : J} (p : PJ j s j′) → 
                     f _ p ≈MI f′ _ (subst (λ s → PJ j s j′) eq p)

\end{code}

\noindent
The uniqueness property is then given by:

%format sup' = sup

%if style == code

\begin{code}

{-

\end{code}

%endif

\begin{code}

MIunfoldUniq : ∀ {J} {X : J → Set} {S PJ} 
                 (α : X -*-> obj* ⟦ S ◁* PJ ⟧* X) → (β : X -*-> MI {J} S PJ) →
                 (  (j : J) (x : X j) → 
                    (sup⁻¹ (β j x)) ⟦⟧MI= ((mor* ⟦ S ◁* PJ ⟧* β ⊚ α) j x)) → 
                 (j : J) (x : X j) → β j x ≈MI MIunfold α j x 

MIunfoldUniq α β commβ i x with commβ i x
MIunfoldUniq α β commβ i x | commix with β i x
MIunfoldUniq α β commβ i x | (refl , y) | sup (.(proj₁ (α i x)) , g) = 
  sup (λ p → ♯ ≈MItrans (y p) (MIunfoldUniq α β commβ _ _))



\end{code}

However, Agda rejects this definition due to the recursive call not
being guarded immediately by the |♯|, however, it is productive due to
the fact that the proof of transitivity of bisimulation is
contractive.  We can persuade the system this is productive by fusing
the definition of |≈MItrans| with this |MIunfoldUniq| in a cumbersome
but straightforward way.
%, for details see the source of this paper.

%if style == code

\begin{code}

-}

MIunfoldDiag : ∀  {J} {X : J → Set} S PJ 
                  (α : X -*->  obj* ⟦ S ◁* PJ ⟧* X) 
                  (β : X -*->  MI {J} S PJ) → Set
MIunfoldDiag {J} {X} S PJ α β = 
  (j : J) (x : X j) → _⟦⟧MI=_ {J} {S} {PJ} {j} (sup⁻¹ (β j x)) ((mor* ⟦ S ◁* PJ ⟧* β ⊚ α) j x)


MIunfoldUniq' : ∀ {I} {X : I → Set} {S PI} 
                  (α : X -*-> obj* ⟦ S ◁* PI ⟧* X) → (β : X -*-> MI {I} S PI) →
                  MIunfoldDiag S PI α β → (i : I) → {t : MI S PI i} → (x : X i) →
                  t ≈MI (β i x) → t ≈MI (MIunfold α i x)
MIunfoldUniq' α β comm i x bb with comm i x
MIunfoldUniq' α β comm i x bb | commix with β i x 
MIunfoldUniq' α β comm i x (sup bb) | refl , y | sup (.(proj₁ (α i x)) , g) = 
  sup (λ p → ♯ (MIunfoldUniq' α β comm _ (proj₂ (α i x) _ _) (≈MItrans (♭ (bb p)) (y p))))

MIunfoldUniq : ∀ {I} {X : I → Set} {S PI} 
                 (α : X -*-> obj* ⟦ S ◁* PI ⟧* X) → (β : X -*-> MI {I} S PI) →
                 MIunfoldDiag S PI α β → (i : I) → (x : X i) →
                 (β i x) ≈MI (MIunfold α i x)
MIunfoldUniq α β comm i x = MIunfoldUniq' α β comm i x ≈MIrefl

\end{code}

%endif


\noindent
The paths to positions in an indexed |M|-tree are always 
finite -- in fact modulo the use of |♭|, this |Path| is the same as the 
definition for the initial algebra case.

\begin{code}

data Path  {I J : Set} (S : J → Set)  
           (PI  : (j : J) → S j → I  → Set) 
           (PJ  : (j : J) → S j → J  → Set) 
           : (j : J) → MI S PJ j → I → Set where
  path : ∀  {j s f i} →     
               PI j s i 
            ⊎  (  Σ* j′ ∶ J *Σ 
                  (Σ* p ∶ PJ j s j′ *Σ Path S PI PJ j′ (♭ (f j′ p)) i)) 
            → Path S PI PJ j (sup (s , f)) i 

\end{code}

Just as parameterised initial algebras of indexed containers are
built from |WI|-types, so parameterised terminal coalgebras of indexed
containers are built from |MI|-types as follows.

\begin{code}

ν^C : {I J : Set} → ICont* (I ⊎ J) J → ICont* I J
ν^C {I} {J} (S ◁* P) = 
  let  PI  : (j : J) → S j → I  → Set ;  PI  j s i   = P $$ j $$ s $$ (inj₁ i) 
       PJ  : (j : J) → S j → J  → Set ;  PJ  j s j′  = P $$ j $$ s $$ (inj₂ j′)
  in   MI S PJ ◁* Path S PI PJ

\end{code}

\begin{code}

out^C : ∀ {I J} → (F : ICont* (I ⊎ J) J) → ν^C F ⇒* F ⟨ ν^C F ⟩C* 
out^C {I} {J} (S ◁* P) = (λ _ → sup⁻¹) ◁* outr
  where  outr :  {j : J} (s : (ν^C (S ◁* P) projS*) $$ j) →
                 ((((S ◁* P) ⟨ ν^C (S ◁* P) ⟩C*) projP*) $$ j $$ (sup⁻¹ s)) -*->
                 ((ν^C (S ◁* P)) projP* $$ j $$ s)
         outr (sup s) i′ p = path p 

\end{code}

%if style == newcode

\begin{code}


path⁻¹ : ∀  {I J S PI PJ j s f i} → Path S PI PJ j (sup (s , f)) i →
              PI j s i 
           ⊎  (Σ* j′ ∶ J *Σ (Σ* p ∶ PJ j s j′ *Σ Path {I} {J} S PI PJ j′ (♭ (f j′ p)) i)) 
path⁻¹ (path (inj₁ x)) = inj₁ x
path⁻¹ (path (inj₂ y)) = inj₂ y 



in^C' :  ∀ {I J} → (F : ICont* (I ⊎ J) J) → F ⟨ ν^C F ⟩C* ⇒* ν^C F 
in^C' {I} {J} (S ◁* P) = (λ {_ (s , f) → sup (s , λ i x → ♯ (f i x))}) ◁* λ _ _ → path⁻¹ 

\end{code}

%endif

\begin{proposition}
|(ν^C F , out^C F)| is the terminal object in the category of parametrized |F|-coalgebras of indexed containers. By full and faithfulness, |(⟦ ν^C F ⟧* , ⟦ out^C F ⟧⇒*)| will also be terminal in the indexed functor case.
\end{proposition}

\begin{proof}
Mirroring the case of initial algebras, the coiteration for this terminal co-algebra employs the coiteration of |MI| for the shape maps. The position map takes a |Path| and builds a |Q| position by applying the position map from the coalgebra at every step in the path --- note that this position map is {\em inductive} in its path argument.

\begin{code}

unfold^C : ∀  {I J} (F : ICont* (I ⊎ J) J) {G : ICont* I J} → 
              G ⇒* F ⟨ G ⟩C* → G ⇒* ν^C F
unfold^C {I} {J} (S ◁* P) {T ◁* Q} (f ◁* r) = funfold ◁* runfold  
    where  PI  :  (j : J) → S j → I  → Set ;  PI  j s i    = P j s (inj₁ i) 
           PJ  :  (j : J) → S j → J  → Set ;  PJ  j s j′   = P j s (inj₂ j′)
           funfold = MIunfold f
           runfold :  {j : J} (t : T j) 
                      (i : I) → Path S PI PJ j (funfold j t) i → Q j t i 
           runfold t i (path p) = 
             r t i (   [   inj₁
                       ,   (λ y →  inj₂   (  _ , proj₁ (proj₂ y) 
                                          ,  runfold (proj₂ (f _ t) _ _) i (proj₂ (proj₂ y)))) ] p)

\end{code}

We must then show that |unfold^C| is the unique morphism that makes the following diagram commute:

\[
\xymatrix{
\mbox{|G|}
\ar[d]_{\mbox{|F ⟨ (unfold^C F α) ⟩M*|}}\ar[rr]^{\mbox{|α|\quad}}
& &\mbox{|F ⟨ G ⟩C*|}\ar[d]^{\mbox{|unfold^C F α|}}
\\
\mbox{|ν^C F|} \ar[rr]^{\mbox{|out^C F|\quad}}
& 
\quad&
\mbox{|F ⟨ ν^C F ⟩C*|}  }
\]

\noindent
As with the initial algebra case, this follows immediately from the definition:

\begin{code}

unfoldComm : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
                (α : G ⇒* F ⟨ G ⟩C*) →
                (out^C F comp^C* unfold^C F α) ≡⇒*
                  ((F ⟨ (unfold^C F α) ⟩CM*) comp^C* α)       
unfoldComm (S ◁* P) (f ◁* r) = (λ j s → refl) ◁* (λ j s i p → refl) 

\end{code}

\noindent
We also have to show that the |unfold^C| is {\em unique}; that is, any morphism that makes the 
above diagram commute must be equal to |unfold^C F α|.

 In order to show this in Agda, we are assuming a second extensionality principle
%\footnote{It should be possible to verify this formally but we didn't manage to complete the proof. We have checked it on paper.}
namely that if two |MI| trees are bi-similar, then they are in fact equal:
\begin{code}
postulate MIext : ∀  {J S PJ} {j : J} {x y : MI S PJ j} →
                     x ≈MI y → x ≅ y

\end{code}


\noindent
The inverse of this principle is obviously true:

\begin{code}

MIext⁻¹ : ∀  {J S PJ} {j : J} {x y : MI S PJ j} → 
             x ≅ y → x ≈MI y
MIext⁻¹ refl = ≈MIrefl

\end{code}

\noindent
It is reasonable to assume that any language with fully fledged support for co-inductive types {\em and} extensional equality would admit such an axiom.

We can now state the property that |unfold^C| is, indeed, unique:

\begin{spec}

unfoldUniq : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
                (α : G ⇒* F ⟨ G ⟩C*) (β : G ⇒* ν^C F) → 
                (out^C F comp^C* β)  ≡⇒* (F ⟨ β ⟩CM* comp^C* α) →
                β  ≡⇒* (unfold^C F α)

\end{spec}

\noindent
The proof that the shape maps agree follows from the proof that |MIunfold| is unique, and the proof that the position maps agree follows the same inductive structure as |runfold|. Unfortunately, because Agda lacks full support for both co-induction and extensional equality it is not feasible to complete the proof terms for these propositions in our Agda development. The main obstacle remains mediating between bi-simulation, the (functional) extensional equality and Agda's built-in notion of equality. We have completed this proof on paper, however, and we are hopeful that soon we may be in a position to complete these proof terms in a system where the built-in equality is sensible for both functions and co-inductive types.

%if style == code

\begin{spec}


ext⁻¹₂′ :  ∀ {l l' l''} {A A' : Set l} {B : A → Set l'} {B' : A' → Set l'} {C : A → Set l''} {C' : A' → Set l''} {f : (a : A) → B a → C a} {g : (a : A') → B' a → C' a} → A ≡ A' → B ≅ B' → C ≅ C' → f ≅ g →
                  ((a : A) (a' : A') → a ≅ a' → (b : B a) (b' : B' a') → b ≅ b' → f a b ≅ g a' b') 
ext⁻¹₂′ refl refl refl refl a .a refl  b .b refl = refl

unfoldUniq : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) 
                (α : G ⇒* F ⟨ G ⟩C*) (β : G ⇒* ν^C F) → 
                (out^C F comp^C* β)  ≡⇒* (F ⟨ β ⟩CM* comp^C* α) →
                β  ≡⇒* (unfold^C F α)
unfoldUniq {I} {J} {F} G (αf ◁* αr) (βf ◁* βr) (feq ◁* req) =  (λ j s → MIext (MIunfoldUniq αf βf (λ j′ s′ → cong proj₁ (feq j′ s′) , (λ {j″} p″ → MIext⁻¹ (trans (ext⁻¹₂′ refl (ext (λ a → cong (λ zz → ICont*.P F j′ (proj₁ zz) (inj₂ a)) (feq j′ s′) )) refl (cong proj₂ (feq j′ s′)) j″ j″ refl p″ (subst (λ zz → ICont*.P F j′ (proj₁ zz) (inj₂ j″)) (feq j′ s′) p″) (sym (subst-removable (λ zz → ICont*.P F j′ (proj₁ zz) (inj₂ j″)) (feq j′ s′) p″))) (cong (λ pp → βf j″ (proj₂ (αf j′ s′) j″ pp)) (trans (subst-removable (λ zz → ICont*.P F j′ (proj₁ zz) (inj₂ j″)) (feq j′ s′) p″) (sym (subst-removable (λ s' → ICont*.P F j′ s' (inj₂ j″)) (cong proj₁ (feq j′ s′)) p″)))))
   )) j s)) ◁* {!ext⁻¹!} 

--(λ j s → MIext (MIunfoldUniq αf βf (λ j s → cong proj₁ (feq j s)) , ?)) ◁* {!!}

\end{spec}

%endif

\end{proof}

