
%if style==code

\begin{code}

{-# OPTIONS --universe-polymorphism #-}

module initalgok where

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

open import initalg

\end{code}

%endif

\begin{code}

comp : ∀ {I} {C D E : ICont I} → D ⇒ E → C ⇒ D → C ⇒ E
comp (f ◁ r) (g ◁ q) = (f ∘ g) ◁ (λ s i → q s i ∘ r (g s) i)

comp* :  ∀ {I J} {C D E : ICont* I J} → D ⇒* E → C ⇒* D → C ⇒* E
comp* (f ◁* r) (g ◁* q) = (λ j → f j ∘ g j) ◁* (λ {j} s i → q s i ∘ r (g j s) i)

record _≡⇒_ {I} {C D : ICont I} (m n : C ⇒ D) : Set where
  constructor ⇒eq
  field
    f : (s : ICont.S C) → _⇒_.f m s ≡ _⇒_.f n s
    r : (s : ICont.S C) (i : I) (p : ICont.P D _ _) → _⇒_.r m s i p ≡ _⇒_.r n s i (subst (λ s' → ICont.P D s' i) (f s) p)
    
record _≡⇒*_ {I J} {C D : ICont* I J} (m n : C ⇒* D) : Set where
  field
    f : {j : J} → (s : ICont*.S C j) → _⇒*_.f m j s ≡ _⇒*_.f n j s
    r : {j : J} → (s : ICont*.S C j) (i : I) (p : ICont*.P D j _ _) → _⇒*_.r m s i p ≡ _⇒*_.r n s i (subst (λ s' → ICont*.P D j s' i) (f s) p)

postulate ext' :  ∀ {l l'} {A A' : Set l} {B : A → Set l'} {B' : (a : A') → Set l'}  {f : (a : A) → B a} {g : (a : A') → B' a} → 
                  ((a : A) (a' : A') → a ≅ a' → f a ≅ g a') → f ≅ g

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          {D : ∀ x → (y : B x) → C x y → Set d}
          {x y u v s t}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → s ≅ t → f x u s ≅ f y v t
cong₃ f refl refl refl = refl


≡⇒≡ : ∀ {I} {C D : ICont I} (m n : C ⇒ D) → m ≡⇒ n → m ≡ n
≡⇒≡ {I} {S ◁ P} {T ◁ Q} (f ◁ r) (g ◁ q) eq  =  cong₂ con (ext (_≡⇒_.f eq)) (ext' (λ a a' x → ext' (λ b b' y → ext' (λ c c' z → trans (_≡⇒_.r eq a b c)  (cong₃ q x y (trans (subst-removable (λ s' → ICont.P (T ◁ Q) s' b) (_≡⇒_.f eq a) c ) z))))))
  where con : (f : S → T) (g : (s : S) (i : I) → Q (f s) i → P s i) → (S ◁ P) ⇒ (T ◁ Q) ; con = _◁_



comm : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) (α : F ⟨ G ⟩C* ⇒* G) →
       (comp* (fold^C F α) (in^C F)) ≡⇒* comp* α (F ⟨ (fold^C F α) ⟩CM*)           
comm {I} {J} {S ◁* P} (T ◁* Q) (f ◁* r) = 
  record {  f = λ _ → refl; 
            r = λ {j} s i p → refl }

congpath : {I J : Set} {S : J → Set}  
           {PI  : (j : J) → S j → I  → Set} 
           {PJ  : (j : J) → S j → J  → Set} 
           {j : J} {x : obj*  ⟦ S ◁* PJ ⟧* (WI S PJ) j} {i : I} →
           (p q : Path S PI PJ j (sup _ x) i) → pathminusone p ≡ pathminusone q → p ≡ q
congpath (path .q) (path q) refl = refl

cong⊎map : ∀ {a b c d} {A : Set a} {B B′ : Set b} {C : Set c} {D : Set d}
           {f f′ : A → C} {g : B → D} {g′ : B′ → D} {x : A ⊎ B} {x′ : A ⊎ B′} → f ≡ f′ → (p : B ≡ B′) → g ≅ g′ → x ≅ x′ → Data.Sum.map f g x ≡ Data.Sum.map f′ g′ x′
cong⊎map refl refl refl refl = refl




,,≡ : {A : Set} {B : A → Set} {C : (a : A) → B a → Set} → {t t' : Σ A (λ a → Σ (B a) (C a))} → (proj₁ t ≡ proj₁ t') → (proj₁ (proj₂ t) ≅ proj₁ (proj₂ t')) → (proj₂ (proj₂ t) ≅ proj₂ (proj₂ t')) → t ≡ t' 
,,≡ {t = a , b , c} {t' = ._ , ._ , ._} refl refl refl = refl

,,≡₁ : {A A' : Set} {B : A → Set} {B' : A' → Set} {C : (a : A) → B a → Set} {C' : (a : A') → B' a → Set} → {t : Σ A (λ a → Σ (B a) (C a))} {t' : Σ A' (λ a → Σ (B' a) (C' a))} → A ≡ A' → B ≅ B' → C ≅ C' → t ≅ t' → proj₁ t ≅ proj₁ t'
,,≡₁ refl refl refl refl = refl 

,,≡₂ : {A A' : Set} {B : A → Set} {B' : A' → Set} {C : (a : A) → B a → Set} {C' : (a : A') → B' a → Set} → {t : Σ A (λ a → Σ (B a) (C a))} {t' : Σ A' (λ a → Σ (B' a) (C' a))} → A ≡ A' → B ≅ B' → C ≅ C' → t ≅ t' → proj₁ (proj₂ t) ≅ proj₁ (proj₂ t')
,,≡₂ refl refl refl refl = refl 

,,≡₃ : {A A' : Set} {B : A → Set} {B' : A' → Set} {C : (a : A) → B a → Set} {C' : (a : A') → B' a → Set} → {t : Σ A (λ a → Σ (B a) (C a))} {t' : Σ A' (λ a → Σ (B' a) (C' a))} → A ≡ A' → B ≅ B' → C ≅ C' → t ≅ t' → proj₂ (proj₂ t) ≅ proj₂ (proj₂ t')
,,≡₃ refl refl refl refl = refl 


uniq : ∀  {I J} {F : ICont* (I ⊎ J) J} (G : ICont* I J) (α : F ⟨ G ⟩C* ⇒* G)
          (β : μ^C F ⇒* G) → (comp* β (in^C F)) ≡⇒* comp* α (F ⟨ β ⟩CM*) →
          β ≡⇒* fold^C F α
uniq {I} {J} {SP} (TQ) (fr) (gq) βcomm = 
   record { f = WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) _; r = foo  }
 where foo : {j : J} (s : ICont*.S (μ^C SP) j) (i : I)
              (p : ICont*.P TQ j (_⇒*_.f gq j s) i) →
              _⇒*_.r gq s i p ≡
              _⇒*_.r (fold^C SP fr) s i
               (subst (λ s' → ICont*.P TQ j s' i)
                (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ z → _≡⇒*_.f βcomm) j s) p)
       foo (sup _ x) i p = congpath _ _ (trans (_≡⇒*_.r βcomm x _ _) 
         (cong⊎map refl 
                   (cong (Σ J) (ext (λ j → cong (Σ (ICont*.P SP _ (proj₁ x) (inj₂ j))) (ext (λ p → cong (λ x' → ICont*.P TQ j x' i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ z → _≡⇒*_.f βcomm) j _ ))))))  
                   (ext' (uncurry λ r₀ → uncurry λ r₁ r₂ → uncurry λ r₀' → uncurry λ r₁' r₂'  pp →   ,,≡ (,,≡₁ refl refl (ext λ j → ext λ v → cong (λ xx → ICont*.P TQ j xx i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) j _)) pp) (,,≡₂ refl refl (ext λ j → ext λ v → cong (λ xx → ICont*.P TQ j xx i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) j _)) pp) (trans (foo _ _ _) (cong₃ (λ xx yy zz → Pathfold (ICont*.S SP) (λ j s i' → ICont*.P SP j s (inj₁ i')) (λ j s j′ → ICont*.P SP j s (inj₂ j′)) TQ (_⇒*_.f fr) (_⇒*_.r fr) (proj₂ x xx yy) i zz) ((,,≡₁ refl refl (ext λ j → ext λ v → cong (λ xx → ICont*.P TQ j xx i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) j _)) pp)) (,,≡₂ refl refl (ext λ j → ext λ v → cong (λ xx → ICont*.P TQ j xx i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) j _)) pp) (trans (subst-removable (λ s' → ICont*.P TQ r₀ s' i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ z → _≡⇒*_.f βcomm) r₀ (proj₂ x r₀ r₁)) r₂) (,,≡₃ refl refl (ext λ j → ext λ v → cong (λ xx → ICont*.P TQ j xx i) (WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) j _)) pp)))))) (cong₂ (λ xx yy → _⇒*_.r fr (proj₁ x , xx) i yy) (ext λ i' → ext λ z →  WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ _ → _≡⇒*_.f βcomm) _ _) (trans (subst-removable (λ s' → ICont*.P TQ _ s' i) (_≡⇒*_.f βcomm x) p) (sym (subst-removable (λ s' → ICont*.P TQ _ s' i)(WIfolduniq (_⇒*_.f fr) (_⇒*_.f gq) (λ z → _≡⇒*_.f βcomm) _ (sup _ x)) p)))))) 



\end{code}