{-# OPTIONS --type-in-type --no-termination-check
  #-}

module Cont where

data _≡_ {A : Set} (a : A) : {B : Set} -> B -> Set where
  refl : a ≡ a

postulate ≡ext : {A : Set} {B : A -> Set} {f g : (a : A) -> B a} ->
                 ((a : A) -> f a ≡ g a) -> f ≡ g  

postulate ≡ext2 : {A : Set} {B : A -> Set} {C : (a : A) -> B a -> Set} ->
                  {f g : (a : A) -> (b : B a) -> C a b} ->
                  ((a : A) -> (b : B a) -> f a b ≡ g a b) -> f ≡ g  

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B 

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> (b : B a) -> Σ A B

Σ≡ : {A : Set} {B : A -> Set} -> 
     {a a' : A} -> (p : a ≡ a') -> {b : B a} -> {b' : B a'} -> (b ≡ b') ->
     _≡_ {Σ A B} (a , b) {Σ A B} (a' , b')
Σ≡ refl refl = refl

data Cont1 : Set where
  _◁_ : (S : Set) -> (P : S -> Set) -> Cont1

data Cont2 : Set where
  _◁_,_ : (S : Set) -> (P : S -> Set) -> (Q : S -> Set) -> Cont2


data _⇒_ : (C D : Cont1) -> Set where
  _◁_ : forall {S T P Q} -> 
        (f : S -> T) -> (r : (s : S) -> Q (f s) -> P s) -> (S ◁ P) ⇒ (T ◁ Q) 

_o_ : {C D E : Cont1} -> (f : D ⇒ E) -> (g : C ⇒ D) -> C ⇒ E
_o_ {_ ◁ _} {_ ◁ _} {_ ◁ _} (a ◁ c) (b ◁ d) = 
   (\s -> a (b s)) ◁ \s r -> d s (c (b s) r) 

⟦_⟧ : Cont1 -> Set -> Set
⟦ S ◁ P ⟧ T = Σ S (\s -> P s -> T) 

_$_ : {C D : Cont1} -> (m : C ⇒ D) -> {T : Set} -> ⟦ C ⟧ T -> ⟦ D ⟧ T
_$_ {S ◁ P} {T ◁ Q} (shf ◁ pof) (s , f) = shf s , \q -> f (pof s q)  

U : Cont2 -> Set -> Set
U (S ◁ P₀ , P₁) T = ⟦ S ◁ P₁ ⟧ T 

-- U C is a functor, obviously

mapU : (C : Cont2) -> {T T' : Set} -> (f : T -> T') -> U C T -> U C T'
mapU (S ◁ P₀ , P₁) f (s , g) = s , \p -> f (g p)      

R : (C : Cont2) -> {T : Set} -> (Q : T -> Set) -> U C T -> Set
R (S ◁ P₀ , P₁) Q (s , f) = P₀ s + Σ (P₁ s) (\p -> Q (f p)) 

-- R C is an indexed functor, it's action on morphisms is given by

mapR : (C : Cont2) -> {T : Set} -> {Q Q' : T -> Set}
       (f : (t : T) -> Q t -> Q' t) -> (u : U C T) -> R C Q u -> R C Q' u
mapR (S ◁ P₀ , P₁) f (s , g) (inl p) = inl p 
mapR (S ◁ P₀ , P₁) f (s , g) (inr (p , q)) = inr (p , f (g p) q) 

-- Prove the laws?

-- We notice this relationship between U and R, as yet we don't understand it

φ : (C : Cont2) {T T' : Set} (f : T -> T') (Q' : T' -> Set) (u : U C T) ->
      R C Q' (mapU C f u) -> R C (\t -> Q' (f t)) u
φ (S ◁ P₀ , P₁) f Q' (a , b) x = x   

-- and since this is the identity function dressed in the emperors new clothes, 
-- we have that this is actually an iso.

-- Partial application of Cont2:

_[_] : (C : Cont2) -> (D : Cont1) -> Cont1
C [ T ◁ Q ] = U C T ◁ R C Q

-- C [ - ] is a functor in Cont1

map[] : (C : Cont2) -> {D D' : Cont1} -> D ⇒ D' -> C [ D ] ⇒ C [ D' ]
map[] C {T ◁ Q} {T' ◁ Q'} (f ◁ r) = 
  mapU C f ◁ \u x -> mapR C r u (φ C f Q' u x)    

data W (C : Cont2) : Set where
  sup : U C (W C) -> W C

sup⁻¹ : {C : Cont2} -> W C -> U C (W C)
sup⁻¹ (sup u) = u

foldW : (C : Cont2) (D : Set) -> (U C D -> D) -> W C -> D
foldW (S ◁ P , Q) D m (sup (s , f)) = 
  m (mapU (S ◁ P , Q) (foldW (S ◁ P , Q) D m) (s , f)) 
  -- The fold square holds by definition :) If this is structural.

R* : (C : Cont2) -> W C -> Set
R* C (sup u) = R C (R* C) u -- show that this is structural :)

μ : (F : Cont2) -> Cont1
μ F = W F ◁ R* F    

inμ : (F : Cont2) -> F [ μ F ] ⇒ μ F
inμ (S ◁ P₀ , P₁) = sup ◁ \_ r -> r

foldμ : (F : Cont2) -> (H : Cont1) -> (F [ H ] ⇒ H) -> μ F ⇒ H
foldμ (S ◁ P₀ , P₁) (T ◁ Q) (a ◁ b) = foldW (S ◁ P₀ , P₁) T a ◁ d       
  where d : (w : W (S ◁ P₀ , P₁)) -> Q (foldW (S ◁ P₀ , P₁) T a w) -> 
            R* (S ◁ P₀ , P₁) w
        d (sup (s , f)) q = mapR (S ◁ P₀ , P₁) d (s , f) (b _ q) 

foldμsq : (F : Cont2) (H : Cont1) (m : F [ H ] ⇒ H) -> {X : Set}
          (x : ⟦ F [ μ F ] ⟧ X) ->
              ((m o (map[] F (foldμ F H m))) $ x) 
            ≡ (((foldμ F H m) o (inμ F)) $ x)
foldμsq (S ◁ P₀ , P₁) (T ◁ Q) (a ◁ b) ((s , f) , g) = 
   Σ≡ refl (≡ext (\a -> refl))   