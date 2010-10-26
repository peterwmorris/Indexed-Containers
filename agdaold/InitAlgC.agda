{-# OPTIONS --type-in-type 
  #-}
module ICont where

open import Data.Product
open import Data.Unit
open import Data.Empty
-- open import Data.Sum -- Not using coz the names are awful
open import Data.Bool
open import Relation.Binary.HeterogeneousEquality


module Utils where
  {- Fixing some terrible name decisions in the Std. Lib. -}

  data _+_ : Set -> Set -> Set where
    inl : {A B : Set} -> A -> A + B
    inr : {A B : Set} -> B -> A + B

  [_,_] :  {a b c : Set}
           -> (a -> c) -> (b -> c) -> (a + b -> c)
  [ f , g ] (inl x) = f x
  [ f , g ] (inr y) = g y

  +elim : forall {A B} -> (M : (A + B) -> Set) 
           -> (minl : (a : A) -> M (inl a))
           -> (minr : (b : B) -> M (inr b))
           -> (ab : A + B) -> M ab
  +elim M minl minr (inl a) =  minl a
  +elim M minl minr (inr b) =  minr b 

  π₀ : {A : Set} {B : A -> Set} -> Σ A B -> A
  π₀ = proj₁
  π₁ : {A : Set} {B : A -> Set} -> (t : Σ A B) -> B (π₀ t) 
  π₁ = proj₂

  -, : forall {a P Q} -> (forall {x} -> P x -> Q x) -> Σ a P -> Σ a Q
  -, = map-Σ₂

  {- -}

  _∘_ : {a : Set} {b c : a -> Set} ->
       (forall {x} -> b x -> c x) -> ((x : a) -> b x) ->
       ((x : a) -> c x)
  f ∘ g = \x -> f (g x)

module CCC where

  open Utils

  data Cont : Set where
    _◁_ : (S : Set) -> (P : S -> Set) -> Cont

  data _⇒_ : Cont -> Cont -> Set where
    _◁_ : forall {S P T Q} -> (f : S -> T) -> ((s : S) -> Q (f s) -> P s) 
                           -> (S ◁ P) ⇒ (T ◁ Q) 

  ⟦_⟧ : Cont -> Set -> Set
  ⟦ S ◁ P ⟧ X = Σ S (\s -> P s -> X)  

  ⟦_⟧M : {C D : Cont} -> C ⇒ D -> {X : Set} -> ⟦ C ⟧ X -> ⟦ D ⟧ X
  ⟦_⟧M {S ◁ P} {T ◁ Q} (f ◁ r) (s , p) = f s , \q -> p (r s q) 

  data Cont₂ : Set where
    _◁_ : (S : Set) -> (PQ : (S -> Set) × (S -> Set)) -> Cont₂ 

  U : (F : Cont₂) -> Set -> Set
  U (S ◁ (P₀ , P₁)) T = ⟦ S ◁ P₁ ⟧ T   

  R : (F : Cont₂) {T : Set} (Q : T -> Set) -> U F T -> Set
  R (S ◁ (P₀ , P₁)) Q (s , f) = P₀ s + Σ (P₁ s) (\p -> Q (f p)) 

  _[_] : Cont₂ -> Cont -> Cont
  F [ T ◁ Q ] = U F T ◁ R F Q

  UM : (F : Cont₂) {T T' : Set} (f : T -> T') -> U F T -> U F T'
  UM (S ◁ (P₀ , P₁)) f (s , g) = s , \p -> f (g p)

  RM : (F : Cont₂) {T T' : Set} (f : T -> T') {Q : T -> Set} {Q' : T' -> Set}
       -> (r : (t : T) -> Q' (f t) -> Q t)
        -> (u : U F T) -> R F Q' (UM F f u) -> R F Q u   
  RM (S ◁ (P₀ , P₁)) f r (s , l) (inl p) = inl p 
  RM (S ◁ (P₀ , P₁)) f r (s , l) (inr (p , q)) = inr (p , r (l p) q) 

  _[_]M : (F : Cont₂) -> {G G' : Cont} -> (G ⇒ G') -> F [ G ] ⇒ F [ G' ]
  _[_]M (S ◁ (P₀ , P₁)) {T ◁ Q} {T' ◁ Q'} (f ◁ r) = 
    UM (S ◁ (P₀ , P₁)) f ◁ RM (S ◁ (P₀ , P₁)) f r  

  data W (S : Set) (P : S -> Set) : Set where
    sup : Σ S (\s -> P s -> W S P) -> W S P

  UU : Cont₂ -> Set
  UU (S ◁ (P₀ , P₁)) = W S P₁  -- μ ⟦ S ◁ P₁ ⟧

  RR : (F : Cont₂) -> UU F -> Set
  -- RR F (sup sf) = R F (RR F) sf
  RR (S ◁ (P₀ , P₁)) (sup (s , f)) = 
    P₀ s + Σ (P₁ s) (\p -> RR (S ◁ (P₀ , P₁)) (f p)) 

  μ : Cont₂ -> Cont
  μ F = UU F ◁ RR F

  inC : {F : Cont₂} -> F [ μ F ] ⇒ μ F
  inC {S ◁ (P₀ , P₁)} = sup ◁ id
    where id : (sf : Σ S (\s' -> P₁ s' -> W S (\x -> P₁ x))) 
               -> RR (S ◁ (P₀ , P₁)) (sup sf) 
               -> R (S ◁ (P₀ , P₁)) (RR (S ◁ (P₀ , P₁))) sf  
          id (s , f) = \x -> x 

  foldW : {S : Set} -> {P : S -> Set} -> {T : Set} 
          -> (f : (Σ S (\s -> P s -> T)) -> T) -> W S P -> T
  foldW f (sup (s , l)) = f (s , \p -> foldW f (l p)) 

  _-alg : (F : Cont₂) -> Set
  F -alg = Σ Cont (\A -> F [ A ] ⇒ A)  

  foldC : {F : Cont₂} -> (A : Cont) -> (α : F [ A ] ⇒ A) -> μ F ⇒ A  
  foldC {S ◁ (P₀ , P₁)} (T ◁ Q) (f ◁ r) = foldW f ◁  r' 
    where r' : (w : W S P₁) -> Q (foldW f w) -> RR (S ◁ (P₀ , P₁)) w
          r' (sup (s , g)) q = 
            RM (S ◁ (P₀ , P₁)) (foldW f) {_} {Q} r' (s , g) 
               (r (s , \p -> foldW f (g p)) q)
  
