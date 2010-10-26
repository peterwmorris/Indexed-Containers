{-# OPTIONS --type-in-type 
  #-}


module W where

open import Data.Product
open import Data.Unit
open import Data.Empty
-- open import Data.Sum -- Not using coz the names are awful
open import Data.Bool 
open import Relation.Binary.HeterogeneousEquality

open import ICont
open Utils



data W (S : Set) (P : S -> Set) : Set where
  sup : (s : S) -> (P s -> W S P) -> W S P

wrec : {S : Set} {P : S -> Set} (C : W S P -> Set) 
  (h : (s : S) (f : P s -> W S P) (g : (p : P s) -> C (f p)) -> C (sup s f)) ->
    (w : W S P) -> C w
wrec C h (sup s f) = h s f (\p -> wrec C h (f p))



WI' : {O : Set} (S : O -> Set) (P : (o : O) -> O -> S o -> Set) -> Set
WI' {O} S P = W (Σ O S) (\s -> Σ O (\o -> P (π₀ s) o (π₁ s)))

OK : {O : Set} (S : O -> Set) (P : (o : O) -> O -> S o -> Set) ->
       WI' {O} S P -> O -> Set
OK {O} S P w o = wrec (\_ -> O -> Set) H w o
  where H : (s : Σ O S) -> (Σ O (\o -> P (π₀ s) o (π₁ s)) -> WI' {O} S P) ->
                ((Σ O (\o -> P (π₀ s) o (π₁ s))) -> O -> Set) -> O -> Set
        H os f g o = Σ (o ≅ π₀ os) (\_ -> 
                       (o' : O) -> (p : P (π₀ os) o' (π₁ os)) -> g (o' , p) o')
 
WI : {O : Set} (S : O -> Set) (P : (o : O) -> O -> S o -> Set) -> O -> Set
WI {O} S P o = Σ (WI' {O} S P) (\w -> OK {O} S P w o)


supi : forall {O S P} -> {o : O} -> (s : S o) -> 
         ((o' : O) -> P o o' s -> WI {O} S P o') -> WI {O} S P o  
supi {o = o} s f = (w , ok)
  where w = sup (o , s) (\t -> π₀ (f (π₀ t) (π₁ t)))
        ok = (≅-refl , \o' p -> π₁ (f o' p))   

wreci : forall {O S P} -> (C : (o : O) -> WI {O} S P o -> Set)   
  (h : (o : O)(s : S o)(f : (o' : O) -> P o o' s -> WI {O} S P o') ->
        (g : (o' : O) (p : P o o' s) -> C o' (f o' p)) -> 
         C o (supi {O} {S} {P} s f)) ->
    (o : O) -> (w : WI {O} S P o) -> C o w
wreci {O} {S} {P} C h o (w , ok) = 
  wrec (\w -> (o : O) (ok : OK S P w o) -> C o (w , ok)) l w o ok 
    where l : (s : Σ O S)
              (f : Σ O (\o' -> P (π₀ s) o' (π₁ s)) -> WI' {O} S P)
              (g : (p : Σ O (\o' -> P (π₀ s) o' (π₁ s))) (o' : O)
                   (ok' : OK S P (f p) o') -> C o' (f p , ok'))
              (o' : O) 
              (ok' : OK S P (sup s f) o') ->
              C o' (sup s f , ok')
          l (o , s) f g .o (≅-refl , okf) = 
             (h o s (\o' p -> (f (o' , p) ,   okf o' p)) 
                    (\o' p ->  g (o' , p) o' (okf o' p)))      

