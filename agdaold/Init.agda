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
open BasicContainers
open FixedPoints


data _-alg {I O : Set} (F : Cont (I + O) O) : Set where
  alg : (obj  : Cont I O) -> F [ obj ] ⇒C obj -> _-alg {I} {O} F 

algobj : {I O : Set} {F : Cont (I + O) O} -> F -alg -> Cont I O
algobj (alg A _) = A

algin : {I O : Set} {F : Cont (I + O) O} -> (α : F -alg) ->  
          F [ algobj α  ] ⇒C algobj α
algin (alg _ m) = m

μCalg : {I O : Set} (F : Cont (I + O) O) -> F -alg
μCalg F = alg (μC F) inC

foldTy : {I O : Set} {F : Cont (I + O) O} -> F -alg -> Set
foldTy {F = F} μF = (α : F -alg) -> algobj μF ⇒C algobj α  

initalg□ : {I O : Set} (F : Cont (I + O) O) (initalg : F -alg)
           -> foldTy initalg -> Set
initalg□ {I} {O} F a f = {Xs : I -> Set} {o : O} (α : F -alg)
                         (v : ⟦ F [ algobj a ] ⟧ Xs o) ->
                         ⟦ algobj α ⟧₌ 
                           (⟦ f α ⟧N (⟦ algin a ⟧N v)) 
                           (⟦ algin α ⟧N (substisor F (algobj α) 
                                          (⟦ F ⟧m (\{i} -> +elim 
                                            (\i -> [ Xs , ⟦ algobj a ⟧ Xs ] i
                                              -> [ Xs , ⟦ algobj α ⟧ Xs ] i)
                                            (\i x -> x) 
                                            (\i -> ⟦ f α ⟧N) i)
                                         (substisol F (algobj a) v))))

fold□ : forall {I O} (F : Cont (I + O) O) 
                     -> initalg□ F (μCalg F) (\α -> foldC ( algin α)) 
fold□ {I} {O} (S ◁ Ps) {o = o} (alg (T ◁ Qs) (f ◁ r)) ((s , g) ◁ h) = 
 ≅-refl ◁₌ \{_} q -> help (r q) 
  where help : {i : I} 
         (rq : Ps o (inl i) s +
               Σ O
               (\j ->
                 Σ (Ps o (inr j) s)
                 (\p ->
                 Qs j i
                 (wirec (\o' _ -> T o') (\{o'} s' f' g' -> f (s' , \{_} -> g'))
                 (g p)))))
         ->
         h
         ([ inl ,
          (\x ->
             inr
             (map-Σ₂
              (\{x} ->
                 map-Σ₂
                 (\{x'} ->
                    wirec (\o' w ->
                       Qs o' i
                       (wirec (\o0 _ -> T o0) (\{o} s' f' g' -> f (s' , \{_} -> g'))
                       w) ->
                       Path (\o0 i' -> Ps o0 (inl i')) o' i w)
                    (\{o} s' f' g' q' ->
                       [ inl ,
                       (\x' -> inr (map-Σ₂ (\{x0} -> map-Σ₂ (\{x1} -> g' x1)) x')) ]
                       (r q'))
                    (g x')))
              x))
          ]
          rq)
         ≅
         [ (\p' -> h (inl p')) ,
         (\t ->
            h
            (inr
             (π₀ t ,
              π₀ (π₁ t) ,
              wirec (\o' w ->
                      Qs o' i
                      (wirec (\o0 _ -> T o0) (\{o} s' f' g' -> f (s' , \{_} -> g'))
                      w) ->
                      Path (\o0 i' -> Ps o0 (inl i')) o' i w)
                   (\{o} s' f' g' q' ->
                 [ inl ,
                 (\x -> inr (map-Σ₂ (\{x} -> map-Σ₂ (\{x'} -> g' x')) x)) ]
                 (r q'))
              (g (π₀ (π₁ t))) (π₁ (π₁ t)))))
         ]
         rq
        help (inl y) = ≅-refl 
        help (inr (x , x' , y)) = ≅-refl   

initalguniq : {I O : Set} (F : Cont (I + O) O) (initalg : F -alg) 
                          -> (m : foldTy initalg) -> initalg□ F initalg m -> Set
initalguniq {I} {O} F μF fold square = 
  (n : foldTy μF) -> (νF : initalg□ F μF n) -> (α : F -alg) -> 
    {Xs : I -> Set} -> {o : O} (v : ⟦ algobj μF ⟧ Xs o) -> 
      ⟦ algobj α ⟧₌ (⟦ fold α ⟧N v) (⟦ n α ⟧N v) 

folduniq : {I O : Set} (F : Cont (I + O) O) -> 
                       initalguniq F (μCalg F) (\α -> foldC (algin α)) (fold□ F)
folduniq {I} {O} (S ◁ Ps) fold' fold'□ (alg (T ◁ Qs) (αf ◁ αr)) {Xs} {o} (sup s f ◁ g) = {! !}