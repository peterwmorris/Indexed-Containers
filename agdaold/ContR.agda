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

  module BasicContainers where

    open Utils

    _*_,_  : (X : Set -> Set) -> (I O : Set) -> Set
    X * I , O = O -> X I 

    FuncO : (I : Set) -> Set
    FuncO I = (I -> Set) -> Set

    FuncO* : (I O : Set) -> Set
    FuncO* I O = O -> FuncO I    

    record Cont (I : Set) : Set 
     where
      field S : Set
      field P : I -> S -> Set

    Cont* : (I O : Set) -> Set
    Cont* I O = O -> Cont I

    _◁_ : {I : Set} -> (S : Set) -> (P : I -> S -> Set) -> Cont I 
    S ◁ P = record { S = S ; P = P }

    _◁*_ : {I O : Set} -> (S : O -> Set) -> (P : (o : O) -> I -> S o -> Set) -> Cont* I O
    (S ◁* P) o = S o ◁ P o 

    record ⟦_⟧ {I : Set} (SP : Cont I) (X : I -> Set) : Set where
      field s : Cont.S SP
      field f : {i : I} -> Cont.P SP i s -> X i



    KC : {I : Set} -> Set -> Cont I
    KC A = record { S = A
                  ; P = \ _ _ -> ⊥ } 

    IdC : {I : Set} -> Cont* I I
    IdC i = record { S = ⊤
                   ; P = \ j _ -> i ≅ j } 

    ΔC : forall {I O O'} -> (f : O' -> O) -> Cont* I O -> Cont* I O'
    ΔC f SPs = \ o -> SPs (f o)

    ΣFo :  {I O O' : Set} -> (O -> O')  -> (FuncO* I O) 
                                        -> (FuncO* I O')
    ΣFo {O = O} f F o' Xs = 
      Σ O (\o -> (o' ≅ (f o)) × (F o Xs))

    ΠFo :  {I O O' : Set} -> (O -> O')  -> (FuncO* I O) 
                                        -> (FuncO* I O')
    ΠFo {O = O} f F o' Xs = 
        (o : O) -> (o' ≅ (f o)) -> (F o Xs)

    Csnd :  forall { I J } -> Cont (I + J) -> Cont J
    Csnd SP = record { S = Cont.S SP 
                      ; P =  (\ j -> Cont.P SP (inr j)) }

    U : forall { I J } -> Cont (I + J) -> (J -> Set) -> Set
    U  SP Ts =  ⟦ Csnd SP ⟧ Ts

    R : forall { I J } -> (SP : Cont (I + J)) 
                       -> {Ts : J -> Set} 
                       -> (Qs : {j : J} -> I -> (Ts j) -> Set)
                       -> I -> U SP Ts -> Set
    R {I} {J} SP Qs i sf =
               Cont.P SP (inl i) (⟦_⟧.s sf)
               + Σ J (\ j -> Σ (Cont.P SP (inr j) (⟦_⟧.s sf)) 
                             (\ p -> Qs i (⟦_⟧.f sf p)))  

    _[_]C : forall { I J } -> Cont (I + J) -> Cont* I J -> Cont I 
    _[_]C SP TQs = record { S = U SP (\ j -> Cont.S (TQs j))
                          ; P = R SP (\ {j} -> Cont.P (TQs j)) }

    _[_]C* : forall { I J K } -> Cont* (I + J) K 
                              -> Cont* I J -> Cont* I K
    SPs [ TQs ]C* = \ k -> (SPs k) [ TQs ]C 

    data WI {I : Set} (S : I -> Set) 
                      (Ps : {i : I} -> I -> S i -> Set) : 
              I -> Set where 
      sup : {i : I} -> (s : S i) 
                     -> (f : {i' : I} -> Ps i' s -> WI S Ps i') 
                     -> WI S Ps i  

    wirec : forall {O S} {P : {o : O} -> O -> S o -> Set}
      -> (C : (o : O) -> WI S P o -> Set)   
      (h :  {o : O} -> (s : S o) 
            -> (f : {o' : O} -> P o' s -> WI S P o')
            -> (g : {o' : O} -> (p : P o' s) -> C o' (f p)) 
            -> C o (sup s f))
      -> {o : O} -> (w : WI S P o) -> C o w
    wirec C h (sup s f) = h s f (\p -> wirec C h (f p))

    μS : forall {I O} -> Cont* (I + O) O -> O -> Set
    μS SPs = WI (\ o -> Cont.S (SPs o)) 
                (\ {o} o' s -> Cont.P (SPs o) (inr o') s)

    Path : forall {I O S} ->
           {Ps : {o : O} -> O -> S o -> Set} -> 
           (Qs : {o : O} -> I -> S o -> Set) 
           {o : O} -> I -> (WI S Ps o) -> Set
    Path {O = O} {Ps = Ps} Qs i (sup s f) = 
           Qs i s + Σ O (\ o' -> Σ (Ps o' s) (\ p -> Path Qs i (f p)) )   

    μC : forall {I O} -> Cont* (I + O) O -> Cont* I O 
    μC SPs o = record { S = μS SPs o
                      ; P = Path (\{o'} i s -> Cont.P (SPs o') (inl i) s) }

    record _⇒C_  {I : Set} 
                 (SP TQ : Cont I) : Set where
      field f : Cont.S SP -> Cont.S TQ
      field r :  {i : I} {s : Cont.S SP} 
                 -> Cont.P TQ i (f s) -> Cont.P SP i s

    _⇒C*_ : {I O : Set} -> (SP TQ : Cont* I O) -> Set
    _⇒C*_ {I} {O} SP TQ = (o : O) -> (SP o) ⇒C (TQ o)

    inC : forall {I O} (SPs : Cont* (I + O) O) -> 
            (SPs [ μC SPs ]C*) ⇒C* (μC SPs)
    inC SPs o = record { f =  \ t -> sup (⟦_⟧.s t) (⟦_⟧.f t) 
                       ; r = \ p -> p } 

    
{-

    foldW : forall {O S} {Ps : {o : O} -> O -> S o -> Set} 
                   {T : O -> Set} ->
             ({o : O} -> SemC 
                      Σ (S o) 
                        (\s -> {o' : O} -> Ps o' s -> T o') -> T o)
               -> {o : O} -> WI S (\o' -> Ps o') o -> T o
    foldW {T = T} α w = 
      wirec (\o _ -> T o) (\s f g -> α (s , \{_} -> g)) w    

-}


    foldC : forall {I O} (SPs : Cont* (I + O) O) {TQs : Cont* I O} 
              (α : (SPs [ TQs ]C*) ⇒C* TQs) 
             -> (μC SPs) ⇒C* TQs
    foldC {I} {O} SPs {TQs} α o = 
             record { f = f
                    ; r =  \ {i} {w} ->  wirec (\ o w -> Cont.P (TQs o) i (f {o} w) 
                                                      -> Path  (\{o'} i' s -> Cont.P (SPs o') (inl i') s) i w) 
                                               (\ {o} _ _ g q -> [ inl , inr ∘ -, (-, (g _))] (_⇒C_.r (α o) q)   ) w    }
            where f = \ {o} -> wirec (\o _ -> Cont.S (TQs o)) 
                                 (\s _ g -> (\ {o} -> _⇒C_.f (α o)) (record { s = s 
                                                                    ; f = \{_} -> g })) {o}          
{-
    foldC : forall {I O} (SPs : Cont* (I + O) O) {TQs : Cont* I O} 
              (α : MorC* (SPs [ TQs ]C*) TQs) 
             -> MorC* (μC SPs) TQs
    foldC {I} {O} SPs {TQs} α o = record { f = foldW (\ {o} -> MorC.f (α o))   
                                         ; r = {!  !} }
          where foldW : ({o : O} -> ⟦ Csnd (SPs o) ⟧ (\ o' -> Cont.S (TQs o')) -> Cont.S (TQs o))
                        -> {o : O} -> (μS SPs o) -> Cont.S (TQs o)
                foldW f w =  wirec (\o _ -> Cont.S (TQs o)) 
                                    (\s _ g -> f (record { s = s 
                                                         ; f = \{_} -> g })) w   
   

{!\{o} {i} w -> 
                                         wirec (\o w -> Cont.P (TQs o) (MorC.f (α o) w) 
                                                     -> Path (\o' i' -> Cont.P (SPs o') (inl i')) o i w) 
                                               (\_ _ g q -> 
                                                [ inl , inr ∘ -, (-, (g _))] (MorC.r α q)) w  !} }
-}