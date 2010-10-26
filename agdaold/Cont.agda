{-# OPTIONS --type-in-type 
  #-}
module ICont where

  open import Data.Product
  open import Data.Unit
  open import Data.Empty
  -- open import Data.Sum -- Not using coz the names are awful
  open import Data.Bool
  open import Relation.Binary.PropositionalEquality


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

    data Cont₁ : Set where
      _◁_ : (S : Set)
         -> (P : S -> Set) 
         -> Cont₁

    data ⟦_⟧₁ : Cont₁ -> Set -> Set where
      _◁_ : {S : Set} {P : S -> Set}{ X : Set } 
              -> (s : S) 
              -> (f : (P s) -> X) 
              -> ⟦ (S ◁ P) ⟧₁ X

    ⟦_⟧₁m : (SP : Cont₁) -> {X Y : Set} 
          -> (X -> Y) 
          -> ⟦ SP ⟧₁ X -> ⟦ SP ⟧₁ Y
    ⟦ S ◁ P ⟧₁m f (s ◁ g) = s ◁ \ p -> f (g p)    

{-
    data NCont (n : ℕ) : Set where
      _◁_ : (S : Set) 
          -> (P : (Fin n) -> S -> Set) 
          -> NCont n  
-}

    data Cont (I : Set) : Set where
      _◁_ : (S : Set) 
          -> (P : I -> S -> Set) 
          -> Cont I  

    FuncO : (I : Set) -> Set
    FuncO I = (I -> Set) -> Set

    FuncO* : (I O : Set) -> Set
    FuncO* I O = O -> FuncO I

    IdFo : {O : Set} -> O -> FuncO O
    IdFo o X = X o 

    data ⟦_⟧ {I : Set} : Cont I -> FuncO I where
      _◁_ : forall {S P X} (s : S ) 
                         -> (f : {i : I} -> P i s -> X i) 
                         -> ⟦ S ◁ P ⟧ X

    FuncM : {I : Set}(F : FuncO I) -> Set
    FuncM {I} F = {X Y : I -> Set} -> ({i : I} -> X i -> Y i)
                                   -> F X -> F Y

    ⟦_⟧m : forall {I} -> (SP : Cont I) -> FuncM  ⟦ SP ⟧
    ⟦_⟧m (S ◁ Ps) f (s ◁ g) =  s ◁  \ p ->  f (g p)  
 
{-
    Cont* : (I O : Set) -> Set
    Cont* I O = O -> Cont I
-}

    data Cont* (I O : Set) : Set where
      _◁_ : (Ss : O -> Set) 
            -> (Ps : {o : O} -> I -> Ss o -> Set) 
            -> Cont* I O

    abs : {I O : Set} -> (O -> Cont I) -> Cont* I O
    abs {I} {O} SPs = S* ◁ P*
            where S* : O -> Set
                  S* o with SPs o
                  ...  | Ss ◁ _ = Ss
                  P* : {o : O} -> I -> S* o -> Set 
                  P* {o} with SPs o
                  ...  | _ ◁ Ps = Ps

    _app_ : {I O : Set} -> Cont* I O -> O -> Cont I
    (Ss ◁ Ps) app o = (Ss o) ◁ (Ps {o})

    ⟦_⟧* : {I O : Set} -> Cont* I O -> FuncO* I O
    ⟦ SPs ⟧* o =  ⟦ SPs app o ⟧

{-
    U : forall { I J } -> Cont (I + J) -> Cont* I J -> Set
    U  (S ◁ P) (Ts ◁ _) =  ⟦ S ◁ (\ j -> P (inr j)) ⟧ Ts

    R : forall { I J } -> (SP : Cont (I + J)) 
                       -> (TQs : Cont* I J) -> I -> U SP TQs -> Set
    R {I} {J} (S ◁ P) (Ts ◁ Qs) i (s ◁ f) =
               P (inl i) s
               + Σ J (\ j -> Σ (P (inr j) s) 
                             (\ p -> Qs i (f p)))
-}



    _[_]C : forall { I J } -> Cont (I + J) -> Cont* I J -> Cont I
    _[_]C {I} {J} (S ◁ P) (T ◁ Qs) = 
        (Σ S (\s -> {j : J} -> P (inr j) s -> T j)) 
      ◁ \i sf ->   P (inl i) (π₀ sf) 
                   + Σ J (\j -> 
                       Σ (P (inr j) (π₀ sf)) (\p -> 
                         Qs i (π₁ sf p)))  

{-

    _[_]C : forall { I J } -> Cont (I + J) -> Cont* I J -> Cont I 
    _[_]C SP TQs = U SP TQs ◁ R SP TQs  

    _[_]C : forall { I J } -> Cont (I + J) -> Cont* I J -> Cont I 
    _[_]C {I} {J} (S ◁ P) (Ts ◁ Qs) = U ◁ R  
                         where U : Set
                               U = ⟦ S ◁ (\ j -> P (inr j)) ⟧ Ts
                               R : I -> U -> Set
                               R i (s ◁ f) =  P (inl i) s
                                            + Σ J (\ j -> Σ (P (inr j) s) 
                                                            (\ p -> Qs i (f p)))
-}  
    

    _[_]C* : forall { I J K } -> Cont* (I + J) K -> Cont* I J -> Cont* I K
    SPs [ TQs ]C* = abs (\ k -> (SPs app k) [ TQs ]C )

{-
    ΣC : forall {I O O'} -> (f : O -> O') 
                         -> Cont* I O -> Cont* I O'
    ΣC {I} {O} f SPs o' = ΣS ◁ ΣP  
             where ΣS = ΣF f IdF o' (S* SPs)
                   ΣP : I -> ΣS -> Set
                   ΣP i (o , (_ , s)) = P* SPs i s
-}
    ΠF : forall {I O O'} -> (f : O -> O') -> FuncO* I O -> FuncO* I O'
    ΠF {O = O} f F o' Xs = (o : O) -> (o' ≡ f o) -> F o Xs  


    ΠC :  forall {I O O'} -> (f : O -> O') 
                          -> Cont* I O -> Cont* I O'
    ΠC {I} {O} {O'} f (Ss ◁ Ps) = ΠS ◁ ΠP
                  where ΠS : O' -> Set
                        ΠS o' = ΠF f IdFo o' Ss
                        ΠP : {o' : O'} -> I -> (ΠS o') -> Set
                        ΠP {o'} i g = Σ O (\ o -> Σ (o' ≡ f o) 
                                                  (\ q -> Ps i (g o q))) 

    data _⇒₁_ : Cont₁ -> Cont₁ -> Set where
      _◁_ : forall {S P T Q} -> (f : S -> T) 
                              -> (r : {s : S} -> Q (f s) -> P s) 
                              -> (S ◁ P) ⇒₁ (T ◁ Q)

    ⟦_⟧₁⇒ : forall {SP TQ} -> (SP ⇒₁ TQ) 
                         -> {X : Set} -> (⟦ SP ⟧₁ X) -> ⟦ TQ ⟧₁ X
    ⟦ f ◁ r ⟧₁⇒ (t ◁ h) = (f t) ◁ (\ q -> h (r q))

    data _⇒C_ {I : Set} : 
                 (SP TQ : Cont I) -> Set where
      _◁_ : forall {S P T Q} 
             ->  (f : S -> T)
             ->  (r : {i : I}{s : S} 
                       -> Q i (f s) -> P i s)
             ->  (S ◁ P) ⇒C (T ◁ Q)

    _⇒C*_ : {I O : Set} -> (SP TQ : Cont* I O) -> Set
    SPs ⇒C* TQs = (o : _) -> (SPs app o) ⇒C (TQs app o)


    ⟦_⟧⇒ : forall {I SP TQ} -> (SP ⇒C TQ) 
                         -> {X : I -> Set} -> (⟦ SP ⟧ X) -> ⟦ TQ ⟧ X
    ⟦ f ◁ r ⟧⇒ (s ◁ h) = (f s) ◁ (\ q -> h (r q))

    q₁ : forall {SP TQ} -> ({X : Set} -> (⟦ SP ⟧₁ X) -> ⟦ TQ ⟧₁ X)
                   -> (SP ⇒₁ TQ) 
    q₁ {S ◁ P} {T ◁ Q} α = f ◁ r  
           where fr : (s : S) -> ⟦ T ◁ Q ⟧₁ (P s)
                 fr s = α {P s} (s ◁ \ p -> p) 
                 f  : S -> T
                 f s with fr s 
                 ... |  (t ◁ _) = t
                 r : {s : S} -> Q (f s) -> P s
                 r {s} with fr s
                 ...   |  (_ ◁ r') = r'

    data WI {I : Set} (S : I -> Set) 
                      (Ps : {i : I} -> I -> S i -> Set) : 
              I -> Set where 
      sup : {i : I} -> (s : S i) 
                     -> (f : {i' : I} ->  Ps i' s -> WI S Ps i') 
                     -> WI S Ps i  


    sup' : {I : Set}{Ss : I -> Set}
           {Ps : {i : I} -> I -> Ss i -> Set}
           {i : I} ->  ⟦ Ss ◁ Ps ⟧* i (WI Ss Ps) -> WI Ss Ps i
    sup' ( s ◁ f ) = sup s f 

{-
    data WI {O : Set} (SPs : Cont* O O) : O -> Set where
      sup : {o : O} -> (s : S* SPs o) 
                     ->(f : {o' : O} -> P* SPs o o' s -> WI SPs o') 
                     -> WI SPs o  
-}  

  
    μS : forall {I O} -> Cont* (I + O) O -> O -> Set
    μS (Ss ◁ Ps) = WI Ss (\ o' s -> Ps (inr o') s)

    Path : forall {I O S} ->
           {Ps : {o : O} -> O -> S o -> Set} -> 
           (Qs : {o : O} -> I -> S o -> Set) 
           {o : O} -> I -> (WI S Ps o) -> Set
    Path {O = O} {Ps = Ps} Qs i (sup s f) = 
           Qs i s + Σ O (\ o' -> Σ (Ps o' s) (\ p -> Path Qs i (f p)) )   


    μC : forall {I O} -> Cont* (I + O) O -> Cont* I O 
    μC (Ss ◁ Ps)  = WI Ss (\ o' s -> Ps (inr o') s)
                  ◁ Path (\i s -> Ps (inl i) s)


    inC : forall {I O} {SPs : Cont* (I + O) O} -> 
            SPs [ μC SPs ]C* ⇒C* μC SPs
    inC {SPs = S ◁ Ps} o =  ( \ t -> sup (π₀ t) ((π₁ t {_}))) ◁ \ p -> p 

    data ℕ : Set where
      zero : ℕ
      suc  : ℕ -> ℕ  

    data Fin : ℕ -> Set where
      zero : (n : ℕ) -> Fin (suc n)
      suc  : (n : ℕ) -> Fin n -> Fin (suc n)

    GFin : (ℕ -> Set) -> ℕ -> Set
    GFin X n = Σ ℕ (\ m -> (m ≡ suc n) × (⊤ + X m))

    GLam : (ℕ -> Set) -> ℕ -> Set
    GLam X n = Fin n + (X n) × (X n) + Σ ℕ (\ m -> (m ≡ suc n) × X m)