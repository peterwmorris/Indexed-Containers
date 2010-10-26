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

    id : {A : Set} -> A -> A
    id x = x

    ψ : {A : ⊥ -> Set} -> (z : ⊥) -> A z
    ψ ()

    <> : ⊤
    <> = record {}

    data ℕ : Set where
      zero : ℕ
      suc : ℕ -> ℕ

  module BasicContainers where

    open Utils

    data Cont (I O : Set) : Set where
      _◁_ : (S : O -> Set) 
            -> (Ps : (o : O) -> I -> S o -> Set) 
            -> Cont I O

    Func : (I O : Set) -> Set 
    Func I O = (I -> Set) -> O -> Set
{-
    Map : {I O : Set}(Func I O) -> Set
    Map F = {X Y : I -> Set}
            ((i : I) -> X i -> Y i)
            -> (o : O) -> F X o -> F Y o
-}

    data ⟦_⟧ {I O : Set} : Cont I O -> Func I O where
      _◁_ : forall {S Ps X o} (s : S o) 
                              -> (f : {i : I} -> Ps o i s -> X i) 
                              -> ⟦ S ◁ Ps ⟧ X o

    con : forall {I O S Xs o} {Ps : (o : O) -> I -> S o -> Set} -> 
            ⟦ S ◁ Ps ⟧ Xs o -> S o
    con (s ◁ _) = s   

    pay : forall {I O S Xs o} {Ps : (o : O) -> I -> S o -> Set} -> 
            (v : ⟦ S ◁ Ps ⟧ Xs o) -> {i : I} -> Ps o i (con v) -> Xs i
    pay (_ ◁ f) = f   

    ⟦_⟧m : forall {I O Xs} -> (C : Cont I O) -> {Ys : I -> Set} -> 
             ({i : I} -> Xs i -> Ys i) -> {o : O} -> ⟦ C ⟧ Xs o -> ⟦ C ⟧ Ys o
    ⟦_⟧m (S ◁ Ps) f (s ◁ g) = s ◁ \p -> f (g p)

    data ⟦_⟧₌ {I O : Set} {Xs : I -> Set} {o : O} : 
               (C : Cont I O) -> (u v : ⟦ C ⟧ Xs o) -> Set where
      _◁₌_ : forall {S Ps s t} {f : {i : I} -> Ps o i s -> Xs i} 
                               {g : {i : I} -> Ps o i t -> Xs i}  
             -> (eqs : s ≅ t) 
             -> ({i : I} -> (p : Ps o i s) -> 
                  f p ≅ g (≅-subst (\(x : S o) -> Ps o i x) eqs p)) 
             -> ⟦ S ◁ Ps ⟧₌ (s ◁ f) (t ◁ g)

    data _⇒C_ {I O : Set} : (SPs TQs : Cont I O) -> Set where
      _◁_ : forall {S Ps T Qs} 
             -> (f : {o : O} -> S o -> T o)
             -> (r : {o : O}{i : I}{s : S o} -> Qs o i (f s) -> Ps o i s)
             -> (S ◁ Ps) ⇒C (T ◁ Qs)

    _⇒_ : {I O : Set} -> (F G : Func I O) -> Set 
    _⇒_ {I} {O} F G = {Xs : I -> Set} {o : O} -> F Xs o -> G Xs o

    data _≃_ { I O : Set } (F G : Func I O) : Set where
      iso :  (F ⇒ G) -> (G ⇒ F) -> F ≃ G 

    ⟦_⟧N : forall {I O} -> {SPs : Cont I O} -> {TQs : Cont I O}
               -> (SPs) ⇒C (TQs) -> ⟦ SPs ⟧ ⇒ ⟦ TQs ⟧
    ⟦_⟧N {SPs = S ◁ Ps} {TQs = T ◁ Qs} (f ◁ r) {Xs} (s ◁ l) = f s ◁ \q -> l (r q) 

    q : forall {I O S T} {Ps : (o : O) -> I -> S o -> Set} 
                         {Qs : (o : O) -> I -> T o -> Set} ->
          (⟦ S ◁ Ps ⟧ ⇒ ⟦ T ◁ Qs ⟧) -> (S ◁ Ps) ⇒C (T ◁ Qs)
    q {I} {O} {S} {T} {Ps} {Qs} n = f ◁ r 
      where trick = \{o : O} (s : S o) -> s ◁ (\p -> p) 
            f : {o : O} -> S o -> T o   
            f s with n (trick s)
            ...    | t ◁ _ = t 
            r : {o : O} {i : I} {s : S o} -> Qs o i (f s) -> Ps o i s
            r {s = s} with n (trick s) 
            ...          | _ ◁ g = g 

    0C : {I O : Set} -> Cont I O  
    0C = (\_ -> ⊥) ◁ (\_ _ _ -> ⊥) 

    0F : {I O : Set} -> Func I O
    0F Xs o = ⊥

    0isor : {I O : Set} -> 0F {I} {O} ⇒ ⟦ 0C {I} {O} ⟧
    0isor ()    

    0isol : {I O : Set} -> ⟦ 0C {I} {O} ⟧ ⇒ 0F {I} {O}
    0isol (() ◁ f)

    0iso : {I O : Set} -> ⟦ 0C {I} {O} ⟧ ≃ 0F {I} {O}
    0iso = iso 0isol 0isor  

    1C : {I O : Set} -> Cont I O
    1C = (\_ -> ⊤) ◁ (\_ _ _ -> ⊥)

    1F : {I O : Set} -> Func I O
    1F Xs o = ⊤

    1isor : {I O : Set} -> 1F {I} {O} ⇒ ⟦ 1C {I} {O} ⟧
    1isor {I} {O} {Xs} v = tt ◁ ⊥-elim    

    1isol : {I O : Set} -> ⟦ 1C {I} {O} ⟧ ⇒ 1F {I} {O}
    1isol {o = o} (s ◁ f) = tt 

    1iso : {I O : Set} -> ⟦ 1C {I} {O} ⟧ ≃ 1F {I} {O}
    1iso = iso 1isol 1isor  

    IdC : {O : Set} -> Cont O O
    IdC = (\_ -> ⊤) ◁ (\i o _ -> i ≅ o)

    IdF : {O : Set} -> Func O O
    IdF Xs = Xs
  
    Kisor : {O : Set} -> IdF {O} ⇒ ⟦ IdC {O} ⟧
    Kisor {O} {Xs} v = tt ◁  \ eq -> ≅-subst (\i -> Xs i) eq v   

    Kisol : {O : Set} -> ⟦ IdC {O} ⟧ ⇒ IdF {O}
    Kisol {o = o} (s ◁ f) = f ≅-refl 

    Kiso : {O : Set} -> ⟦ IdC {O} ⟧ ≃ IdF {O}
    Kiso = iso Kisol Kisor  

    ΔC : forall {I O O'} -> (f : O' -> O) -> Cont I O -> Cont I O'
    ΔC f (S ◁ Ps) = (S ∘ f) ◁ (\o' -> Ps (f o'))

    ΔF : forall {I O O'} -> (f : O' -> O) -> Func I O -> Func I O'
    ΔF f F Xs = (F Xs) ∘ f 

    Δisor : forall {I O O'} (f : O' -> O) (C : Cont I O) -> 
                 ΔF f ⟦ C ⟧ ⇒ ⟦ ΔC f C ⟧
    Δisor f (S ◁ Ps) {Xs} {o} (s ◁ g) = s ◁ g

    Δisol : forall {I O O'} (f : O' -> O) (C : Cont I O) -> 
                 ⟦ ΔC f C ⟧ ⇒  ΔF f ⟦ C ⟧
    Δisol f (S ◁ Ps) {Xs} {o} (s ◁ g) = s ◁ g

    Δiso : forall {I O O'} (f : O' -> O) (C : Cont I O) -> 
                ⟦ ΔC f C ⟧ ≃ ΔF f ⟦ C ⟧
    Δiso f C = iso (Δisol f C) (Δisor f C)

    ΣC : forall {I O O'} -> (f : O -> O') -> Cont I O -> Cont I O'
    ΣC {O = O} f (S ◁ Ps) = (\o' -> Σ O (\ o -> (o' ≅ (f o)) × S o))
                               ◁ \o' i t -> Ps (π₀ t) i (π₁ (π₁ t)) 

    ΣF : forall {I O O'} -> (f : O -> O') -> Func I O -> Func I O'
    ΣF {O = O} f F Xs o' = Σ O (\o -> Σ (o' ≅ f o) (\_ -> F Xs o))  

    Σisor : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                 ΣF f ⟦ C ⟧ ⇒ ⟦ ΣC f C ⟧
    Σisor f (S ◁ Ps) (o , eq , s ◁ g) = (o , eq , s) ◁ g 
  
    Σisol : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                 ⟦ ΣC f C ⟧ ⇒  ΣF f ⟦ C ⟧ 
    Σisol f (S ◁ Ps) ((o , eq , s) ◁ g) = (o , eq , s ◁ g) 

    Σiso : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                ⟦ ΣC f C ⟧ ≃ ΣF f ⟦ C ⟧
    Σiso f C = iso (Σisol f C) (Σisor f C)

    ΠC : forall {I O O'} -> (f : O -> O') -> Cont I O -> Cont I O'
    ΠC {O = O} f (S ◁ Ps) = (\o' -> (o : O) -> (o' ≅ (f o)) -> S o)
                               ◁ \o' i g -> 
                                  Σ O (\o -> 
                                   Σ (o' ≅ (f o)) (\eq -> Ps o i (g o eq ))) 

    ΠF : forall {I O O'} -> (f : O -> O') -> Func I O -> Func I O'
    ΠF {O = O} f F Xs o' = (o : O) -> (o' ≅ f o) -> F Xs o  

    Πisor : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                 ΠF f ⟦ C ⟧ ⇒ ⟦ ΠC f C ⟧
    Πisor f (S ◁ Ps) v = 
        (\o eq -> con (v o eq)) 
      ◁ \t -> pay (v (π₀ t) (π₀ (π₁ t))) (π₁ (π₁ t))  
  
    Πisol : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                 ⟦ ΠC f C ⟧ ⇒  ΠF f ⟦ C ⟧
    Πisol f (S ◁ Ps) (s ◁ f') = \o eq -> (s o eq) ◁ \p -> f' (o , eq , p)   

    Πiso : forall {I O O'} (f : O -> O') (C : Cont I O) -> 
                ⟦ ΠC f C ⟧ ≃ ΠF f ⟦ C ⟧
    Πiso f C = iso (Πisol f C) (Πisor f C)

  module FixedPoints where

    open Utils
    open BasicContainers

    _[_]F : forall { I J K } -> Func (I + J) K -> Func I J -> Func I K
    G [ F ]F  =  \Xs k ->  G [ Xs ,  F Xs ] k

    _[_] : forall { I J K } -> Cont (I + J) K -> Cont I J -> Cont I K
    _[_] {I} {J} (S ◁ Ps) (T ◁ Qs) = 
        (\k -> Σ (S k) (\s ->  {j : J} -> Ps k (inr j) s -> T j)) 
      ◁ \k i sf ->   Ps k (inl i) (π₀ sf) 
                   + Σ J (\j -> 
                       Σ (Ps k (inr j) (π₀ sf)) (\p -> 
                         Qs j i (π₁ sf p)))  



    substisol : forall { I J K } -> (SPs : Cont (I + J) K)(TQs : Cont I J) 
                -> ⟦ SPs [ TQs ] ⟧ ⇒ ⟦ SPs ⟧ [ ⟦ TQs ⟧ ]F
    substisol (S ◁ Ps) (T ◁ Qs) {Xs} {k} ((s , ts) ◁ f) = 
       s ◁ \{ ij } -> +elim ((\ij -> Ps k ij s -> [ Xs , ⟦ T ◁ Qs ⟧ Xs ] ij)) 
                             (\i p -> f (inl p))
                             (\j p -> ts p ◁ \qs -> f (inr ((j , p , qs)))) ij 

    substisor : forall { I J K } -> (SPs : Cont (I + J) K)(TQs : Cont I J) 
                -> ⟦ SPs ⟧ [ ⟦ TQs ⟧ ]F ⇒ ⟦ SPs [ TQs ] ⟧
    substisor (S ◁ Ps) (T ◁ Qs) {Xs} {k} (s ◁ f) = 
        (s , \{_} p -> con (f p)) 
      ◁ [ f , (\t -> pay (f (π₀ (π₁ t))) (π₁ (π₁ t)) ) ]  

    substiso : forall { I J K } -> (SPs : Cont (I + J) K)(TQs : Cont I J) 
                -> ⟦ SPs [ TQs ] ⟧ ≃ ⟦ SPs ⟧ [ ⟦ TQs ⟧ ]F
    substiso SPs TQs =  iso (substisol SPs TQs) (substisor SPs TQs)  

    data WI {O : Set} (S : O -> Set) (P : (o : O) -> O -> S o -> Set) : 
              O -> Set where 
      sup : {o : O} -> (s : S o) 
                     -> (f : {o' : O} -> P o o' s -> WI S P o') 
                     -> WI S P o  

    wirec : forall {O S P} -> (C : (o : O) -> WI S P o -> Set)   
      (h : {o : O} -> (s : S o) -> (f : {o' : O} -> P o o' s -> WI S P o') ->
            (g : {o' : O} -> (p : P o o' s) -> C o' (f p)) -> C o (sup s f)) ->
        {o : O} -> (w : WI S P o) -> C o w
    wirec C h (sup s f) = h s f (\p -> wirec C h (f p))

    Path : {I O : Set}{S : O -> Set}{P : (o : O) -> O -> S o -> Set} 
             (Q : (o : O) -> I -> S o -> Set) (o : O) -> I -> (WI S P o) -> Set
    Path {I} {O} {S} {P} Q _ i w = 
      wirec (\_ _ -> Set)  
            (\{o} s f g -> (Q o i s) + Σ O (\o' -> Σ (P o o' s) (\p -> g p))) 
            w    

    μC : forall {I O} -> Cont (I + O) O -> Cont I O 
    μC (S ◁ Ps) =   WI S (\o' o -> Ps o' (inr o)) 
                  ◁ Path (\o' i -> Ps o' (inl i)) 

    inC : forall {I O} {F : Cont (I + O) O} -> 
            F [ μC F ] ⇒C μC F
    inC {F = S ◁ Ps} = (\t -> sup (π₀ t) (π₁ t {_})) ◁ \p -> p     


    foldW : forall {O S} {Ps : (o : O) -> O -> S o -> Set} {T : O -> Set} ->
             ({o : O} -> Σ (S o) (\s -> {o' : O} -> Ps o o' s -> T o') -> T o)
               -> {o : O} -> WI S (\o' o'' -> Ps o' o'') o -> T o
    foldW {T = T} α w = 
      wirec (\o _ -> T o) (\s f g -> α (s , \{_} -> g)) w  

    foldC : forall {I O} {SPs : Cont (I + O) O} {TQs : Cont I O}
              (α : SPs [ TQs ] ⇒C TQs) -> μC SPs ⇒C TQs
    foldC {I} {O} {SPs = S ◁ Ps} {TQs = T ◁ Qs} (f ◁ r) = 
              foldW f 
            ◁ \{o} {i} {w} -> 
                wirec (\o w -> Qs o i (foldW f w) -> 
                         Path (\o' i' -> Ps o' (inl i')) o i w) 
                  (\_ _ g q -> 
                    [ inl , inr ∘ -, (-, (g _))] (r q)) w 



  module SPF where

   open Utils
   open BasicContainers
   open FixedPoints

   data TCont (I : Set) : Set where
     _◁_ : (S : Set) -> (I -> S -> Set) -> TCont I

   sh : {I : Set} -> TCont I -> Set
   sh (S ◁ _) = S

   po : {I : Set} -> (T : TCont I) -> I -> sh T -> Set
   po (_ ◁ P) = P

   Cont' : (I O : Set) -> Set
   Cont' I O = O -> TCont I

   ⌈_⌉ : {I O : Set} -> (Cont I O) -> Cont' I O
   ⌈ S ◁ Ps ⌉ o = (S o) ◁ Ps o

   ⌊_⌋ : {I O : Set} -> Cont' I O -> Cont I O
   ⌊ C ⌋ = (\o -> sh (C o)) ◁ (\o -> po (C o))

   _* : (Set -> Set) -> Set -> Set -> Set
   (X *) I O = O -> X I

   data SPT : (I : Set) -> Set where
     KU  : forall {I}                                -> SPT I
     KU  : forall {I}                                -> SPT I
     IdU    : forall {O}                                -> (SPT *) O O

--     ΣU     : forall {I O O'} -> (O -> O')     -> SPF I O -> SPF I O'
 --    ΠU     : forall {I O O'} -> (O -> O')     -> SPF I O -> SPF I O'
  --   μU     : forall {I O}    -> SPF (I + O) O            -> SPF I O
   --
--     elISPT : {I : Set} -> ISPT I -> TCont I
  --   elISPT ZeroU    = ⌈ 0C ⌉ <>   
    -- elISPT UnitU    = ⌈ 1C ⌉ <>   
--     elISPT (IdU o)      = ⌈ IdC ⌉ o 
  --   elISPT (ΣU f F o')  = ⌈ ΣC f (elSPF F) ⌉ o' 
    -- elISPT (ΠU f F o')  = ⌈ ΠC f (elSPF F) ⌉ o'  
--     elISPT (μU F o)     = ⌈ μC (elSPF F) ⌉ o  

  --   elSPF : {I O : Set} -> SPF I O -> Cont I O
    -- elSPF F = ⌊ (\o -> elISPT (F o)) ⌋


{-
   wk : {I J : Set} -> ISPT I -> (I -> J) -> ISPT J
   wk (ZeroU y) f = ZeroU y 
   wk (UnitU y) f = UnitU y 
   wk (IdU y) f = IdU (f y) 
   wk (ΣU y y' y0) f = ΣU y (\x -> wk (y' x) f) y0
   wk (ΠU y y' y0) f = ΠU y (\x -> wk (y' x) f) y0 
   wk (μU y y') f = μU (\x -> wk (y x) ([ inl ∘ f , inr ])) y'  

   wkF : {I J O : Set} -> SPF I O -> (I -> J) -> SPF J O
   wkF F f o = wk (F o) f  

   Bind : {I J : Set} -> ISPT I -> SPF J I -> ISPT J
   Bind (ZeroU y) T = ZeroU y 
   Bind (UnitU y) T = UnitU y 
   Bind (IdU y) T = T y 
   Bind (ΣU y y' y0) T = ΣU y (\x -> Bind (y' x) T) y0 
   Bind (ΠU y y' y0) T = ΠU y (\x -> Bind (y' x) T) y0 
   Bind (μU y y') T = 
     μU (\x -> Bind (y x) ([ (\i -> wk (T i) inl) , IdU ∘ inr ])) y' 

   _>>=_ : {I J O : Set} -> SPF I O -> SPF J I -> SPF J O
   (F >>= A) o = Bind (F o) A 

   _[_]U : forall { I J K } -> SPF (I + J) K -> SPF I J -> SPF I K 
   F [ A ]U = F >>= ([ IdU , A ]) 

   _UpU_ : {I O : Set} -> SPF I O -> SPF I O -> SPF I O
   _UpU_ {O = O} A B = 
     ΣU ([ id , id ]) ([ A , B ])        

   _UtU_ : {I O : Set} -> SPF I O -> SPF I O -> SPF I O
   _UtU_ {O = O} A B = 
     ΠU ([ id , id ]) ([ A , B ])     

   UFin : SPF ⊥ ℕ
   UFin = μU ((ΣU suc UnitU) UpU (ΣU suc (IdU ∘ inr)))

   ULam : SPF ⊥ ℕ
   ULam = μU ((wkF UFin ψ) UpU (((IdU ∘ inr) UtU (IdU ∘ inr)) UpU ((IdU ∘ inr) ∘ suc)))   
-}
{-
  
  fold□ : forall {I O S T} {Ps : (o : O) -> I + O -> S o -> Set}
            {Qs : (o : O) -> I -> T o -> Set} {Xs : I -> Set} {o : O}
              (α : (S ◁ Ps)[ T ◁ Qs ] ⇒C (T ◁ Qs)) -> 
                (v : ⟦ (S ◁ Ps)[ μC (S ◁ Ps) ] ⟧ Xs o) -> ⟦ T ◁ Qs ⟧₌ (⟦ foldC {Ps = Ps} α ⟧N (⟦ inC {Ps = Ps} ⟧N v )) (⟦ α ⟧N (substisor (S ◁ Ps) (T ◁ Qs) (⟦ S ◁ Ps ⟧m  (\{i} -> +-elim (\ i -> [ Xs , ⟦ μC (S ◁ Ps) ⟧ Xs ] i -> [ Xs , ⟦ T ◁ Qs ⟧ Xs ] i ) (\i x -> x) (\i -> ⟦ foldC {Ps = Ps} α ⟧N) i) (substisol (S ◁ Ps) (μC (S ◁ Ps)) v)))) 

  fold□ {I} {O} {T = T} {Ps = Ps} {Qs = Qs} {o = o} (f ◁ r) ((s , g) ◁ h) = ≅-refl ◁₌ \{_} q -> help (r q) 
    where help : {i : I} 
           -- (p : Qs o i (f (s , \{_} p' -> wirec (\o' _ -> T o') (\{o} s' f' g' -> f (s' , \{_} -> g')) (g p'))))
           (rq : Ps o (inj₁ i) s +
                 Σ O
                 (\j ->
                   Σ (Ps o (inj₂ j) s)
                   (\p ->
                   Qs j i
                   (wirec (\o' _ -> T o') (\{o'} s' f' g' -> f (s' , \{_} -> g'))
                   (g p)))))
           ->
           h
           ([ inj₁ ,
            (\x ->
               inj₂
               (map-Σ₂
                (\{x} ->
                   map-Σ₂
                   (\{x'} ->
                      wirec (\o' w ->
                         Qs o' i
                         (wirec (\o0 _ -> T o0) (\{o} s' f' g' -> f (s' , \{_} -> g'))
                         w) ->
                         Path (\o0 i' -> Ps o0 (inj₁ i')) o' i w)
                      (\{o} s' f' g' q' ->
                         [ inj₁ ,
                         (\x' -> inj₂ (map-Σ₂ (\{x0} -> map-Σ₂ (\{x1} -> g' x1)) x')) ]
                         (r q'))
                      (g x')))
                x))
            ]
            rq)
           ≅
           [ (\p' -> h (inj₁ p')) ,
           (\t ->
              h
              (inj₂
               (proj₁ t ,
                proj₁ (proj₂ t) ,
                wirec (\o' w ->
                        Qs o' i
                        (wirec (\o0 _ -> T o0) (\{o} s' f' g' -> f (s' , \{_} -> g'))
                        w) ->
                        Path (\o0 i' -> Ps o0 (inj₁ i')) o' i w)
                     (\{o} s' f' g' q' ->
                   [ inj₁ ,
                   (\x -> inj₂ (map-Σ₂ (\{x} -> map-Σ₂ (\{x'} -> g' x')) x)) ]
                   (r q'))
                (g (proj₁ (proj₂ t))) (proj₂ (proj₂ t)))))
           ]
           rq
          help (inj₁ y) = ≅-refl 
          help (inj₂ (x , x' , y)) = ≅-refl   

-}
