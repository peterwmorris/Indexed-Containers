{-# OPTIONS --type-in-type
  #-}

module IndCont where

module ICont where

  data Zero : Set where
  
  _Ψ : Zero -> {S : Set} -> S
  () Ψ   
  
  record One : Set where
  
  <> : One
  <> = record {}
  
  record Sig {S : Set} (T : S -> Set) : Set where
    field fst : S
    field snd : T fst
  
  open module Sig' {S : Set}{T : S -> Set} =
                Sig {S}{T}
  
  tup : {S : Set} {T : S -> Set} -> 
           (s : S) -> (T s) -> Sig T
  tup s t = record {fst = s;
                    snd = t}
  
  record Sig2 {S : Set} {T : S -> Set} (U : (s : S) -> T s -> Set) : Set where
    field fst₂ : S
    field snd₂ : T fst₂
    field thd₂ : U fst₂ snd₂
  
  open module Sig2' {S : Set}{T : S -> Set}{U : (s : S) -> T s -> Set} = 
                Sig2 {S}{T}{U}
  
  tup₂ : {S : Set} {T : S -> Set} {U : (s : S) -> T s -> Set} ->
           (s : S) -> (t : T s) -> (U s t) -> Sig2 U
  tup₂ s t u = record {fst₂ = s;
                       snd₂ = t;
                       thd₂ = u}
  
  data _+_ (A B : Set) : Set where
    left : (a : A) -> A + B
    right : (b : B) -> A + B
  
  _∇_ : {A B : Set} {C : Set1} -> (f : A -> C) -> (g : B -> C) -> A + B -> C
  (f ∇ g) (left a) = f a
  (f ∇ g) (right b) = g b
  
  Bool : Set
  Bool = One + One
  
  tt : Bool
  tt = left <>
  
  ff : Bool 
  ff = right <>
  
  data Eq (X : Set) (a : X) : (b : X) -> Set where
    refl : Eq X a a
  
  record IC (I : Set) : Set1 where
    field sh : Set
    field po : sh -> I -> Set
  
  open module IC' {I : Set} = 
               IC {I}
  
  _◁_ : {I : Set} -> (S : Set) -> (P : S -> I -> Set) -> IC I
  S ◁ P = record {sh = S; po = P}
  
  ICont : (I O : Set) -> Set1
  ICont I O = O -> IC I
  
  record Ext {I : Set} (C : IC I) (X : I -> Set) : Set where
    field con : sh C
    field pay : (i : I) -> (p : (po C) con i) -> X i
  
  open module Ext' {I : Set}{C : IC I}{X : I -> Set} =
                Ext {I}{C}{X}
  
  ext : {I : Set} {C : IC I} {X : I -> Set} -> (s : sh C) ->
           ((i : I) -> (po C) s i -> X i) -> Ext C X
  ext s f = record {con = s; pay = f}
  
  ⟦_⟧ : {I O : Set} (C : ICont I O ) (X : I -> Set) -> O -> Set
  ⟦ C ⟧ X o = Ext (C o) X
  
  ⟦_⟧M : {I O : Set}(C : ICont I O){X Y : I -> Set} ->
           (f : (i : I) -> X i -> Y i) ->
             (o : O) -> ⟦ C ⟧ X o -> ⟦ C ⟧ Y o
  ⟦ C ⟧M f o v = ext (con v) (\i p -> f i ((pay v) i p))
   
  CZero : {I : Set} -> IC I  
  CZero = Zero ◁ (\s i -> Zero) 
  
  COne : {I : Set} -> IC I
  COne = One ◁ (\s i -> Zero)
  
  CK : {I : Set} -> IC I  
  CK = One ◁ (\s i -> One)
  
  CΣ : {I O O' : Set} -> (O -> O') -> (ICont I O) -> ICont I O'
  CΣ {I} {O} {O'} f C o' = (Sig2 (\(o : O) (e : Eq O' (f o) o') -> S o)) ◁
                             (\s i -> P (fst₂ s) (thd₂ s) i)              
    where S = \(o : O) -> sh (C o)  
          P = \(o : O) -> po (C o) 
  
  CΔ : {I O O' : Set} -> (O' -> O) -> (ICont I O) -> ICont I O'
  CΔ {I} {O} {O'} f C o' = C (f o')
  
  CΠ : {I O O' : Set} -> (O -> O') -> (ICont I O) -> ICont I O'
  CΠ {I} {O} {O'} f C o' = ((o : O) -> Eq O' (f o) o' -> S o) ◁
                            (\shf i -> Sig2 (\(o : O) (e : Eq O' (f o) o') -> 
                              P o (shf o e) i))
    where S = \(o : O) -> sh (C o)  
          P = \(o : O) -> po (C o) 
  
  data W (O : Set) (S : O -> Set) (P : (o : O) -> S o -> O -> Set) : O -> Set
    where sup : {o : O} -> (s : S o) -> ((o' : O) -> P o s o' -> W O S P o') 
                                            -> W O S P o  
  
  wπ₀ : forall {O} {S} {P} {o} -> (w : W O S P o) -> S o
  wπ₀ (sup s f) = s
  
  wπ₁ : forall {O} {S} {P} {o} -> (w : W O S P o) -> 
          (o' : O) -> P o (wπ₀ w) o' -> W O S P o'
  wπ₁ (sup s f) = f
  
  wrec : forall {O S P} -> {C : (o : O) -> W O S P o -> Set}   
    (h : (o : O) -> (s : S o) -> (f : (o' : O) -> P o s o' -> W O S P o') ->
          (g : (o' : O) -> (p : P o s o') -> C o' (f o' p)) -> C o (sup s f)) ->
      (o : O) -> (w : W O S P o) -> C o w
  wrec {C = C} h o (sup s f) = h o s f (\o' p -> wrec {C = C} h o' (f o' p))
  
  data Path {O : Set} {S : O -> Set} {P : (o : O) -> S o -> O -> Set} 
              {I : Set} (Q : (o : O) -> S o -> I -> Set) :
                (o : O) -> (W O S P o) -> I -> Set where
    here  : {o : O} -> {w : W O S P o} ->
             {i : I} -> (Q o (wπ₀ w) i) -> Path Q o w i
    there : {o : O} -> {w : W O S P o} 
             {i : I} -> (o' : O) -> (p : P o (wπ₀ w) o') -> 
               Path Q o' ((wπ₁ w) o' p) i -> Path Q o w i
  
  Cμ : {I O : Set} -> ICont (I + O) O -> ICont I O
  Cμ {I} {O} C o = (W O S Pr o) ◁ (Path P o)
    where S = \(o : O) -> sh (C o)
          P = \(o : O) (s : S o) (i : I) -> (po (C o)) s (left i)
          Pr = \(o : O) (s : S o) (o' : O) -> (po (C o)) s (right o')
  
  Cη : {I : Set} -> ICont I I
  Cη {I} i = One ◁ (\s j -> Eq I i j)
  
  _>>=_ : {I J : Set} -> IC I -> (I -> IC J) -> IC J
  (_>>=_) {I} {J} A F = T ◁ Q
    where S : Set
          S = sh A
          P : S -> I -> Set
          P = po A
          T : Set
          T = Sig (\(s : S) -> ((i : I) -> P s i -> sh (F i)))
          Q : T -> J -> Set
          Q t j = Sig2 (\(i : I) (p : P (fst t) i) -> po (F i) ((snd t) i p) j)
  
  data ISPT : (I : Set) -> Set1 where
   K0  : {I : Set}                                           -> ISPT I
   K1  : {I : Set}                                           -> ISPT I
   η   : {I : Set}                                     -> I  -> ISPT I
   Σ   : {I O O' : Set} -> (O  -> O') -> (O -> ISPT I) -> O' -> ISPT I
   Δ   : {I O O' : Set} -> (O' -> O ) -> (O -> ISPT I) -> O' -> ISPT I
   Π   : {I O O' : Set} -> (O  -> O') -> (O -> ISPT I) -> O' -> ISPT I
   μ   : {I O : Set}            -> (O -> ISPT (I + O)) -> O  -> ISPT I 
  
  eval : {I : Set} -> ISPT I -> IC I
  eval K0         = CZero
  eval K1         = COne
  eval (η i)      = Cη i
  eval (Σ f T o') = CΣ f (\o -> eval (T o)) o'
  eval (Δ f T o') = CΔ f (\o -> eval (T o)) o'
  eval (Π f T o') = CΠ f (\o -> eval (T o)) o'
  eval (μ F o)    = Cμ (\o' -> eval (F o')) o
  
  cunit : {I : Set} -> {X : I -> Set} ->  Ext COne X
  cunit = ext <> (\i p -> p Ψ)  
  
  cσ : {I O O' : Set} -> {f : O -> O'} -> {C : ICont I O} -> 
        {X : I -> Set} -> {o' : O'} -> 
          (o : O) -> (e : Eq O' (f o) o') -> ⟦ C ⟧ X o -> ⟦ CΣ f C ⟧ X o'
  cσ o e v = ext (tup₂ o e (con v)) (pay v)
  
  cδ : {I O O' : Set} -> {f : O' -> O} -> {C : ICont I O} -> 
        {X : I -> Set} -> {o' : O'} -> 
          ⟦ C ⟧ X (f o') -> ⟦ CΔ f C ⟧ X o'
  cδ v = v
  
  cπ : {I O O' : Set} -> {f : O -> O'} -> {C : ICont I O} -> 
         {X : I -> Set} -> {o' : O'} -> 
           ((o : O) -> (e : Eq O' (f o) o') -> ⟦ C ⟧ X o) -> ⟦ CΠ f C ⟧ X o'
  cπ {C = C} f = ext (\o e -> con (f o e)) 
                      (\i t -> pay (f (fst₂ t) (snd₂ t)) i (thd₂ t)) 
  
  cin : {I O : Set} -> {C : ICont (I + O) O} -> {X : I -> Set} -> {o : O} ->
         (⟦ C ⟧ (X ∇ ⟦ Cμ C ⟧ X) o) -> ⟦ Cμ C ⟧ X o
  cin {I} {O} {C} {X} {o} v = ext s' f'
    where s : sh (C o)
          s = con v 
          f : (io : I + O) -> (po (C o) s io) -> (X ∇ ⟦ Cμ C ⟧ X) io
          f = pay v
          s' : sh (Cμ C o) 
          s' = (sup s (\o' p -> con (f (right o') p)))
          f' : (i : I) -> po (Cμ C o) s' i -> X i
          f' i (here q) = f (left i) q
          f' i (there o' p r) = pay (f (right o') p) i r
  
  cvar : forall {I} {X} {i} -> X i -> ⟦ Cη ⟧ X i
  cvar {I} {X} {i} x = ext <> f
    where f : (i' : I) -> Eq I i i' -> X i'
          f .i refl = x 
  
  fold : forall {I} {O} {X} {Y} -> {F : ICont (I + O) O} ->
           (α : (o : O) -> ⟦ F ⟧ (X ∇ Y) o -> Y o) (o : O) -> 
              ⟦ Cμ F ⟧ X o -> Y o
  fold {I} {O} {X} {Y} {F} α o v = wrec {C = C} H o w k 
    where S = \(o : O) -> sh (F o)
          P = \(o : O) (s : S o) (o' : O) -> (po (F o)) s (right o')
          Q = \(o : O) (s : S o) (i : I) -> (po (F o)) s (left i)
          w : W O S P o 
          w = con v
          k : (i : I) -> Path Q o w i -> X i
          k = pay v
          C : (o : O) -> W O S P o -> Set
          C o w = ((i : I) -> Path Q o w i -> X i) -> Y o
          H : (o : O) -> (s : S o) -> (f : (o' : O) -> P o s o' -> W O S P o') ->
               (g : (o' : O) -> (p : P o s o') -> C o' (f o' p)) -> C o (sup s f)
          H o s f g l = α o (ext s foo)
            where foo : ((i : I + O) -> po (F o) s i -> (X ∇ Y) i)
                  foo (left i) p = l i (here p)
                  foo (right o') q = g o' q (\i r -> l i (there o' q r))
  
  ccomp : forall {I} {O} {X} {A : IC O} {F : ICont I O} -> 
            Ext A (⟦ F ⟧ X) -> Ext (A >>= F) X
  ccomp v = ext (tup s (\o p -> con (f o p))) 
                  (\i p -> pay (f (fst₂ p) (snd₂ p)) i (thd₂ p)) 
    where s = con v; f = pay v

module SPF where

  
