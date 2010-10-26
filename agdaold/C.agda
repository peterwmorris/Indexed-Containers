{-# OPTIONS --type-in-type
  #-}

module Cont where

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

_×_ : (A B : Set) -> Set
A × B = Sig (\(a : A) -> B)

record Sig2 {S : Set} {T : S -> Set} (U : (s : S) -> T s -> Set) : Set where
 field fst₂ : S
 field snd₂ : T fst₂
 field thd₂ : U fst₂ snd₂

open module Sig2' {S : Set} {T : S -> Set} {U : (s : S) -> T s -> Set} = 
              Sig2 {S} {T} {U}

tup₂ : {S : Set} {T : S -> Set} {U : (s : S) -> T s -> Set} ->
         (s : S) -> (t : T s) -> (U s t) -> Sig2 U
tup₂ s t u = record {fst₂ = s;
                     snd₂ = t;
                     thd₂ = u}

data _+_ (A B : Set) : Set where
  left  : (a : A) -> A + B
  right : (b : B) -> A + B

_∇_ : {A B : Set} {C : Set} -> (f : A -> C) -> (g : B -> C) -> A + B -> C
(f ∇ g) (left a) = f a
(f ∇ g) (right b) = g b 

data Eq (X : Set) (a : X) : (b : X) -> Set where
  refl : Eq X a a

data Nat : Set where zero : Nat ; 1+ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus zero n = n
plus (1+ m) n = 1+ (plus m n)

{-# BUILTIN NATURAL  Nat  #-}
{-# BUILTIN ZERO     zero #-}
{-# BUILTIN SUC      1+ #-}

data Fin : Nat -> Set where
  fz : {n : Nat} ->          Fin (1+ n)
  fs : {n : Nat} -> Fin n -> Fin (1+ n)

data Cont (n : Nat) : Set where
  _◁_ : (S : Set) -> (P : S -> Fin n -> Set) -> Cont n

sh : {n : Nat} -> Cont n -> Set
sh (S ◁ P) = S

po : {n : Nat} -> (C : Cont n) -> sh C -> Fin n -> Set
po (S ◁ P) = P

data ⟦_⟧ {n : Nat} (C : Cont n) (X : Fin n -> Set) : Set where
  ext : (s : sh C) -> (f : (i : Fin n) -> (p : (po C) s i) -> X i) -> ⟦ C ⟧ X

con : {n : Nat} {C : Cont n} {X : Fin n -> Set} -> ⟦ C ⟧ X -> (sh C)
con (ext s f) = s

pay : {n : Nat} {C : Cont n} {X : Fin n -> Set} -> 
        (v : ⟦ C ⟧ X) -> (i : Fin n) -> (p : (po C) (con v) i) -> X i
pay (ext s f) = f

cmap : {n : Nat} {C : Cont n} {X Y : Fin n -> Set} ->
         (f : (i : Fin n) -> X i -> Y i) -> ⟦ C ⟧ X -> ⟦ C ⟧ Y
cmap f (ext s g) = ext s (\i p -> f i (g i p))

_:>_ : {n : Nat} (X : Set) -> (Y : Fin n -> Set) -> Fin (1+ n) -> Set
(_:>_) X Y fz = X
(_:>_) X Y (fs i) = Y i 

|ε| : Fin 0 -> Set
|ε| ()

_:m>_ : {n : Nat} {X Y : Set} {X' Y' : Fin n -> Set} ->  
          (f : X -> Y) -> (g : (i : Fin n) -> X' i -> Y' i) ->
            (i : Fin (1+ n)) -> (X :> X') i -> (Y :> Y') i
(_:m>_) f g fz x = f x
(_:m>_) f g (fs i) x' = g i x'

CZero : {n : Nat} -> Cont n  
CZero = Zero ◁ (\s i -> Zero) 

COne : {n : Nat} -> Cont n
COne = One ◁ (\s i -> Zero)
 
unit : {n : Nat} -> {X : Fin n -> Set} ->  ⟦ COne ⟧ X
unit = ext <> (\i p -> p Ψ)  

CVar : {n : Nat} -> (i : Fin n) -> Cont n
CVar {n} i = One ◁ (\s j -> Eq (Fin n) i j)

valp : {n : Nat} -> {i : Fin n} -> {X : Fin n -> Set} -> X i -> (j : Fin n) -> 
         Eq (Fin n) i j -> X j
valp {i = i} x .i refl = x

val : {n : Nat} -> {i : Fin n} -> {X : Fin n -> Set} -> X i -> ⟦ CVar i ⟧ X
val x = ext <> (valp x) 

CPlus : {n : Nat} -> (A B : Cont n) -> Cont n
CPlus C D = ((sh C) + (sh D)) ◁ (po C ∇ po D)

inl : {n : Nat} {A B : Cont n} {X : Fin n -> Set} -> ⟦ A ⟧ X -> ⟦ CPlus A B ⟧ X
inl (ext s f) = (ext (left s) f)
 
inr : {n : Nat} {A B : Cont n} {X : Fin n -> Set} -> ⟦ B ⟧ X -> ⟦ CPlus A B ⟧ X
inr (ext t g) = (ext (right t) g)

CTimes : {n : Nat} -> (A B : Cont n) -> Cont n
CTimes C D = ((sh C) × (sh D)) ◁ (\st i -> (po C (fst st) i) + (po D (snd st) i))

pair : {n : Nat} {A B : Cont n} {X : Fin n -> Set} -> 
         ⟦ A ⟧ X -> ⟦ B ⟧ X -> ⟦ CTimes A B ⟧ X
pair (ext s f) (ext t g) = 
  ext (tup s t) (\i -> (f i) ∇ (g i))

CArr : {n : Nat} -> (K : Set) -> (C : Cont n) -> Cont n
CArr K C = (K -> (sh C)) ◁ (\sf i -> Sig (\(k : K) -> po C (sf k) i))

fun : {n : Nat} {K : Set} {C : Cont n} {X : Fin n -> Set} ->
        (K -> ⟦ C ⟧ X) -> ⟦ CArr K C ⟧ X
fun f = 
  ext (\k -> con (f k)) (\i kp -> pay (f (fst kp)) i (snd kp))

data W (S : Set) (P : S -> Set) : Set where
  sup : (s : S) -> (P s -> W S P) -> W S P 

wπ₀ : forall {S P} -> W S P -> S
wπ₀ (sup s _) = s

wπ₁ : forall {S P} -> (w : W S P) -> P (wπ₀ w) -> W S P
wπ₁ (sup _ f) = f

wrec : {S : Set} {P : S -> Set} (R : W S P -> Set) 
         (h : (s : S) -> (f : P s -> W S P) -> 
                (g : (p : P s) -> R (f p)) -> R (sup s f)) ->
           (w : W S P) -> R w
wrec {S} {P} R h (sup s f) = h s f (\p -> wrec R h (f p) )


data Path {n : Nat} {S : Set} {P : S -> Set} (Q : S -> Fin n -> Set) :
         W S P -> Fin n -> Set where 
  here : forall {w i} -> Q (wπ₀ w) i -> Path Q w i 
  there : forall {w i} -> (p : P (wπ₀ w)) -> Path Q (wπ₁ w p) i -> Path Q w i  

CMu : {n : Nat} -> Cont (1+ n) -> Cont n
CMu C = (W S (\s -> P s fz)) ◁ (Path (\s i -> P s (fs i)))
  where S = sh C
        P = po C


muin : {n : Nat} {C : Cont (1+ n)} {X : Fin n -> Set} -> 
         ⟦ C ⟧ ((⟦ CMu C ⟧ X) :> X) -> ⟦ CMu C ⟧ X
muin {n} {C} {X} (ext s f) = ext s' f'        
  where s' : sh (CMu C)
        s' = sup s (\p -> con (f fz p)) 
        f' : (i : Fin n) (p : po (CMu C) s' i) -> X i
        f' i (here q) = f (fs i) q 
        f' i (there p r) =  pay (f fz p) i r 

fold : {n : Nat} {C : Cont (1+ n)} {X : Fin n -> Set} {Y : Set} ->
          (⟦ C ⟧ (Y :> X) -> Y) -> ⟦ CMu C ⟧ X -> Y
fold {n} {C} {X} {Y} α v = wrec R h (con v) (pay v) 
  where 
    S : Set
    S = sh C
    P : S -> Set
    P = \s -> (po C) s fz
    Q : sh C -> Fin n -> Set
    Q = \s i -> (po C) s (fs i)
    R = \w -> ((i : Fin n) -> Path {P = P} Q w i -> X i) -> Y 
    h : (s : S) (f : P s -> W S P)
         (g : (p : P s) -> ((i : Fin n) -> Path {P = P} Q (f p) i -> X i) -> Y)
          (m : (i : Fin n) -> Path {P = P} Q (sup s f) i -> X i) -> Y
    h s f g m = α (ext s f' )
      where
        f' : (i : Fin (1+ n)) (p : po C s i) -> (Y :> X) i
        f' fz p = g p  (\i q -> m i (there p q))  
        f' (fs i') q = m i' (here q) 

codata M (S : Set) (P : S -> Set) : Set where
  sup : (s : S) -> (P s -> M S P) -> M S P 

mπ₀ : forall {S P} -> M S P -> S
mπ₀ (sup s _) = s

mπ₁ : forall {S P} -> (m : M S P) -> P (mπ₀ m) -> M S P
mπ₁ (sup _ f) = f


mcorec : {S : Set} {P : S -> Set} (R : Set) -> (Q : M S P -> Set) ->
           (R -> Sig2 (\(s : S) (f : P s -> R) -> One)) -> 
             R -> Sig (\(m : M S P) -> Q m)
mcorec R Q h r with h r
...          | t ~ record {
  fst = (sup (fst₂ t) (\p -> fst (mcorec R Q h (snd₂ t p))));
  snd = {! !} }

data MPath {n : Nat} {S : Set} {P : S -> Set} (Q : S -> Fin n -> Set) :
         M S P -> Fin n -> Set where 
  here : forall {m i} -> Q (mπ₀ m) i -> MPath Q m i 
  there : forall {m i} -> (p : P (mπ₀ m)) -> MPath Q (mπ₁ m p) i -> MPath Q m i  
CNu : {n : Nat} -> Cont (1+ n) -> Cont n
CNu C = (M S (\s -> P s fz)) ◁ (MPath (\s i -> P s (fs i)))
  where S = sh C
        P = po C

nuout : {n : Nat} {C : Cont (1+ n)} {X : Fin n -> Set} -> 
         ⟦ CNu C ⟧ X -> ⟦ C ⟧ ((⟦ CNu C ⟧ X) :> X)
nuout {n} {C} {X} (ext s f) = ext s' f'  
  where s' = mπ₀ s
        f' : (i : Fin (1+ n)) (p : po C s' i) -> ((⟦ CNu C ⟧ X) :> X) i
        f' fz p = ext (mπ₁ s p) (\i r -> f i (there p r)) 
        f' (fs i') q = f i' (here q)  

unfold : {n : Nat} {C : Cont (1+ n)} {X : Fin n -> Set} {Y : Set} ->
          (Y -> ⟦ C ⟧ (Y :> X)) -> Y -> ⟦ CMu C ⟧ X 
unfold {n} {C} {X} {Y} α y = {! !} 

data C : Nat -> Set where
 ⊥   : {n : Nat}               -> C n
 ⊤   : {n : Nat}               -> C n
 !   : {n : Nat} -> Fin n      -> C n
 _⊕_ : {n : Nat} -> C n -> C n -> C n
 _⊗_ : {n : Nat} -> C n -> C n -> C n
 _→_ : {n : Nat} -> Set -> C n -> C n
 μ   : {n : Nat} -> C (1+ n)   -> C n 

eval : {n : Nat} -> C n -> Cont n
eval ⊥ = CZero 
eval ⊤ = COne  
eval (! y) = CVar y 
eval (y ⊕ y') = CPlus (eval y) (eval y') 
eval (y ⊗ y') = CTimes (eval y) (eval y') 
eval (y → y') = CArr y (eval y') 
eval (μ y) = CMu (eval y)  

data List (A : Set) : Set where
  ε : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
ε ++ as = as
(a :: as) ++ bs = a :: (as ++ bs)

data Bool : Set where
  tt : Bool
  ff : Bool

CList'' : Bool -> Fin 2 -> Set
CList'' tt i = Zero 
CList'' ff i = One

CList' : Cont 2
CList' = Bool ◁ CList''

CList : Cont 1 
CList = CMu CList'

List' : Set -> Set
List' A = ⟦ CList ⟧ (A :> |ε|)

cons' : {A : Set} -> A -> (List' A) -> (i : Fin 2) -> One -> 
          ((List' A) :> (A :> |ε|)) i
cons' a as fz _ = as
cons' a as (fs fz) _  = a
cons' a as (fs (fs ())) _ 

nil : {A : Set} -> List' A
nil = muin {C = CList'} (ext tt (\i p -> p Ψ))

cons : {A : Set} -> A -> List' A -> List' A
cons a as = muin {C = CList'} (ext ff (cons' a as))

l2cl : {A : Set} -> List A -> List' A
l2cl ε = nil
l2cl (a :: as) = cons a (l2cl as)

CList''' : C 1
CList''' = μ (⊤ ⊕ (! (fs fz) ⊗ (! fz)))

List'' : Set -> Set
List'' A = ⟦ eval CList''' ⟧ (A :> |ε|)

genListalg : {A B : Set} -> B -> (A -> B -> B) -> ⟦ CList' ⟧ (B :> (A :> |ε|))
               -> B
genListalg n c (ext tt _) = n
genListalg n c (ext ff f) = c (f (fs fz) <>) (f fz <>)

sumalg : ⟦ CList' ⟧ (Nat :> (Nat :> |ε|)) -> Nat
sumalg = genListalg 0 plus 

appendalg : {A : Set} -> List' A -> 
              ⟦ CList' ⟧ ((List' A) :> (A :> |ε|)) -> 
                List' A
appendalg as = genListalg  as cons

cappend : {A : Set} -> List' A -> List' A 
            -> List' A
cappend as bs = fold (appendalg bs) as

cl2l : {A : Set} -> List' A -> List A
cl2l = fold (genListalg ε (_::_))

revalg : {A : Set} -> 
  ⟦ CList' ⟧ ((List' A -> List' A) :> (A :> |ε|)) ->
   List' A -> List' A
revalg = genListalg (\x -> x) (\a f as -> f (cons a as))

CTree'' : Bool -> Fin 2 -> Set
CTree'' tt fz = Zero
CTree'' tt (fs fz) = One
CTree'' tt (fs (fs ())) 
CTree'' ff fz = Bool
CTree'' ff (fs fz) = Zero
CTree'' ff (fs (fs ())) 

CTree' : Cont 2
CTree' = Bool ◁ CTree''

CTree : Cont 1 
CTree = CMu CTree'

leaf' : {A : Set} -> A -> (i : Fin 2) -> CTree'' tt i -> 
          ((⟦ CTree ⟧ (A :> |ε|)) :> (A :> |ε|)) i
leaf' a fz () 
leaf' a (fs fz) _ = a  
leaf' a (fs (fs ())) _ 
leaf : {A : Set} -> A -> ⟦ CTree ⟧ (A :> |ε|)
leaf a  = muin {C = CTree'} (ext tt (leaf' a))

node' : {A : Set} -> ⟦ CTree ⟧ (A :> |ε|) -> ⟦ CTree ⟧ (A :> |ε|) -> 
         (i : Fin 2) -> CTree'' ff i -> ((⟦ CTree ⟧ (A :> |ε|)) :> (A :> |ε|)) i
node' l r fz ff = l
node' l r fz tt = r
node' l r (fs fz) () 
node' l r (fs (fs ())) _  

node : {A : Set} -> ⟦ CTree ⟧ (A :> |ε|) -> ⟦ CTree ⟧ (A :> |ε|) -> 
         ⟦ CTree ⟧ (A :> |ε|)
node l r = muin {C = CTree'} (ext ff (node' l r))

genTreealg : {A B : Set} -> (A -> B) -> (B -> B -> B) -> 
               ⟦ CTree' ⟧ (B :> (A :> |ε|)) -> B
genTreealg l n (ext tt f) = l (f (fs fz) <>) 
genTreealg l n (ext ff f) = n (f fz ff) (f fz tt)

sumTreealg : ⟦ CTree' ⟧ (Nat :> (Nat :> |ε|)) -> Nat
sumTreealg = genTreealg (\x -> x) plus

flatTreealg : {A : Set} -> ⟦ CTree' ⟧ (List A :> (A :> |ε|)) -> List A
flatTreealg = genTreealg (\x -> x :: ε) (_++_)

cflatTreealg : {A : Set} -> ⟦ CTree' ⟧ ((List' A) :> (A :> |ε|)) -> List' A
cflatTreealg = genTreealg (\x -> cons x nil) cappend 

