module Containers where

data Zero : Set where

_Ψ : Zero -> {S : Set} -> S
() Ψ   

record One : Set where

<> : One
<> = record {}

record Sig {S : Set} (T : S -> Set) : Set where
  field fst : S
  field snd : T fst

open module Sig' {S : Set} {T : S -> Set} =
              Sig {S}{T}

tup : {S : Set} {T : S -> Set} -> 
        (s : S) -> (T s) -> Sig T
tup s t = record {fst = s;
                  snd = t}

_*_ : (A B : Set) -> Set
A * B = Sig (\(a : A) -> B)

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

_|+₁|_ : {A B : Set} {C : Set1} -> (f : A -> C) -> (g : B -> C) -> A + B -> C
(f |+₁| g) (left a) = f a
(f |+₁| g) (right b) = g b

_|+|_ : {A B : Set} {C : Set} -> (f : A -> C) -> (g : B -> C) -> A + B -> C
(f |+| g) (left a) = f a
(f |+| g) (right b) = g b 

data Eq {X : Set} (a : X) : {Y : Set} -> (b : Y) -> Set where
  refl : Eq {X} a {X} a

trans : {X Y Z : Set} {a : X} {b : Y} {c : Z} -> Eq a b -> Eq b c -> Eq a c
trans refl refl = refl

resp : {S T : Set} (f : S -> T) -> {s s' : S} -> Eq s s' -> Eq (f s) (f s')
resp f refl = refl

data EqTy : Set -> Set -> Set1 where
  reflTy : {X : Set} -> EqTy X X

respTy : {S : Set} (P : S -> Set) -> {s s' : S} -> Eq s s' -> EqTy (P s) (P s')
respTy P refl = reflTy

coerce : {X Y : Set} -> EqTy X Y -> X -> Y
coerce reflTy x = x

data Nat : Set where zero : Nat ; 1+ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus zero n = n
plus (1+ m) n = 1+ (plus m n)

{-# BUILTIN NATURAL  Nat  #-}
{-# BUILTIN ZERO     zero #-}
{-# BUILTIN SUC      1+   #-}

data Bool : Set where
  tt : Bool
  ff : Bool

data Fin : Nat -> Set where
  fz : {n : Nat} ->          Fin (1+ n)
  fs : {n : Nat} -> Fin n -> Fin (1+ n)

So : Bool -> Set
So tt = One
So ff = Zero

data Cont : Set1 where
  _◃_ : (S : Set) -> (P : S -> Set) -> Cont 

sh : Cont -> Set
sh (S ◃ P) = S

po : (C : Cont) -> sh C -> Set
po (S ◃ P) = P

data ⟦_⟧ (C : Cont) (X : Set) : Set where
  ext : (s : sh C) -> (f : ((po C) s) -> X) -> ⟦ C ⟧ X


con : {C : Cont} {X : Set} -> ⟦ C ⟧ X -> (sh C)
con {C = (S ◃ P)} (ext s f) = s

pay : {C : Cont} {X : Set} -> 
        (v : ⟦ C ⟧ X) -> (p : (po C) (con v)) -> X
pay {C = (S ◃ P)} (ext s f) = f

data _=ext=_ {C : Cont} {X : Set} (e e' : ⟦ C ⟧ X) : Set where
  extEq : (sheq : Eq (con e) (con e')) -> 
            ((p : (po C) (con e)) -> 
              Eq (pay e p) (pay e' (coerce (respTy (po C) sheq) p)))
              -> e =ext= e'

reflext : {C : Cont} {X : Set} {e : ⟦ C ⟧ X} -> e =ext= e
reflext = extEq refl (\p -> refl)

transext : {C : Cont} {X : Set} {e e' e'' : ⟦ C ⟧ X} ->
             e =ext= e' -> e' =ext= e'' -> e =ext= e'' 
transext {C = S ◃ P} {e = ext s f} {e' = ext .s f'} {e'' = ext .s f''}
  (extEq refl q) (extEq refl q') = extEq refl (\p -> trans (q p) (q' p))



cmap : {C : Cont} {X Y : Set} ->
         (f : X -> Y) -> ⟦ C ⟧ X -> ⟦ C ⟧ Y
cmap {C = S ◃ P} f (ext s g) = ext s (\p -> f (g p))

respmap : {C : Cont} {X Y : Set} (f : X -> Y) -> {e e' : ⟦ C ⟧ X}
            -> e =ext= e' -> cmap f e =ext= cmap f e'
respmap {C = S ◃ P} f {ext s g} {ext .s g'} (extEq refl q) = 
  extEq refl (\p -> resp f (q p))

respext : {C D : Cont} {X : Set} (α : {Y : Set} -> ⟦ C ⟧ Y -> ⟦ D ⟧ Y) ->
            {e e' : ⟦ C ⟧ X} -> (Eq e e') -> α e =ext= α e'
respext {C = S ◃ P} {D = T ◃ Q} α refl = reflext 

data CMorph (C D : Cont) : Set where
  cmorph : (sf : (sh C) -> (sh D)) -> 
             ((cs : (sh C)) -> (po D) (sf cs) -> ((po C) cs)) -> CMorph C D 

_$_ : {C D : Cont} {X : Set} (m : CMorph C D) -> ⟦ C ⟧ X -> ⟦ D ⟧ X
(_$_) {C = S ◃ P} {D = T ◃ Q} (cmorph sf pf) (ext s f) = 
                                               ext (sf s) (\q -> f (pf s q))

data List (A : Set) : Set where
  ε : List A
  _::_ : A -> List A -> List A

CList : Cont
CList = Nat ◃ Fin

data Maybe (A : Set) : Set where
  No : Maybe A
  Yes : A -> Maybe A

CMaybe : Cont
CMaybe = Bool ◃ So

isSucc : Nat -> Bool
isSucc 0 = ff
isSucc (1+ n) = tt

neFin : (n : Nat) -> (So (isSucc n)) -> Fin n
neFin 0 () 
neFin (1+ n) v = fz

cheadm : CMorph CList CMaybe
cheadm = cmorph isSucc neFin

length : {A : Set} -> List A -> Nat
length ε = 0
length (A :: as) = 1+ (length as)

proj : {A : Set} -> (as : List A) -> Fin (length as) -> A
proj ε         ()  
proj (a :: as) fz = a
proj (a :: as) (fs i) = proj as i

list2clist : {A : Set} -> List A -> ⟦ CList ⟧ A
list2clist as = ext (length as) (proj as)

clist2list : {A : Set} -> ⟦ CList ⟧ A -> List A
clist2list (ext 0 _) = ε
clist2list (ext (1+ n) f) = (f fz) :: (clist2list (ext n (\i -> f (fs i))))

cmaybe2maybe : {A : Set} -> ⟦ CMaybe ⟧ A -> Maybe A
cmaybe2maybe (ext ff _) = No
cmaybe2maybe (ext tt f) = Yes (f <>)

max : {n : Nat} -> Fin (1+ n)
max {0} = fz
max {1+ n} = fs max

emb : {n : Nat} -> Fin n -> Fin (1+ n)
emb fz = fz
emb (fs i) = fs (emb i)

revfin : (n : Nat) -> Fin n -> Fin n
revfin ._ fz = max
revfin (1+ n) (fs i) = emb (revfin n i)

creversem : CMorph CList CList
creversem = cmorph (\n -> n) revfin

tricky : {C : Cont} -> (s : sh C) -> ⟦ C ⟧ ((po C) s)
tricky {C = S ◃ P} s = ext s (\p -> p)

quote : {C D : Cont} -> ({X : Set} -> (⟦ C ⟧ X) -> (⟦ D ⟧ X)) -> CMorph C D
quote {C = S ◃ P} {D = T ◃ Q} f = cmorph (\s -> con (trick s)) 
                                          (\s q -> pay (trick s) q)
  where
    trick = (\(s : S) -> f {P s} (tricky s))

quoter : {C D : Cont} -> ({X : Set} -> (⟦ C ⟧ X) -> (⟦ D ⟧ X)) -> {X : Set}
           (s : sh C) -> ⟦ D ⟧ ((po C) s)
quoter {C = S ◃ P} α s with quote α
...                    | cmorph u g = ext (u s) (g s)

trickster : {C : Cont} -> {X : Set} -> ⟦ C ⟧ X -> ⟦ C ⟧ X
trickster {C = S ◃ P} (ext s f) = cmap f (tricky s)

notrick : {C : Cont} -> {X : Set} -> (e : ⟦ C ⟧ X) -> e =ext= (trickster e)
notrick {C = S ◃ P} (ext s f) = reflext 

dia1 : {C D : Cont} -> (α : {X : Set} -> ⟦ C ⟧ X -> ⟦ D ⟧ X) -> (s : sh C) -> 
         (quoter α {po C s} s) =ext= (α {(po C) s} (tricky {C} s))
dia1 {C = S ◃ P} {D = T ◃ Q} α s = extEq refl (\q -> refl) 

dia2 : {C D : Cont} -> (α : {X : Set} -> ⟦ C ⟧ X -> ⟦ D ⟧ X) -> {X : Set} ->
         (e : ⟦ C ⟧ X) -> (α {X} (cmap (pay e) (tricky (con e)))) =ext=
                            (cmap (pay e) (α {(po C) (con e)} (tricky (con e))))
dia2 {C = S ◃ P} {D = T ◃ Q} α (ext s f) = 
  ? {- transext (notrick (ext s f)) (transext ? (respmap f (dia1 α s)))
-}


{-



(con (ext (con (α (ext s (\p -> p)))) (\p -> f (pay (α (ext s (\p' -> p'))) p))))



yonedash : {C D : Cont} -> (m : {X : Set} -> (⟦ C ⟧ X) -> (⟦ D ⟧ X)) -> 
    {X : Set} -> (e : ⟦ C ⟧ X) -> 
      Eq (con (m e)) (con ((quote m) $ e))
yonedash {C = S ◃ P} {D = T ◃ Q} m (ext s f) with  
... | ext x y = ? 
\
-}
