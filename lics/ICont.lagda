%include agda.fmt

%format \ = "\lambda"
%format Sig = "\Sigma"
%format <   = "\lhd" 
%format _<_   = "\_\lhd\_" 
%format ==ext = "\equiv"ext

%if style == newcode
\begin{code}

  {-# OPTIONS --no-termination-check
  #-}

module ICont where

data _==_ {A : Set} (a : A) : {B : Set} -> B -> Set where
  refl : a == a

postulate ==ext : {A : Set} {B : A -> Set} {C : (a : A) -> B a -> Set} ->
                 {f g : (a : A) -> (b : B a) -> C a b} ->
                 ((a : A) -> (b : B a) -> f a b == g a b) -> f == g  

resp2 : {A : Set} {B C : A -> Set} (f : (a : A) -> (b : B a) -> C a)
        {a  : A} -> {b b' : B a} -> (b == b') ->
        (f a b) == (f a b')
resp2 f refl = refl

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B 



data Sig (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> (b : B a) -> Sig A B

SigEq : {A : Set} {B : A -> Set}
        {a a' : A} -> (p : a == a') -> {b : B a} -> {b' : B a'} -> (b == b') ->
        _==_ {Sig A B} (a , b) {Sig A B} (a' , b')
SigEq refl refl = refl

\end{code}
%endif

We begin by defining |Cont|:

\begin{code}

data Cont (I : Set) : Set1 where
  _<_ : (S : Set) -> (P : S -> I -> Set) -> Cont I

sh : {I : Set} -> Cont I -> Set
sh (S < P) = S

po : {I : Set} -> (C : Cont I) -> sh C -> I -> Set
po (S < P) = P

ICont : Set -> Set -> Set1
ICont I O = O -> Cont I

\end{code}

It will be useful to view |ICont|, as |O|-indexed shapes and positions, rather than being an |O|-indexed |Cont|:

\begin{code}

data ICont* (I O : Set) : Set1 where
  _<_ : (S : O -> Set) -> (P : (o : O) -> S o -> I -> Set) -> ICont* I O

ic* : {I O : Set} -> ICont I O -> ICont* I O
ic* C = (\ o -> sh (C o)) < \ o -> po (C o)

*ic : {I O : Set} -> ICont* I O -> ICont I O
*ic (S < P) o = S o < P o 

\end{code}

Similarly we define this view which allows us to see a |Cont (I + J)| as having 2 sets of positions:

%format sh+ = sh
%format po+0 = po"^I" 
%format po+1 = po"^J" 
%format P0 = P"^I" 
%format P1 = P"^J" 

\begin{code}

data Cont+ (I J : Set) : Set1 where
  _<_,_ : (S : Set) -> (P : S -> I -> Set) -> 
                       (Q : S -> J -> Set) -> Cont+ I J

sh+ : {I J : Set} -> Cont+ I J -> Set
sh+ (S < P , Q) = S

po+0 : {I J : Set} -> (C : Cont+ I J) -> (sh+ C) -> I -> Set
po+0 (S < P , Q) = P

po+1 : {I J : Set} -> (C : Cont+ I J) -> (sh+ C) -> J -> Set
po+1 (S < P , Q) = Q

c+ : {I J : Set} -> Cont (I + J) -> Cont+ I J
c+ (S < P) = S < (\ s i -> P s (inl i)) , (\ s j -> P s (inr j))

ICont+ : Set -> Set -> Set -> Set1
ICont+ I J O = O -> Cont+ I J

data ICont+* (I J O : Set) : Set1 where
  _<_,_ : (S : O -> Set) -> (P : (o : O) -> S o -> I -> Set) -> 
                            (Q : (o : O) -> S o -> J -> Set) -> ICont+* I J O

ic+* : {I J O : Set} -> ICont+ I J O -> ICont+* I J O 
ic+* C = (\o -> sh+ (C o)) < (\ o -> po+0 (C o)) , \ o -> po+1 (C o)

\end{code}

\pagebreak

Morphisms in |Cont I|:

%format => = "\Rightarrow"
%format o = "\cdot"
%format _=>_ = "\_\Rightarrow\_"
%format _o_ = "\_\cdot\_"

\begin{code}

data _=>_ {I : Set} (C D : Cont I) : Set where
  _<_ :  (f : sh C -> sh D) -> 
         (r : (s : sh C) -> (i : I) -> po D (f s) i -> po C s i) -> C => D

shf : {I : Set} -> {C D : Cont I} -> C => D -> sh C -> sh D
shf (f < r) = f

pof :  {I : Set} -> {C D : Cont I} -> (m : C => D) -> (s : sh C) -> (i : I) -> 
       (po D) (shf m s) i -> (po C) s i
pof (f < r) = r

_o_ : {I : Set} {C D E : Cont I} -> (f : D => E) -> (g : C => D) -> C => E
(a < c) o (b < d) = (\ s -> a (b s)) < \ s i r -> d s i (c (b s) i r)

\end{code}

Morphisms in |ICont I J|:

%format =>* = "\Rightarrow^*"
%format _=>*_ = "\_\Rightarrow^*\_"

\begin{code}

data _=>*_ {I J : Set} (C D : ICont I J) : Set where
  _<_ :  (f : (j : J) -> sh (C j) -> sh (D j)) -> 
         (r :  (j : J) (s : sh (C j)) -> 
               (i : I) -> po (D j) (f j s) i -> po (C j) s i) -> 
         C =>* D 

m* : {I J : Set} -> {C D : ICont I J} -> 
     ((j : J) -> C j => D j) -> C =>* D
m* {_} {_} {C} {D} m  with ic* C | ic* D 
m* {_} {_} {C} {D} m | (S < P) | (T < Q) = (\ j -> shf (m j)) < \ j -> pof (m j)

*m :  {I J : Set} -> {C D : ICont I J} -> 
      (C =>* D) -> ((j : J) -> C j => D j) 
*m {_} {_} {C} {D} (f < r) = (\ j -> f j < r j) 


\end{code}

Give rise to functors, we do not prove the laws here, because we do not need them:

%format left = "\llbracket"
%format right = "\rrbracket"

\begin{code}
 

left_right : {I : Set} -> Cont I -> (I -> Set) -> Set
left_right {I} C T = Sig (sh C) (\ s -> (i : I) -> po C s i -> T i) 

_$_ :  {I : Set} -> {C D : Cont I} -> (m : C => D) -> {X : I -> Set} -> 
       left C right X -> left D right X
_$_ {_} (a < b) (s , f) = a s , \ i q -> f i (b s i q)  

\end{code}

Before we define the least fixed point we define partial application. We begin by defining the functor |U|:

\begin{code}

U : {I J : Set} -> Cont (I + J) -> (J -> Set) -> Set
U C T = left (sh C) < (\ s j -> po C s (inr j)) right T 

mapU :  {I J : Set} -> (C : Cont (I + J)) -> {T T' : J -> Set} -> 
        (f : (j : J) -> T j -> T' j) -> U C T -> U C T'
mapU C f (s , g) = s , \ j p -> f j (g j p)      

\end{code}

\pagebreak

And the indexed functor |R|:

\begin{code}

R :  {I J : Set} -> (C : Cont (I + J)) -> {T : J -> Set} -> 
     (Q : (j : J) -> T j -> I -> Set) -> U C T -> I -> Set
R {_} {J} C Q (s , f) i =
     po C s (inl i)
  +  Sig J (\ j -> Sig (po C s (inr j)) (\ p -> Q j (f j p) i)) 

mapR :  {I J : Set} -> (C : Cont (I + J)) -> {T : J -> Set} -> 
        {Q Q' : (j : J) -> T j -> I -> Set}
        (f : (j : J) (t : T j) (i : I) -> Q j t i -> Q' j t i) -> 
        (u : U C T) (i : I) -> R C Q u i -> R C Q' u i
mapR C f (s , g) i (inl p)              = inl p
mapR C f (s , g) i (inr (j , (p , q)))  = inr (j , (p , f j (g j p) i q)) 

\end{code}

Again, we do not need to prove the functor laws for |U| and |R| but it would be possible in an extensional style.

We will need this relationship between |U| and |R|:

%format phi = "\phi"

\begin{code}

phi :  {I J : Set} (C : Cont (I + J)) {T T' : J -> Set} 
       (f : (j : J) -> T j -> T' j) 
       (Q' : (j : J) -> T' j -> I -> Set) (u : U C T) (i : I) ->
       R C Q' (mapU C f u) i -> R C (\ j' t i' -> Q' j' (f j' t) i') u i
phi C f Q' (a , b) i x = x

\end{code}

We now define the partial application of a |Cont (I + J)| to an |ICont I J|, which gives rise to a functor:

\begin{code}

_[_] : {I J : Set} -> (C : Cont (I + J)) -> (D : ICont I J) -> Cont I 
C [ D ]  with ic* D
C [ D ]  | (T < Q) = U C T < R C Q

map[] :  {I J : Set} (C : Cont (I + J)) -> {D D' : ICont I J} -> 
         ((j : J) -> D j => D' j) -> C [ D ] => C [ D' ]
map[] C {D} {D'} m  with m* m
map[] C {D} {D'} m  | (f < r) = 
  mapU C f < \ u i x -> mapR C r u i (phi C f (\ j -> po (D' j)) u i x)  

\end{code}
  
We can begin the construction of the least fixed point. The shapes inductive containers will be given by |W|-Types, here the constructor |sup| takes advantage of the functor |U|:

%format U* = U"^{\mu}"

\begin{code}

data W {I J : Set} (C : ICont (I + J) J) (j : J) : Set where
  sup : U (C j) (W C) -> W C j

foldW :  {I J : Set} (C : ICont (I + J) J) (D : J -> Set) -> 
         ((j : J) -> U (C j) D -> D j) -> (j : J) -> W C j -> D j
foldW C D m j (sup u) = m j (mapU (C j) (foldW C D m) u) 

\end{code}

Note that |U*| from the paper is simply defined as |W|.

The postions will then be given by paths through such a tree, again we take advatage of the functor |R|.

%format R* = R"^{\mu}"

\begin{code}

R* : {I J : Set} -> (C : ICont (I + J) J) -> (j : J) -> W C j -> I -> Set
R* C j (sup u) i = R (C j) (R* C) u i

\end{code}

Note that this definition is not structurally recursive, it is however terminating on the size of the |W|-type.

The fixed point of an |ICont (I + J) J| is an |ICont I J|: 

%format mu = "\mu"

\begin{code}

mu : {I J : Set} -> (F : ICont (I + J) J) -> ICont I J
mu F j = W F j < R* F j   

\end{code}

\pagebreak

The algebra contains a morphism from |F [ mu F ]| to |mu F|, given by:

%format inmu = "\Varid{in}\mu"

\begin{code}

inmu : {I J : Set} (F : ICont (I + J) J) -> (j : J) -> (F j) [ mu F ] => mu F j
inmu F j  with ic+* (\j -> c+ (F j))
inmu F j  | (S < P0 , P1) = sup <  \ _ _ r -> r 

\end{code}

And the associated fold by:

%format foldmu = fold"\mu"
%format foldmusq = fold"\mu\square"

\begin{code}

foldmu :  {I J : Set} -> (F : ICont (I + J) J) -> (H : ICont I J) -> 
          ((j : J) -> (F j) [ H ] => H j) -> (j : J) -> mu F j => H j
foldmu {I} {J} F H m  with m* m
foldmu {I} {J} F H m  | (a < b) = *m (foldW F  (\ j -> sh (H j)) a < d)  
  where  d :  (j : J) (w : W F j) (i : I) -> 
              po (H j) (foldW F (\ j -> sh (H j)) a j w) i -> R* F j w i
         d j (sup (s , f)) i q = mapR (F j) d (s , f) i (b j _ i q) 

\end{code}

We show that the fold square commutes by observation on the action of the 
container functor. 

\begin{code}

foldmusq :  {I J : Set} (F : ICont (I + J) J) (H : ICont I J) 
            (m : (j : J) -> (F j) [ H ] => H j) -> {X : I -> Set}
            (j : J) -> (x : left (F j) [ mu F ] right X) ->
                (((m j) o (map[] (F j) (foldmu F H m))) $ x) 
            ==  (((foldmu F H m j) o (inmu F j)) $ x)
foldmusq F H m j ((s , f) , g)  with m j
foldmusq F H m j ((s , f) , g)  | (a < b) = SigEq refl (==ext (\ x y -> refl)) 


\end{code}
