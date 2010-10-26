{-# OPTIONS --type-in-type 
  #-}
module spf where

open import Utils

mutual

  SPF : (I O : Set) -> Set
  SPF I O = O -> SPT I 

  data SPT : (I : Set) -> Set where
    ZeroU   : forall {I} -> SPT I
    UnitU   : forall {I} -> SPT I 
    Var     : forall {I}                         -> SPF I I
    ΣU      : forall {I O O'}  -> (O -> O')     
                               -> SPF I O        -> SPF I O'
    ΠU      : forall {I O O'}  -> (O -> O')
                               -> SPF I O        -> SPF I O'
    μU      : forall {I O}     -> SPF (I + O) O  -> SPF I O

ΔU : forall {I O O'}  -> (O' -> O) -> SPF I O -> SPF I O'
ΔU f As o' = As (f o')

_[_]U_  : forall {I J K}   -> SPF (I + J) K  
                           -> SPF I J        -> SPF I K
As [ Bs ]U k with As k
...          | ZeroU   = ZeroU
...          | UnitU   = UnitU
...          | Var (inl i)   =  Var i 
...          | Var (inr j)   =  Bs j 
...          | ΣU f As' i =  ΣU f (\ o ->  As' [ Bs ]U o) i 
...          | ΠU f As' i = ΠU f (\ o ->  As' [ Bs ]U o) i  
...          | μU As' i = μU ( \ o -> {! !} )  i 

