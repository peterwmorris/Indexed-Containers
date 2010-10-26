module Utils where
    {- Fixing some terrible name decisions in the Std. Lib. -}

  open import Data.Product

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