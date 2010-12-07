
{-# OPTIONS --universe-polymorphism #-}

module IFunc where

open import Level
open import Function
open import HeterogeneousEquality 
open import Isomorphism

open import Data.Product

_⟶_ : ∀ {l} {I : Set l} (A B : I → Set l) → Set l
_⟶_ {_} {I} A B = {i : I} → A i → B i

_⊚_ : ∀ {l} {I : Set l} {A B C : I → Set l} → (B ⟶ C) → (A ⟶ B) → A ⟶ C
_⊚_ f g {i} = f {i} ∘ g {i}


record IFunc {l : Level} (I : Set l) : Set (suc l) where
  constructor ifunc
  field
    obj : (I → Set l) → Set l
    mor : {A B : I → Set l} → (A ⟶ B) → obj A → obj B 
    idlaw : {A : I → Set l} → id {_} {obj A} ≅ mor {A} {A} id 
    complaw : {A B C : I → Set l} (f : B ⟶ C) (g : A ⟶ B) →
                (mor {B} {C}) f ∘ (mor {A} {B} g) ≅
                  mor {A} {C} (_⊚_ {B = B} f g) 

record NatTrans {l : Level} {I : Set l} (F G : IFunc I) : Set (suc l) where
  constructor nattrans
  field 
    fun : {A : I → Set l} → IFunc.obj F A → IFunc.obj G A
    law : {A B : I → Set l} {f : A ⟶ B} → 
            fun {B} ∘ (IFunc.mor F f) ≅ IFunc.mor G f ∘ (fun {A})
 
record _≅^F_ {l : Level} {I : Set l} (F G : IFunc I) : Set (suc l) where
  field 
    fiso : {A : I → Set l} → IFunc.obj F A ≈ IFunc.obj G A 
    law1 :  {A B : I → Set l} {f : A ⟶ B} → 
              _≈_.φ (fiso {B}) ∘ (IFunc.mor F f) ≅ IFunc.mor G f ∘ (_≈_.φ (fiso {A}))
    law2 : {A B : I → Set l} {f : A ⟶ B} → 
              _≈_.ψ (fiso {B}) ∘ (IFunc.mor G f) ≅ IFunc.mor F f ∘ (_≈_.ψ (fiso {A}))

IFunc* : {l : Level} (I J : Set l) → Set (suc l) 
IFunc* I J = J → IFunc I

Δ^F : ∀ {l} {I J K : Set l} → (J → K) → IFunc* I K → IFunc* I J 
Δ^F f F = F ∘ f

Σ^F : ∀ {l} {J I K : Set l} → (J → K) → IFunc* I J → IFunc* I K
Σ^F {_} {J} f F k = ifunc (λ A → Σ J λ j → f j ≅ k × IFunc.obj (F j) A) (λ m → uncurry  (λ j → uncurry λ p x → j , p , IFunc.mor (F j) m  x)) (ext (uncurry λ j → uncurry λ p x → cong₂ _,_ refl (cong₂ _,_ refl (app≅ (IFunc.idlaw (F j)) x)))) (λ g h → ext (uncurry λ j → uncurry λ p x → cong₂ _,_ refl (cong₂ _,_ refl (app≅ (IFunc.complaw (F j) g h) x)))) 

{-
woah : ∀ {l} {I J K : Set l} (f : J → K) (F : IFunc* I J) (G : IFunc* I K) → ((k : K) → NatTrans (Σ^F f F k) (G k)) → (j : J) → NatTrans (F j) (Δ^F f G j)
woah f F G m j = nattrans (λ x → NatTrans.fun (m (f j)) (j , refl , x)) (ext (λ a → app≅ (NatTrans.law (m (f j))) (j , refl , a)))

haow : ∀ {l} {I J K : Set l} (f : J → K) (F : IFunc* I J) (G : IFunc* I K) → ((j : J) → NatTrans (F j) (Δ^F f G j)) →  (k : K) → NatTrans (Σ^F f F k) (G k)
haow f F G m k = nattrans (λ {A} → uncurry λ j → uncurry λ p x → subst (λ k → IFunc.obj (G k) A) p (NatTrans.fun (m j) x)) (λ {A} {B} {f} → ext (uncurry λ j → uncurry λ p x → trans (subst-removable (λ k → IFunc.obj (G k) B) p (NatTrans.fun (m j) (IFunc.mor (F j) f x))) (trans (app≅ (NatTrans.law  (m j)) x) (cong₂ (λ nu → IFunc.mor (G nu) {A} {B} f) p (sym (subst-removable (λ k' → IFunc.obj (G k') A) p (NatTrans.fun (m j) x)))))))
-}

Π^F : ∀ {l} {J I K : Set l} → (J → K) → IFunc* I J → IFunc* I K
Π^F {_} {J} f F k = ifunc (λ A → (j : J) → f j ≅ k → IFunc.obj (F j) A) (λ m f j p → IFunc.mor (F j) m (f j p)) (ext (λ f → ext (λ j → ext (λ p → app≅ (IFunc.idlaw (F j)) (f j p))))) (λ g h → ext (λ f → ext (λ j → ext (λ p → app≅ (IFunc.complaw (F j) g h) (f j p)))))

{-
woah : ∀ {l} {I J K : Set l} (f : J → K) (F : IFunc* I K) (G : IFunc* I J) → ((j : J) → NatTrans (Δ^F f F j) (G j)) → (k : K) → NatTrans (F k) (Π^F f G k)
woah {l} {I} {J} {K} f F G m k = nattrans (foo k) (ext (λ a → ext (λ a' → ext (λ a0 → bar k a a' a0)))) -- (λ {A} x j p → NatTrans.fun (m j) (subst (λ k' → IFunc.obj (F k') A) (sym p) x)) (λ {A} {B} {g} → ext (λ x → ext (λ j → ext (λ p → trans (cong (NatTrans.fun (m j)) {!!}) (app≅ (NatTrans.law (m j)) (subst (λ k' → IFunc.obj (F k') A) (sym p) x)))))) 
  where foo : {A : I → Set l} → (k : K) → IFunc.obj (F k) A → (j : J) → f j ≅ k → IFunc.obj (G j) A
        foo .(f j) x j refl = NatTrans.fun (m j) x
        bar : {A B : I → Set l} {f' : {i : I} → A i → B i} (k : K) (x : IFunc.obj (F k) A) (j : J) (p : f j ≅ k) → foo k (IFunc.mor (F k) f' x) j p ≅ (IFunc.mor (G j) f' (foo k x j p))
        bar .(f j) x j refl = app≅ (NatTrans.law (m j)) x
-}

haow : ∀ {l} {I J K : Set l} (f : J → K) (F : IFunc* I K) (G : IFunc* I J) → ((k : K) → NatTrans (F k) (Π^F f G k)) →  (j : J) → NatTrans (Δ^F f F j) (G j)
haow f F G m j = nattrans (λ x → NatTrans.fun (m (f j)) x j refl) (ext (λ a → app≅ (app≅ (app≅ (NatTrans.law (m (f j))) a) j) refl))