module WI where

open import Data.Product
open import Relation.Binary.PropositionalEquality

data W (S : Set)(P : S → Set) : Set where
  sup : (s : S) → (P s → W S P) → W S P

WRec : {S : Set}{P : S → Set} 
       → (M : W S P → Set)
       → ((s : S)(f : P s → W S P) 
       → ((p : P s) → M (f p)) → M (sup s f))
       → (w : W S P) → M w
WRec M m (sup s f) = m s f (λ p → WRec M m (f p))

ext' : {A : Set}{B : A → Set}{f g : (a : A) → B a}
      → f ≡ g
      → (a : A) → f a ≡ g a
ext' refl a = refl

postulate 
  ext : {A : Set}{B : A → Set}{f g : (a : A) → B a}
      → ((a : A) → f a ≡ g a)
      → f ≡ g
  
  extProp : {A : Set}{B : A → Set}{f g : (a : A) → B a}
          → (p : (a : A) → f a ≡ g a)
          → ext' (ext p) ≡ p

eqSup : ∀{S}{P : S → Set}{s : S}{f g : P s → W S P} → ((x : P s) → f x ≡ g x) → sup s f ≡ sup s g
eqSup p with ext p
eqSup p | refl = refl

supEq₀ : ∀{S}{P : S → Set}{s s' : S}{f : P s → W S P}{g : P s' → W S P} → sup s f ≡ sup s' g → s ≡ s'
supEq₀ refl = refl

supEq₁ : ∀{S}{P : S → Set}{s : S}{f g : P s → W S P} → sup s f ≡ sup s g → f ≡ g
supEq₁ refl = refl

^_ : ∀ {I}(S : I → Set) → Set
^_ {I} S = Σ I S

^^_ : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) → ^ S → Set
^^_ {I} {S} P (i , s) = Σ I (λ j → P i j s) 

{-
ideal : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
     → W (^ S) (^^ P) → I → W ((^ S) × I) (λ x → (^^ P) (proj₁ x))
ideal P (sup (j , s) f) i = sup ((j , s) , i) (λ x → ideal P (f x) (proj₁ x)) 

actual : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
     → W (^ S) (^^ P) → W ((^ S) × I) (λ x → (^^ P) (proj₁ x))
actual P (sup (i , s) f) = sup ((i , s) , i) (λ x → actual P (f x))
-}

ideal : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
     → W (^ S) (^^ P) → I → W (I × (^ S)) (λ x → (^^ P) (proj₂ x))
ideal P (sup (j , s) f) i = sup (i , (j , s)) (λ x → ideal P (f x) (proj₁ x)) 

actual : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
     → W (^ S) (^^ P) → W (I × (^ S)) (λ x → (^^ P) (proj₂ x))
actual P (sup (i , s) f) = sup (i , (i , s)) (λ x → actual P (f x))

WI₀ : {I : Set} (S : I → Set)(P : (i j : I) → S i → Set) → Set
WI₀ S P =  W (^ S) (^^ P)

WI₁ : {I : Set} (S : I → Set)(P : (i j : I) → S i → Set) → I → WI₀ S P → Set
WI₁ S P i w = ideal P w i ≡ actual P w

WI : {I : Set} (S : I → Set)(P : (i j : I) → S i → Set) → I → Set
WI S P i = Σ (WI₀ S P) (WI₁ S P i)

sup₀ : ∀ {I}{S : I → Set}{P : (i j : I) → S i → Set}
         (i : I)(s : S i)(f : {j : I} → P i j s → WI₀ S P) 
         → WI₀ S P
sup₀ i s f = sup (i , s) (λ x → f (proj₂ x))

sup₁ : ∀ {I}{S : I → Set}{P : (i j : I) → S i → Set}
         (i : I)(s : S i)(f : {j : I} → P i j s → WI₀ S P) 
         → ({j : I} → (p : P i j s) → WI₁ S P j (f p))
         → WI₁ S P i (sup₀ {I} {S} {P} i s f)
sup₁ i s f f' = eqSup (λ x → f' (proj₂ x))

lem1 : ∀ {I}{S : I → Set}{P : (i j : I) → S i → Set}
         {i j : I}(s : S i)(f : {j : I} → P i j s → WI₀ S P) 
         → WI₁ S P j (sup₀ {I} {S} {P} i s f) → j ≡ i
lem1 s f w = cong proj₁ (supEq₀ w)

lem2 : ∀ {I}{S : I → Set}{P : (i j : I) → S i → Set}
         {i j : I}(s : S i)(f : {j : I} → P i j s → WI₀ S P) 
         → WI₁ S P j (sup₀ {I} {S} {P} i s f)
         → {j : I}{p : P i j s} → ideal P (f p) j ≡ actual P (f p) 
lem2 {I} {S} {P} s f w {j} {p} with lem1 {I} {S} {P} s f w
lem2 s f w {j} {p} | refl = ext' (supEq₁ w) (j , p)



supI : ∀ {I}{S : I → Set}{P : (i j : I) → S i → Set}
         (i : I)(s : S i)(f : {j : I} → P i j s → WI S P j)
         → WI S P i
supI {I} {S} {P} i s f = (sup₀ {I} {S} {P} i s (λ x → proj₁ (f x))) , 
             (sup₁ {I} {S} {P} i s (λ p → proj₁ (f p)) (λ p → proj₂ (f p)))

WRecIaux : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
         → (M : (i : I)(w : WI₀ S P) → WI₁ S P i w → Set)
         → ((i : I)(s : S i)(f : {j : I} → P i j s → WI₀ S P)
            (f' : ({j : I} → (p : P i j s) → WI₁ S P j (f p)))
            → ({j : I} → (p : P i j s) → M j (f p) (f' p))
            → M i (sup₀ {I} {S} {P} i s f) (sup₁ {I} {S} {P} i s f f'))
         → (i : I)(w : WI₀ S P)(w' : WI₁ S P i w) → M i w w'
WRecIaux {I}{S} P M m i (sup (j , s) f) w =
          let f' : {k : I} → P j k s → WI₀ S P
              f' {k} p = f (k , p)
              i≡j : j ≡ i
              i≡j = sym (lem1 {I} {S} {P} s f' w)
              sf : Σ (S i) (λ s → {k : I} → P i k s → WI₀ S P)
              sf = subst (λ x → Σ (S x) (λ s → {k : I} → P x k s → WI₀ S P)) i≡j (s , λ x → f' x)
              s' : S i
              s' = proj₁ sf
              f'' : {k : I} → P i k s' → WI₀ S P
              f'' = proj₂ sf
              g0 : {k : I} → P j k s → WI S P k
              g0 {k} p = f (k , p) , lem2 {I} {S} {P} s (λ {k} p → f (k , p)) w
--              g1 : 
          in {!!}

{-

WRecI : ∀ {I}{S : I → Set}(P : (i j : I) → S i → Set) 
        → (M : (i : I) → WI S P i → Set)
        → ({i : I}(s : S i)(f : {j : I} → P i j s → WI S P j)
           → ((j : I)(p :  P i j s) → M j (f p)) → M i (supI i s f))
        → (i : I)(w : WI S P i) → M i w
WRecI {I}{S} P M m i (sup (j , s) f , w) =
        let f₀ : {k : I} → P j k s → WI₀ S P
            f₀ {k} p = f (k , p)
            f₁ : {k : I} → (p : P j k s) → WI₁ S P k (f₀ p)
            f₁ {k} p = {!!}
            i≡j : j ≡ i
            i≡j = sym (lem1 s f₀ w)
            sf : Σ (S i) (λ s → {k : I} → P i k s → WI₀ S P)
            sf = subst (λ x → Σ (S x) (λ s → {k : I} → P x k s → WI₀ S P)) i≡j (s , λ x → f₀ x)
            s' : S i
            s' = proj₁ sf
            f'' : {k : I} → P i k s' → WI₀ S P
            f'' = proj₂ sf
            m' : {!!}
            m' = m s  
        in {!!}
-}