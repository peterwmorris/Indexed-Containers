{-# OPTIONS --universe-polymorphism #-}

module WIpwm where

open import Level

data _≡_ {A : Set} (a : A) : {B : Set} → B → Set where
  refl : a ≡ a

subst : {A : Set} (P : A → Set) {x y : A} → (x ≡ y) → P x → P y
subst P refl p = p  

subst₂ : {A : Set} {B : A → Set} (P : (a : A) → B a → Set) → {a a' : A} → a ≡ a'
          → {b : B a} {b' : B a'} → b ≡ b' → P a b → P a' b'
subst₂ P refl refl p = p

resp : {A : Set} {B : A → Set} (f : (a : A) → B a) {a b : A} → (a ≡ b) → f a ≡ f b
resp f refl = refl

uip : {A : Set} {a : A} {B : Set} {b : B} (p q : a ≡ b) → p ≡ q
uip refl refl = refl

cong : {A : Set} {B : A → Set} (f g : (a : A) → B a) {a b : A} → (f ≡ g) → (a ≡ b) → f a ≡ g b
cong f .f refl refl = refl

postulate ext : {A : Set} {B : A → Set} {f g : (a : A) → B a} (p : (a : A) → f a ≡ g a) → f ≡ g
  
data W (S : Set) (P : S → Set) : Set where
  sup : (s : S) (f : P s → W S P) → W S P

Wπ₀ : ∀ {S P} → W S P → S
Wπ₀ (sup s _) = s

Wπ₁ : ∀ {S P} → (x : W S P) → P (Wπ₀ x) → W S P
Wπ₁ (sup _ f) = f

Wπ₀≡ : ∀ {S P} → {x y : W S P} → x ≡ y → Wπ₀ x ≡ Wπ₀ y
Wπ₀≡ {x = sup _ _} refl = refl

Wπ₁≡ : ∀ {S P} → {x y : W S P} → x ≡ y → Wπ₁ x ≡ Wπ₁ y
Wπ₁≡ {x = sup _ _} refl = refl


Welim : {S : Set} {P : S → Set} (x : W S P) (Q : W S P → Set) 
         (msup : (s : S) (f : P s → W S P) 
                  (h : (p : P s) → Q (f p)) → Q (sup s f)) 
         → Q x
Welim (sup s f) Q msup = msup s f (λ p → Welim (f p) Q msup)

data WI (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) : I → Set where
  supi : {i : I} (s : S i) (f : {j : I} → P i s j → WI I S P j) → WI I S P i 

WIelim : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set}
          {i : I} (x : WI I S P i) (Q : {i : I} → WI I S P i → Set)
           (msupi : {i : I} (s : S i) (f : {j : I} → P i s j → WI I S P j)
                     (h : {j : I} (p : P i s j) → Q (f p)) → Q (supi s f))
           → Q x
WIelim (supi s f) Q msupi = msupi s f (λ p → WIelim (f p) Q msupi)



record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field π₀ : A ; π₁ : B π₀

Σπ₁≡ : ∀ {A B} → {x y : Σ A B} → x ≡ y → Σ.π₁ x ≡ Σ.π₁ y
Σπ₁≡ {x = a , b} refl = refl



_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

split : {l : Level} {A : Set} {B : A → Set} {C : Σ A B → Set l}  →
          ((a : A) (b : B a) → C (a , b)) → (x : Σ A B) → C x
split f (a , b) = f a b

WIpre : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) → Set 
WIpre I S P = W (Σ I S) (split λ i s → Σ I (P i s))

WIlab : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) → Set 
WIlab I S P = W ((Σ I S) × I) (split (split λ i s _ → Σ I (P i s)))

WIdown : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) → I →
         WIpre I S P → WIlab I S P
WIdown I S P i x = -- (sup (j , s) f) = sup ((j , s) , i) (split λ k p → WIdown I S P k (f (k , p))) 
  Welim x (λ _ → I → WIlab I S P)  
          (split λ j s f h i → sup (((j , s) , i)) (split λ k p → h (k , p) k)) i

WIup : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) →
        WIpre I S P → WIlab I S P
WIup I S P x = -- (sup (i , s) f) =  sup ((i , s) , i) (λ p → WIup I S P (f p))
  Welim x (λ _ → WIlab I S P)  
          (split λ i s f h → sup (((i , s) , i)) h)

WIOK : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) (i : I) → WIpre I S P → Set
WIOK I S P i pre = WIdown I S P i pre ≡ WIup I S P pre

WI' : (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) → I → Set 
WI' I S P i = Σ (WIpre I S P) (WIOK I S P i) 

supi' : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set} 
         {i : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j) → WI' I S P i
supi' {I} {S} {P} {i = i} s f = (sup (i , s) (split (λ j p → Σ.π₀ (f p)))) , resp (sup ((i , s) , i)) (ext (split (λ j p → Σ.π₁ (f p))))

supi'' : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set} 
         {i i' : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j) → i' ≡ i → WI' I S P i'
supi'' {I} {S} {P} {i } s f refl = supi' {I} {S} {P} {i } s f 

projok₀ : ∀ {I S P} (i : I) {j : I} (s : S j) 
           (f : Σ I (P j s) → W (Σ I S) (split (λ i0 s' → Σ I (P i0 s'))))
            → WIOK I S P i (sup (j , s) f) → i ≡ j
projok₀ i s f ok = Σπ₁≡ (Wπ₀≡ ok) 

projok₁ : ∀ {I S P} (i : I) {j : I} (s : S j) 
           (f : Σ I (P j s) → W (Σ I S) (split (λ i0 s' → Σ I (P i0 s'))))
             → WIOK I S P i (sup (j , s) f) → (p : Σ I (P j s)) →
              WIOK I S P (Σ.π₀ p) (f p)
projok₁ i s f ok p = cong _ _ (Wπ₁≡ ok) refl

WIelim'' : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set}
            {i : I} (x : WIpre I S P) (ok : WIOK I S P i x) 
             (Q : {i : I} → WI' I S P i → Set)
              (msupi' : {i i' : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j)
                         (h : {j : I} (p : P i s j) → Q (f p)) (p : i' ≡ i) → Q (supi'' {I} {S} {P} {i} {i'} s f p))
              → Q (x , ok)
WIelim'' {I} {S} {P} {i} (sup (i' , s) f) ok Q msupi -- with projok₀ {I} {S} {P} i s f ok 
 =   subst (λ pr → Q (sup (i' , s) f , pr)) (uip _ _) (msupi s (λ x → (f (_ , x)) , projok₁ {I} {S} {P} i s f ok (_ , x)) (WIelim'' {I} {S} {P} {!!} {!!} {!Q!} msupi) {! projok₀ {I} {S} {P} i s f ok !})

{-

WIelim' : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set}
           {i : I} (x : WI' I S P i) (Q : {i : I} → WI' I S P i → Set)
            (msupi' : {i : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j)
                       (h : {j : I} (p : P i s j) → Q (f p)) → Q (supi' {I} {S} {P} {i} s f))
            → Q x
WIelim' {I} {S} {P} (x , ok) = WIelim'' {I} {S}{P} x ok


WIelim''' : {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set}
             {i : I} (x : WIpre I S P) (ok : WIOK I S P i x) 
              (Q : {i : I} → WI' I S P i → Set)
               (msupi' : {i : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j)
                         (h : {j : I} (p : P i s j) → Q (f p)) → Q (supi' {I} {S} {P} {i} s f))
               → Q (x , ok)
WIelim''' = {!!}
-}

{-

-- Does the computation rule hold?

WIelim'OK :  {I : Set} {S : I → Set} {P : (i : I) → S i → I → Set}
           {i : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j) (Q : {i : I} → WI' I S P i → Set)
            (msupi' : {i : I} (s : S i) (f : {j : I} → P i s j → WI' I S P j)
                       (h : {j : I} (p : P i s j) → Q (f p)) → Q (supi' {I} {S} {P} {i} s f))
             → WIelim' {I} {S} {P} (supi' {I} {S} {P} {i} s f) Q msupi' ≡ msupi' s f  (λ p → WIelim' {I} {S} {P} (f p) Q msupi')
WIelim'OK {I} {S} {P} {i} s f Q msupi with Σπ₁≡
         (Wπ₀≡
          (resp {B = ?} (sup ((i , s) , i)) (ext (split (λ j p → Σ.π₁ (f p)))))) 
... | pr = {!!}
-}