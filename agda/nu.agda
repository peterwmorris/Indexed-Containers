{-# OPTIONS --type-in-type #-}

module nu where

open import Coinduction
open import Data.Unit
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Function
open import Relation.Binary.HeterogeneousEquality

_≡_ : {A : Set} → A → A → Set
a ≡ b = a ≅ b

postulate ext : {A : Set} {B : A → Set} {f g : (a : A) → B a} → ((a : A) → f a ≅ g a) → f ≅ g

postulate ext* : {A : Set} {B : A → Set} {f g : (a : A) → B a} → ((a b : A) → a ≅ b → f a ≅ g b) → f ≅ g

ext** : {A : Set} {B C : A → Set} {f : (a : A) → B a} {g : (a : A) → C a} → B ≅ C → ((a b : A) → a ≅ b → f a ≅ g b) → f ≅ g
ext** refl p = ext* p 

uip** : ∀ {A B C D : Set} {a : A} {b : B} {c : C} {d : D} → b ≅ d → (p : a ≅ b) → (q : c ≅ d) → p ≅ q
uip** refl refl refl = refl

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

caseNat : (n : Nat) {P : Nat → Set} → P zero → ((m : Nat) → P (succ m)) → P n 
caseNat zero mz ms = mz 
caseNat (succ m) mz ms = ms m 

plus : (m n : Nat) → Nat
plus zero n = n
plus (succ m) n = succ (plus m n)

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (succ n)
  succ : ∀ {n} → Fin n → Fin (succ n)

record Cont (n : Nat) : Set where
  constructor _◁_
  field
    S : Set
    P : Fin n → S → Set

record Cont₁ : Set where
  constructor _◁_
  field
    S : Set
    P : S → Set

record _⇒_ {n : Nat} (C D : Cont n) : Set where
  constructor _◁_ 
  field 
    f : Cont.S C → Cont.S D
    r : (i : Fin n) (s : Cont.S C) → Cont.P D i (f s) → Cont.P C i s

⟦_⟧ : ∀ {n} → (C : Cont n) → (Fin n → Set) → Set 
⟦_⟧ {n} (S ◁ P) X = Σ S λ s → (i : Fin n) → P i s → X i 

⟦_⟧₁ : (C : Cont₁) → Set → Set 
⟦ S ◁ P ⟧₁ X = Σ S λ s → P s → X 

⟦⟧₁map : ∀ {X Y C} → (X → Y) → ⟦ C ⟧₁ X → ⟦ C ⟧₁ Y 
⟦⟧₁map f (s , g) = s , f ∘ g

{-
data M (S : Set) (P : S → Set) : Set where
  sup : Σ S (λ s → P s → ∞ (M S P)) → M S P

pus : ∀ {S P} → M S P → Σ S (λ s → P s → M S P)
pus (sup (s , f)) = s ,  ♭ ∘ f  

data Path (S : Set) (P : S → Set) (Q : S → Set) : M S P → Set where
  here : ∀ {sf} → Q (proj₁ (pus sf)) → Path S P Q sf
  there : ∀ {sf} → Σ (P (proj₁ (pus sf))) (λ p → Path S P Q (proj₂ (pus sf) p)) → Path S P Q sf

nu : ∀ {n} → Cont (succ n) → Cont n
nu (S ◁ P) = M S (P zero) ◁ λ i m → Path S (P zero) (P (succ i)) m


_[_] : ∀ {n} → Cont (succ n) → Cont n → Cont n
(S ◁ P) [ T ◁ Q ] = Σ S (λ s → P zero s → T) ◁ λ i → uncurry (λ s f → Σ (P zero s) (λ p → Q i (f p)) ⊎ P (succ i) s)


out : ∀ {n} (C : Cont (succ n)) → nu C ⇒ C [ nu C ] 
out (S ◁ P) = pus ◁ λ i s → [ there , here ]
-}

data W (S : Set) (P : S → Set) : Set where
  sup : Σ S (λ s → P s → W S P) → W S P

data Path (S : Set) (P : S → Set) (Q : S → Set) : W S P → Set where
  here : ∀ {s f} → Q s → Path S P Q (sup (s , f))
  there : ∀ {s f} → Σ (P s) (λ p → Path S P Q (f p)) → Path S P Q (sup (s , f))

{-

MM : (S : Set) (P : S → Set) → Set
MM S P =  W (S ⊎ ⊤) [ P , (λ _ → ⊥) ] 

MM⊥ : {S : Set} {P : S → Set} → MM S P
MM⊥ = sup (inj₂ _ , \())

MMsup : {S : Set} {P : S → Set} → ⟦ S ◁ P ⟧₁ (MM S P) → MM S P
MMsup (s , f) = sup (inj₁ s , f)

Mα : {S : Set} {P : S → Set} → ⟦ S ◁ P ⟧₁ (Nat → MM S P) → Nat → MM S P
Mα (s , f) zero = MM⊥
Mα (s , f) (succ n) = MMsup (s , λ p → f p n)

Mhat : {S : Set} {P : S → Set} {X : Set} → (β : X → ⟦ S ◁ P ⟧₁ X) → X → Nat → MM S P
Mhat β x zero = MM⊥
Mhat β x (succ n) = MMsup (proj₁ (β x) , λ p → Mhat β (proj₂ (β x) p) n)

Msq : {S : Set} {P : S → Set} {X : Set} (β : X → ⟦ S ◁ P ⟧₁ X) (x : X) (n : Nat) → Mhat β x n ≅ Mα (⟦⟧₁map (Mhat β) (β x)) n
Msq β x zero = refl
Msq β x (succ y) = refl

TM :  (S : Set) (P : S → Set) → Set
TM S P = W ((S ⊎ ⊤) ⊎ ⊤) [ [ P , (λ _ → ⊥) ] , (λ _ → ⊥) ] 

TM⊥ : {S : Set} {P : S → Set} → TM S P 
TM⊥ = sup (inj₁ (inj₂ _) , \())

TMsup : {S : Set} {P : S → Set} → ⟦ S ◁ P ⟧₁ (TM S P) → TM S P
TMsup (s , f) = sup (inj₁ (inj₁ s) , f)

TM* : {S : Set} {P : S → Set} → TM S P 
TM* = sup (inj₂ _ , \())

ttrunk : {S : Set} {P : S → Set} → TM S P → Nat → TM S P
ttrunk m zero = TM⊥
ttrunk (sup (inj₁ (inj₁ s) , f)) (succ n) = TMsup (s , λ p → ttrunk (f p) n)
ttrunk (sup (inj₁ (inj₂ _) , f)) (succ n) = TM*
ttrunk (sup (inj₂ _ , f)) (succ n) = TM*

inc : {S : Set} {P : S → Set} → MM S P → TM S P
inc (sup (inj₁ x , y)) = TMsup (x , λ p → inc (y p))
inc (sup (inj₂ _ , _)) = TM⊥ 

trunk : {S : Set} {P : S → Set} → MM S P → Nat → TM S P
trunk m n = ttrunk (inc m) n

M : (S : Set) (P : S → Set) → Set
M S P = Σ (Nat → MM S P) (λ m → (n : Nat) → (inc (m n) ≅ trunk (m (succ n)) n))

α : {S : Set} {P : S → Set} → ⟦ S ◁ P ⟧₁ (M S P) → M S P
α (s , f) = (Mα (s , proj₁ ∘ f)) , prfα 
  where prfα : (n : Nat) → inc (Mα (s , proj₁ ∘ f) n) ≅
                          ttrunk (inc (Mα (s , proj₁ ∘ f) (succ n))) n
        prfα zero = refl
        prfα (succ n) = cong (λ x → sup (inj₁ (inj₁ s) , x)) (ext (λ p → proj₂ (f p) n)) 

hat : {S : Set} {P : S → Set} {X : Set} → (β : X → ⟦ S ◁ P ⟧₁ X) → X → M S P
hat {X = X} β x = (Mhat β x) , prfhat
  where prfhat : {x : X} (n : Nat) → inc (Mhat β x n) ≅ ttrunk (inc (Mhat β x (succ n))) n
        prfhat zero = refl
        prfhat {x} (succ y) = cong (λ z → sup (inj₁ (inj₁ (proj₁ (β x))) , z)) (ext (λ p → prfhat y))

{-
sq : {S : Set} {P : S → Set} {X : Set} (β : X → ⟦ S ◁ P ⟧₁ X) (x : X) (n : Nat) → hat β x ≅ α (⟦⟧₁map (hat β) (β x))
sq β x n =  cong₂ _,_ (ext (Msq _ x)) {!ext₂ ?!}
-}

α′ : {S : Set} {P : S → Set} → M S P → (n : Nat) →  ⟦ S ◁ P ⟧₁ (M S P)
α′ (x , y) n = {!inc (x (succ n))!} , {!!}
-}

data WM (S : Set) (P : S → Set) : Nat → Set where
  wm⊥ : WM S P zero
  sup : ∀ {n} → (s : S) → (P s → WM S P n) → WM S P (succ n)

sup₀ : ∀ {S P n} → WM S P (succ n) → S
sup₀ (sup s f) = s  

sup₁ : ∀ {S P n} → (x : WM S P (succ n)) → P (sup₀ x) → WM S P n
sup₁ (sup s f) = f 

trunc : ∀ {S P} → {n : Nat} → WM S P (succ n) → WM S P n
trunc {n = zero} (sup s f) = wm⊥
trunc {n = succ n} (sup s f) = sup s (trunc ∘ f)

sup₀t≡ : ∀ {S P n} → (x : WM S P (succ (succ n))) → sup₀ (trunc x) ≡ sup₀ x
sup₀t≡ (sup s f) = refl

sup₁t≡ : ∀ {S P n} → (x : WM S P (succ (succ n))) (p : P (sup₀ x)) → trunc (sup₁ x p) ≡ sup₁ (trunc x) (subst P (sym (sup₀t≡ x)) p) 
sup₁t≡ (sup s f) p = refl 

M : (S : Set) (P : S → Set) → Set
M S P = Σ ((n : Nat) → WM S P n) λ f → (n : Nat) → trunc (f (succ n)) ≡ f n

msup₀ : ∀ {S P} → (s : S) (f : P s → M S P) (n : Nat) → WM S P n
msup₀ s f zero = wm⊥
msup₀ s f (succ n) = sup s (λ p → proj₁  (f p) n)

msup₁ : ∀ {S P} → (s : S) (f : P s → M S P) (n : Nat) → trunc (msup₀ s f (succ n)) ≡ msup₀ s f n
msup₁ s f zero = refl
msup₁ {S} {P} s f (succ n) = cong {B = λ f → WM S P (succ n)} (sup s) (ext (λ p → proj₂ (f p) n))

msup : ∀ {S P} → (s : S) (f : P s → M S P) → M S P
msup s f = (msup₀ s f) , (msup₁ s f)

msup⁻¹₀ :  ∀ {S P} → (n : Nat) → M S P → S
msup⁻¹₀ n (x , _) = sup₀ (x (succ n)) 

msup⁻¹₀≡s :  ∀ {S P} →  (n : Nat) → (x : M S P) → msup⁻¹₀ n x ≡ msup⁻¹₀ (succ n) x 
msup⁻¹₀≡s {S} {P} n (x , y) = trans (sym (cong (sup₀ {S} {P} {n}) (y (succ n)))) (sup₀t≡ (x (succ (succ n)))) 

msup⁻¹₀≡ :  ∀ {S P} →  (n : Nat) → (x : M S P) → msup⁻¹₀ zero x ≡ msup⁻¹₀ n x 
msup⁻¹₀≡ zero x = refl
msup⁻¹₀≡ (succ y) x = trans (msup⁻¹₀≡ y x) (msup⁻¹₀≡s y x)

msup⁻¹₁ :  ∀ {S P} (x : (n : Nat) → WM S P n) (y : (n : Nat) → trunc (x (succ n)) ≡ x n) → (n : Nat) → P (sup₀ (x (succ n))) → WM S P n
msup⁻¹₁ m y n p = sup₁ (m (succ n)) p

α :  ∀ {S P} → ⟦ S ◁ P ⟧₁ (M S P) → M S P
α (s , f) = (msup₀ s f) , msup₁ s f

α′₀ : ∀ {S P} → M S P → S
α′₀ (x , y) = sup₀ (x (succ zero))



α′ :  ∀ {S P} → M S P → ⟦ S ◁ P ⟧₁ (M S P) 
α′ m = α′₀ m , {!!}

{-

α′ {S} {P} (x , y) = sup₀ (x (succ zero)) , λ p → (λ n → sup₁ (x (succ n)) (subst P (msup⁻¹₀≡ n (x , y)) p)) , λ n → trans (sup₁t≡ (x (succ (succ n))) (subst P (msup⁻¹₀≡ (succ n) (x , y)) p)) (cong₂ {A = WM S P (succ n)} {B = λ w → P (sup₀ w)} {C = λ w p → WM S P n} {trunc (x (succ (succ n)))} {x (succ n)} sup₁ (y (succ n)) (trans (subst-removable P (sym (sup₀t≡ (x (succ (succ n))))) _) (trans (subst-removable P (trans (msup⁻¹₀≡ n (x , y))
 (trans (sym (cong sup₀ (y (succ n))))
  (sup₀t≡ (x (succ (succ n)))))) _) (sym (subst-removable P (msup⁻¹₀≡ n (x , y)) _))))) 


≡M : ∀ {S P} {x y : M S P} → ((n : Nat) → proj₁ x n ≡ proj₁ y n) → x ≡ y
≡M {x = x , xok} {y = y , yok} p = cong₂ _,_ (ext p) (ext** (ext λ n → subst (λ xn → (trunc (x (succ n)) ≅ xn) ≅ (trunc (y (succ n)) ≅ y n)) (sym (p n)) (subst (λ xsn → (trunc xsn ≅ y n) ≅ (trunc (y (succ n)) ≅ y n)) (sym (p (succ n))) refl)) (λ a b q → uip** (subst (λ c → x a ≅ y c) q (p a)) (xok a) (yok b)))


WM0≡ : ∀ {S P} → (x y : WM S P zero) → x ≡ y
WM0≡ wm⊥ wm⊥ = refl

prfα : ∀ {S P} → (x : M S P) → α (α′ x) ≡ x
prfα {S} {P} (x , y) = ≡M foo
  where foo :  (n : Nat) → proj₁ (α (α′ (x , y))) n ≡ x n
        foo zero = WM0≡ _ _
        foo (succ n') = {!!}

-}