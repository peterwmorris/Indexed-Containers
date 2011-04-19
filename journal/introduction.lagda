%if style == code

\begin{code}

{-# OPTIONS --no-termination-check --universe-polymorphism #-}

module introduction where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality
-- open import Data.List
open import Function

open import common
open import tt


\end{code}

%endif

\section{Introduction}

\begin{code}

data ℕ : Set where
  zero  : ℕ
  suc   : (n : ℕ) → ℕ

\end{code}


\begin{code}

data List (A : Set) : Set where
  []   :               List A
  _∷_  : A → List A →  List A

\end{code}

\begin{code}

data Lam : Set where
  var  : (n : ℕ)      → Lam
  app  : (f a : Lam)  → Lam
  lam  : (t : Lam)    → Lam

\end{code}

%format Fℕ = F "_{" ℕ "}"
%format FList = F "_{" List "}"
%format FLam = F "_{" Lam "}"

\begin{code}

Fℕ : Set → Set
Fℕ X = ⊤ ⊎ X

FList : (A : Set) → Set → Set
FList A X = ⊤ ⊎ (A × X) 

FLam : Set → Set
FLam X = ℕ ⊎ (X × X) ⊎ X

\end{code}

\begin{code}

data Fin : ℕ → Set where
  zero  : ∀ {n}              → Fin (suc n)
  suc   : ∀ {n} (i : Fin n)  → Fin (suc n)

\end{code}

\begin{code}

data Vec (A : Set) : ℕ → Set where
  []   :                                 Vec A zero
  _∷_  : ∀ {n} (a : A) (as : Vec A n) →  Vec A (suc n)

\end{code}

\begin{code}

data ScLam (n : ℕ) : Set where
  var  : (i : Fin n)          → ScLam n
  app  : (f a : ScLam n)      → ScLam n
  lam  : (t : ScLam (suc n))  → ScLam n

\end{code}

%format FFin = F "_{" Fin "}"
%format FVec = F "_{" Vec "}"
%format FScLam = F "_{" ScLam "}"

\begin{code}

FFin : (ℕ → Set) → ℕ → Set
FFin X n = Σ ℕ λ m → (n ≡ suc m) × (⊤ ⊎ X m)

FVec : (A : Set) → (ℕ → Set) → ℕ → Set
FVec A X n = n ≡ zero ⊎ Σ ℕ λ m → (n ≡ suc m) × (A × X m)

FScLam : (ℕ → Set) → ℕ → Set
FScLam X n = Fin n ⊎ (X n × X n) ⊎ (X ∘ suc) n

\end{code}

\begin{code}

mutual

  data NeLam (n : ℕ) : Set where
    var  : (i : Fin n)                  → NeLam n
    app  : (f : NeLam n) (a : NfLam n)  → NeLam n 

  data NfLam (n : ℕ) : Set where
    lam  : (t : NfLam (suc n))          → NfLam n
    ne   : (t : NeLam n)                → NfLam n

\end{code}

%format ι = "\iota"
%format σ = "\sigma"
%format τ = "\tau"
%format Γ = "\Gamma"

%format ->- = "\Rightarrow"
%format _->-_ = _ ->- _

\begin{code}

data Ty : Set where
  ι  : Ty
  _->-_   : (σ τ : Ty) → Ty

data Var (τ : Ty) : List Ty → Set where
  zero  : ∀ {Γ}                  → Var τ (τ ∷ Γ)
  suc   : ∀ {σ Γ} (i : Var τ Γ)  → Var τ (σ ∷ Γ)

data STLam (Γ : List Ty) : Ty → Set where
  var  : ∀ {τ}    (i : Var τ Γ)            → STLam Γ τ
  app  : ∀ {σ τ}  (f : STLam Γ (σ ->- τ)) 
                  (a : STLam Γ σ)          → STLam Γ τ
  lam  : ∀ {σ τ}  (t : STLam (σ ∷ Γ) τ)    → STLam Γ (σ ->- τ) 

\end{code}
