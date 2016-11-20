module SucNat.Base {X : Set} where
  open import Data.Nat using (ℕ ; zero ; suc ; _+_)
  open import Data.Fin using (Fin)

{-
  data Term (n : ℕ) : Set where
    real : X → Term n
    appa : Fin n → Term n
    tzero : Term n
    tsuc : Term n → Term n
-}

  data Base (n : ℕ) : Set where
    real : X → Base n
    appa : Fin n → Base n
    tzero : Base n

  data Term (n : ℕ) : Set where
    S : ℕ → Base n → Term n

  tsuc : {n : ℕ} → Term n → Term n
  tsuc (S k x) = S (suc k) x 

  data Atom (n : ℕ) : Set where
    _==_ : Term n → Term n → Atom n

  infixr 4 _==_

  _+ℕ_ : {n : ℕ} → Term n → ℕ → Term n
  (S k x) +ℕ j = S (j + k) x

  theℕ : {n : ℕ} → ℕ → Term n
  theℕ k = S k tzero

  theVar : {n : ℕ} → X → Term n
  theVar x = S zero (real x)

    
