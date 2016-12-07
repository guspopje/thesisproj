-- QH with any sort of atoms.
open import Data.Nat using (ℕ ; zero ; suc)
module SK.Base {Atom : ℕ → Set} where

  -- QH (sub-)propositions, indexed by a limit on de bruijn indices.  
  data QH (n : ℕ) : Set where
    atom : Atom n → QH n
    ~_ : QH n → QH n
    _∪_ : QH n → QH n → QH n
    [+]_ : QH (suc n) → QH n
    [-]_ : QH (suc n) → QH n
  
  infixr 16 _&_
  infixr 15 _∪_
  infixr 14 _⊃_
  infix 13 _≣_

  -- Implication
  _⊃_ : {n : ℕ} → QH n → QH n → QH n
  p ⊃ q = (~ p) ∪ q

  -- Conjunction
  _&_ : {n : ℕ} → QH n → QH n → QH n
  p & q = ~ (~ p ∪ ~ q)

  -- Equivalence
  _≣_ : {n : ℕ} → QH n → QH n → QH n
  p ≣ q = (p ⊃ q) & (q ⊃ p)
