module SucNat.SK {X : Set} where
  open import SucNat.Base {X = X}
  open import Data.Nat using (ℕ ; zero ; suc)
  open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
  open import SK.Base {Atom = Atom}

  {-
  data SKAxioms : QH zero → Set where
    h1 : (x : Term zero)         → SKAxioms (atom (x == x))
    h2 : (x y : Term zero)       → SKAxioms ((atom (x == y)) ⊃ (atom (y == x)))
    h3 : (x y z : Term zero)     → SKAxioms (((atom (x == y)) & (atom (y == z))) ⊃ (atom (x == z)))
    h4 : (x y : Term zero)       → SKAxioms ((atom (x == y)) ≣ atom (tsuc x == tsuc y))
    h5 : (x : Term zero)         → SKAxioms (~ atom (tsuc x == theℕ zero))
    h6 : (x : Term zero) (a : ℕ) → SKAxioms (~ atom (x == x +ℕ (suc a)))
    h7 : (x : Term zero)         → SKAxioms ((atom (x == (S zero tzero))) ∪ ([-] (atom (x == (S 1 (appa fzero))))))
    -- Fix index issues with x
  -}
