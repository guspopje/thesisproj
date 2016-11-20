module SucNat.FK {X : Set} where
  open import FirstKind
  open import SucNat.Base {X = X}
  open import Data.Nat using (ℕ ; zero ; suc)

  data FKAxioms : FK (Atom zero) → Set where
    h1 : (x : Term zero)         → FKAxioms (atom (x == x))
    h2 : (x y : Term zero)       → FKAxioms ((atom (x == y)) ⊃ (atom (y == x)))
    h3 : (x y z : Term zero)     → FKAxioms (((atom (x == y)) & (atom (y == z))) ⊃ (atom (x == z)))
    h4 : (x y : Term zero)       → FKAxioms ((atom (x == y)) ≣ atom (tsuc x == tsuc y))
    h5 : (x : Term zero)         → FKAxioms (~ atom (tsuc x == theℕ zero))
    h6 : (x : Term zero) (a : ℕ) → FKAxioms (~ atom (x == x +ℕ (suc a)))
    --h7 : (x : X)     → Ticket ((atom ((real x) == tzero)) ∪ ([-] (atom ((real x) == (tsuc (appa zero))))))
