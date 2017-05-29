module Experiments where

  open import QElim
  open import SN
  open import Data.Nat
  open import Data.Fin renaming (zero to fzero ; suc to fsuc)
  open import Data.Vec
  open import Relation.Nullary

  open WithDecAtom sn-da

  test₀ : Prop zero
  test₀ = E E (
      (atom (S 3 (var (fsuc fzero)) == S 1 (var fzero))) -- 3 + x = 1 + y
    & (atom (S 8 ∅ == S 4 (var fzero)))                  -- 8 = 4 + y
    )

  ⟦test₀⟧? : Dec (⟦ test₀ ⟧ [])
  ⟦test₀⟧? = ⟦ test₀ ⟧? []

  -- =)


  -- ∀x.(x = 0 ∨ ∃y.x=y+1)
  test₁ : Prop zero
  test₁ = A ((atom (S zero (var fzero) == S zero ∅))
             ∪ (E (atom (S zero (var (fsuc fzero)) == S 1 (var fzero)))))

  ⟦test₁⟧? : Dec (⟦ test₁ ⟧ [])
  ⟦test₁⟧? = ⟦ test₁ ⟧? []
