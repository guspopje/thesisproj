open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module SucNat.DecVar {X : Set} {_≟_ : Decidable {A = X} _≡_ } where

  open import SucNat.Base {X = X}
  open import Data.Nat using (ℕ)
  open import Data.Empty using (⊥)
  open import Data.Sum
  open import Relation.Nullary
  open import Relation.Nullary.Sum

  module T where
  
    _∈_ : {n : ℕ} → X → Term n → Set
    x ∈ (S k (real y)) = x ≡ y
    x ∈ (S k (appa i)) = ⊥
    x ∈ (S k tzero) = ⊥
    
    _∈?_ : {n : ℕ} (x : X) (t : Term n) → Dec (x ∈ t)
    x ∈? (S k (real y)) = x ≟ y
    x ∈? (S k (appa i)) = no (λ ())
    x ∈? (S k tzero) = no (λ ())
    

  module A where

    _∈_ : {n : ℕ} → X → Atom n → Set
    x ∈ (t == t') = (x T.∈ t) ⊎ (x T.∈ t')

    _∈?_ : {n : ℕ} → (x : X) → (at : Atom n) → Dec (x ∈ at)
    x ∈? (t == t') = (x T.∈? t) ⊎-dec (x T.∈? t')

