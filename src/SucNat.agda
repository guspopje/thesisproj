open import Agda.Primitive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

--module SucNat {X= : DecSetoid lzero lzero}  where
module SucNat {X : Set} {X-dec : Decidable {A = X} _≡_ } where

  open import Data.Vec hiding (_∈_)
  open import Data.Fin hiding (_+_ ; _≤_)
  open import Data.Nat hiding (_⊔_ ; _≟_)
  open import Data.Nat.Properties using (≤-step)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Sum
  open import Relation.Nullary.Negation using (contradiction)
  open import Data.Product
  open import Data.Sum
  open import Data.Unit hiding (_≤?_ ; _≤_)
  open import Data.Empty
  open import Data.Bool
  open import Function -- using (_∘_)

  -- open import FirstKind renaming (_⊃_ to _⊃₁_ ; _&_ to _&₁_)
  open import SecondKind
  open import Common
  
  module SN where

    -- open DecSetoid X= public renaming (Carrier to X ; _≟_ to _≟X_ ; _≈_ to _≈X_ ) hiding (refl ; sym ; trans)

    _≈X_ : X → X → Set
    _≈X_ = _≡_
    
    _≟X_ : (x₁ x₂ : X) → Dec (x₁ ≡ x₂)
    _≟X_ = X-dec
   
    -- Terms

    module Terms where
      data Term (n : ℕ) : Set where
        real : X → Term n
        appa : Fin n → Term n
        tzero : Term n
        tsuc : Term n → Term n

      _∈_ : {n : ℕ} → X → Term n → Set
      x ∈ (real y) = x ≈X y
      x ∈ (appa k) = ⊥
      x ∈ tzero    = ⊥
      x ∈ (tsuc t) = x ∈ t
      
      _∈?_ : {n : ℕ} (x : X) (t : Term n) → Dec (x ∈ t)
      x ∈? (real y) = x ≟X y
      x ∈? (appa _) = no (λ ())
      x ∈? tzero    = no (λ ())
      x ∈? (tsuc t) = x ∈? t

      sub : {n : ℕ} → X → X → Term n → Term n
      sub x₁ x₂ (real x) with x₁ ≟X x
      ... | yes _ = real x₂
      ... | no _  = real x
      sub x₁ x₂ (appa a)  = appa a
      sub x₁ x₂ tzero     = tzero
      sub x₁ x₂ (tsuc t)  = tsuc (sub x₁ x₂ t)

      sub-self : {n : ℕ} → (x : X) → (t : Term n) → sub x x t ≡ t
      sub-self x (real r) with x ≟X r
      ... | yes same = cong real same
      ... | no _ = refl
      sub-self x (appa a) = refl
      sub-self x tzero    = refl
      sub-self x (tsuc t) = cong tsuc (sub-self x t)

      ∉-sub : {n : ℕ} → (x₁ x₂ : X) → (term : Term n)
          → ¬ (x₁ ∈ term)
          → (sub x₁ x₂ term) ≡ term
      ∉-sub x₁ x₂ (real r) notin with x₁ ≟X r
      ... | yes isin = contradiction isin notin
      ... | no _ = refl
      ∉-sub x₁ x₂ (appa _) _ = refl
      ∉-sub x₁ x₂ tzero _ = refl
      ∉-sub x₁ x₂ (tsuc t) notin = cong tsuc (∉-sub x₁ x₂ t notin)

      sub-∉ : {n : ℕ} → (x₁ x₂ : X) → ¬ (x₁ ≈X x₂) → (t : Term n) → ¬ (x₁ ∈ sub x₁ x₂ t)
      sub-∉ x₁ x₂ diff (real x) with x₁ ≟X x
      ... | yes p = λ wrong → diff wrong
      ... | no p  = λ wrong → p wrong
      sub-∉ x₁ x₂ diff (appa a) = id
      sub-∉ x₁ x₂ diff tzero    = id
      sub-∉ x₁ x₂ diff (tsuc t) = sub-∉ x₁ x₂ diff t

      depends : {n : ℕ} → ℕ → Term n → Set
      depends i (real r) = ⊥
      depends i (appa a) = i ≡ (toℕ a)
      depends i tzero = ⊥
      depends i (tsuc t) = depends i t

      depends? : {n : ℕ} → (i : ℕ) → (t : Term n) → Dec (depends i t)
      depends? i (real r) = no (λ ())
      depends? i (appa a) = i Data.Nat.≟ (toℕ a)
      depends? i tzero = no (λ ())
      depends? i (tsuc t) = depends? i t

      ξₐ : {n : ℕ} → ℕ → Fin n → Fin (suc n)
      ξₐ i a with i ≤? toℕ a
      ... | yes _ = suc a
      ... | no _  = relaxFin a

      ξ : {n : ℕ} → ℕ → Term n → Term (suc n)
      ξ i (appa a) = appa (ξₐ i a)
      ξ i (real x) = (real x)
      ξ i tzero    = tzero
      ξ i (tsuc t) = tsuc (ξ i t)

      r→a : {n : ℕ} → X → Fin n → Term n → Term n
      r→a x k (real y) = if ⌊ x ≟X y ⌋ then (appa k) else (real y)
      r→a x k (appa a) = (appa a)
      r→a x k tzero    = tzero
      r→a x k (tsuc t) = tsuc (r→a x k t)


-- BEGIN UGLY

      ξₐ≤ : {n : ℕ} → (i : ℕ) → (a : Fin n)
        → (i ≤ toℕ a)
        → ξₐ i a ≡ suc a
      ξₐ≤ i a i≤a with i ≤? toℕ a
      ... | yes _ = refl
      ... | no i≰a = contradiction i≤a i≰a

      ξₐ≰ : {n : ℕ} → (i : ℕ) → (a : Fin n)
        → ¬ (i ≤ toℕ a)
        → ξₐ i a ≡ relaxFin a
      ξₐ≰ i a i≰a with i ≤? toℕ a
      ... | no _ = refl
      ... | yes i≤a = contradiction i≤a i≰a

      ξₐ-relax : {n : ℕ} → (i : ℕ) → (a : Fin n)
        → ξₐ i (relaxFin a) ≡ relaxFin (ξₐ i a)
      ξₐ-relax i a with i ≤? toℕ a
      ... | yes i≤a = ξₐ≤ i (relaxFin a) (≤-relax i≤a)
      ... | no  i≰a = ξₐ≰ i (relaxFin a) (≰-relax i≰a)

      ξₐ-suc : {n : ℕ} → (i : ℕ) → (a : Fin n)
        → (i ≤ toℕ a)
        → ξₐ i (suc a) ≡ suc (ξₐ i a)
      ξₐ-suc i a i≤a with i ≤? toℕ a | i ≤? toℕ (suc a)
      ... | yes _ | yes _ = refl
      ... | yes _ | no  p = contradiction (≤-step i≤a) p
      ... | no  p | _ = contradiction i≤a p


      ξₐ-comm : {n : ℕ} → (k i : ℕ) → (a : Fin n)
        → ξₐ k (ξₐ (k + i) a) ≡ ξₐ (suc (k + i)) (ξₐ k a)
      ξₐ-comm k i a with k ≤? toℕ a
      ξₐ-comm k i a | yes k≤a with (k + i) ≤? toℕ a
      ξₐ-comm k i a | yes k≤a | yes k+i≤a = trans (ξₐ-suc k a k≤a) (cong suc (ξₐ≤ k a k≤a))
      ξₐ-comm k i a | yes k≤a | no  k+i≰a = ξₐ≤ k (relaxFin a) (≤-relax k≤a)
      ξₐ-comm k i a | no  k≰a = trans (cong (ξₐ k) ((ξₐ≰ (k + i) a (k≰a ∘ (a+b≤c⇒a≤c k i (toℕ a)))))) (trans (ξₐ≰ k (relaxFin a) (≰-relax k≰a)) (sym (ξₐ≰ (suc (k + i)) (relaxFin a) (λ 1+k+i≤a → k≰a (a+b≤c⇒b≤c 1 k (toℕ a) (a+b≤c⇒a≤c (1 + k) i (toℕ a) (subst (λ x → (suc (k + i) ≤ x)) (toℕ-relaxFin a) 1+k+i≤a)))))))

{-
      ξ-comm₀ : {n : ℕ} → (i : ℕ) → (t : Term n)
        → ξ zero (ξ i t) ≡ ξ (suc i) (ξ zero t)
      ξ-comm₀ i (appa a) with i ≤? toℕ a
      ... | yes _ = refl
      ... | no  _ = refl
      ξ-comm₀ i (real x) = refl
      ξ-comm₀ i tzero = refl
      ξ-comm₀ i (tsuc t) = cong tsuc (ξ-comm₀ i t)
-}

      ξ-comm : {n : ℕ} → (k i : ℕ) → (t : Term n)
        → ξ k (ξ (k + i) t) ≡ ξ (suc (k + i)) (ξ k t)
      ξ-comm _ _ (real r) = refl
      ξ-comm k i (appa a) = cong appa (ξₐ-comm k i a)
      ξ-comm _ _ tzero = refl
      ξ-comm k i (tsuc t) = cong tsuc (ξ-comm k i t)

-- END UGLY

      --bind : {n : ℕ} → (x : X) → (i : ℕ) → Term n → Term (suc n)
      --bind x i t = r→a x i (ξ i t)

    open Terms public using (Term ; real ; appa ; tzero ; tsuc)

    
    -- Atoms

    module Atoms where
      module T = Terms
      
      data Atom (n : ℕ) : Set where
        _==_ : Term n → Term n → Atom n

      infixr 4 _==_

      amap : {m n : ℕ} → (Term m → Term n) → Atom m → Atom n
      amap f (t == t') = (f t) == (f t')

      module AtomFun where
        sub : {n : ℕ} → X → X → Atom n → Atom n
        sub x y = amap (T.sub x y)

        _∈_ : {n : ℕ} → X → Atom n → Set
        x ∈ (t == t') = (x T.∈ t) ⊎ (x T.∈ t')

        _∈?_ : {n : ℕ} → (x : X) → (at : Atom n) → Dec (x ∈ at)
        x ∈? (t == t') = (x T.∈? t) ⊎-dec (x T.∈? t')

        sub-self : {n : ℕ} → (x : X) → (atom : Atom n) → sub x x atom ≡ atom
        sub-self x (t == t') = cong₂ _==_ (T.sub-self x t) (T.sub-self x t')
        
        sub-∉ : {n : ℕ} → (x₁ x₂ : X) → ¬ (x₁ ≈X x₂) → (atom : Atom n)
          → ¬ (x₁ ∈ (sub x₁ x₂ atom))
        sub-∉ x₁ x₂ diff (t == t') = [ T.sub-∉ x₁ x₂ diff t , T.sub-∉ x₁ x₂ diff t' ]′

        ∉-sub : {n : ℕ} → (x₁ x₂ : X) → (atom : Atom n)
          → ¬ (x₁ ∈ atom)
          → (sub x₁ x₂ atom) ≡ atom
        ∉-sub x₁ x₂ (t == t') notin = cong₂ _==_ (T.∉-sub x₁ x₂ t (notin ∘ inj₁)) (T.∉-sub x₁ x₂ t' (notin ∘ inj₂))

        -- Does this atom depend on DeBuijn index i?
        depends : {n : ℕ} → ℕ → Atom n → Set
        depends i (t == t') = (T.depends i t) ⊎ (T.depends i t')

        depends? : {n : ℕ} → (i : ℕ) → (atom : Atom n) → Dec (depends i atom)
        depends? i (t == t') = (T.depends? i t) ⊎-dec (T.depends? i t')

        -- Increment DeBuijn indices of level ≥ i.
        ξ : {n : ℕ} → ℕ → Atom n → Atom (suc n)
        ξ = amap ∘ T.ξ

        --ξ-nodep : {n : ℕ} → (i : ℕ) → (a : Atom n)
        --  → ¬ (depends i (ξ i a))
        --ξ-nodep i (t == t') = {!!}

        --ξ-inv : {n : ℕ} → (i : ℕ) → (a : Atom (suc n))
        --  → ¬ (depends i a)
        --  → Σ (Atom n) (λ a' → a ≡ ξ i a')
        --ξ-inv i (t == t') nodep = {!!}

        ξ-comm : {n : ℕ} → (k i : ℕ) → (a : Atom n)
          → ξ k (ξ (k + i) a) ≡ ξ (suc (k + i)) (ξ k a)
        ξ-comm k i (t == t') = cong₂ _==_ (T.ξ-comm k i t) (T.ξ-comm k i t')
        
        --bind : {n : ℕ} → (x : X) → (i : ℕ) → Atom n → Atom (suc n)
        --bind x i = amap (T.bind x i)

        -- Change a real variable to an apparent one.
        r→a : {n : ℕ} → X → Fin n → Atom n → Atom n
        r→a x i = amap (T.r→a x i)

        --∉-r→a : {n : ℕ} → (x : X) → (i : Fin n) → (a : Atom n) → ¬ x ∈ a → (a ≡ r→a x i a)
        --∉-r→a x i (t == t') = {!!}

      
      atomAtomic : Atomic
      atomAtomic = record
        { Atom = Atom
        ; X = X
        ; _∈_ = _∈_
        ; _∈?_ = _∈?_
        ; sub = sub
        --; sub-self = sub-self
        ; sub-∉ = sub-∉
        ; ∉-sub = ∉-sub
        ; depends = depends
        ; depends? = depends?
        ; ξ = ξ
        --; ξ-nodep = ξ-nodep
        --; ξ-inv = ξ-inv
        ; ξ-comm = ξ-comm
        ; r→a = r→a
        --; ∉-r→a = ∉-r→a
        --; bind = bind
        } where open AtomFun

    open Atoms public -- renaming (r→a to r→aa ; _∈_ to _∈a_ ; _∈?_ to _∈a?_ ; ξ to ξa)

    module QHSN = QH-Atomic atomAtomic
    open QHSN public

    module Axioms where

      _=='_ : X → X → QH0
      x ==' y = atom ((real x) == (real y))

      _+'_ : {n : ℕ} → Term n → ℕ → Term n
      t +' m = Data.Nat.fold t tsuc m
      
      data Ticket : QH0 → Set where
        h1 : (x : X) → Ticket (x ==' x)
        h2 : (x y : X) → Ticket ((x ==' y) ⊃ (y ==' x))
        h3 : (x y z : X) → Ticket (((x ==' y) & (y ==' z)) ⊃ (x ==' z))
        h4 : (x y : X) → Ticket ((x ==' y) ≣ atom ((tsuc (real x)) == (tsuc (real y))))
        h5 : (x : X) → Ticket (~ atom (tsuc (real x) == tzero))
        h6 : (x : X) → (n : ℕ) → Ticket (~ atom ((real x) == ((real x) +' (suc n))))
        h7 : (x : X) → Ticket ((atom ((real x) == tzero)) ∪ ([-] (atom ((real x) == (tsuc (appa zero))))))
      
    open Axioms public hiding (_=='_ ; _+'_)
    open Proofs Ticket public

    
  open SN public
