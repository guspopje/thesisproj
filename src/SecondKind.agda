module SecondKind where

  open import Agda.Primitive
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; subst₂)
  open import Relation.Binary.PropositionalEquality.Core
  open import Data.Vec using (Vec ; [] ; _∷_)
  open import Data.List using (List ; _∷_ ; [] ; _++_)
  --open import Data.List using (List ; _∷_ ; [] ; _++_ ; map ; concat)
  open import Data.Fin using (Fin ; zero ; suc ; toℕ)
  open import Data.Nat using (ℕ ; zero ; suc ; _+_)
  open import Data.Nat.Properties.Simple using (+-suc)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable using ()
  open import Relation.Nullary.Sum using (_⊎-dec_)
  open import Relation.Nullary.Product using (_×-dec_)
  open import Relation.Nullary.Negation using (¬?)
  open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Data.Unit
  open import Data.Empty
  open import Function
  --open import Common using (flop)
  open import Common
  
  open import FirstKind renaming (_⊃_ to _⊃₁_ ; _&_ to _&₁_ ; _≣_ to _≣₁_ ;  _≣!_ to _≣!₁_ ; ≣-refl to ≣₁-refl ; ≣-sym to ≣₁-sym)

  -- QH with any sort of atoms.
  module QH-Pure {α : Level} (Atom : ℕ → Set α) where

    -- QH (sub-)propositions, indexed by a limit on de bruijn indices.  
    data QH (n : ℕ) : Set α where
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
    
    -- Well-formed propositions.
    QH0 : Set α
    QH0 = QH zero

    -- Quantifier-free (sub)propositions.
    elementary : {n : ℕ} → QH n → Set
    elementary (atom _) = ⊤
    elementary (~ p) = elementary p
    elementary (p ∪ q) = elementary p × elementary q
    elementary ([+] _) = ⊥
    elementary ([-] _) = ⊥

    -- Map an *elementary* proposition of the second kind to a proposition of the first kind
    mapSF : ∀{β} {C : Set β} → (Atom zero → C) → (p : QH0) → elementary p → FK C
    mapSF f (atom a) _ = atom (f a)
    mapSF f (~ p) e = ~ (mapSF f p e)
    mapSF f (p ∪ q) (elp , elq) = (mapSF f p elp) ∪ (mapSF f q elq)
    mapSF f ([+] _) ()
    mapSF f ([-] _) ()

    -- Map a prop of the first kind to one of the second kind
    mapFS : ∀{β} {C : Set β} → (C → Atom zero) → FK C → QH0
    mapFS f (atom a) = atom (f a)
    mapFS f (~ p) = ~ (mapFS f p)
    mapFS f (p ∪ q) = (mapFS f p) ∪ (mapFS f q)



    -- Canonical mapping of second kind to first kind
    lower : (p : QH0) → elementary p → FK (Atom zero)
    lower = mapSF id

    -- Canonical mapping of first kind to second kind
    raise : FK (Atom zero) → QH0
    raise = mapFS id









    -- A context for identifying a location ("hole") in a QH, à la zipper.
    -- The first argument to each constructor is the parent context.
    -- Indexed by the hole index limit, and the resulting proposition's index limit (see _◂_).
    data Context : ℕ → ℕ → Set α where
      ∙ : {n : ℕ} → Context n n
      _~∙ : {m n : ℕ} → Context m n → Context m n
      _⟨∙∪_⟩ : {m n : ℕ} → Context m n → QH m → Context m n
      _⟨_∪∙⟩ : {m n : ℕ} → Context m n → QH m → Context m n
      _[+]∙ : {m n : ℕ} → Context m n → Context (suc m) n
      _[-]∙ : {m n : ℕ} → Context m n → Context (suc m) n

    -- Insert a QH into a context.
    infix 11 _◂_
    _◂_ : {m n : ℕ} → Context m n → QH m → QH n
    ∙ ◂ p = p
    (c ~∙) ◂ p = c ◂ (~ p)
    (c ⟨∙∪ q ⟩) ◂ p = c ◂ (p ∪ q)
    (c ⟨ p ∪∙⟩) ◂ q = c ◂ (p ∪ q)
    (c [+]∙) ◂ p = c ◂ ([+] p)
    (c [-]∙) ◂ p = c ◂ ([-] p)


    data Somewhere {n : ℕ} (R : {m : ℕ} → QH m → QH m → Set) : QH n → QH n → Set α where
        at : {m : ℕ} {Φ₁ Φ₂ : QH m} → (c : Context m n) → R Φ₁ Φ₂ → Somewhere R (c ◂ Φ₁) (c ◂ Φ₂)




    -- Recursion/induction on QH
    QHrec : ∀{β} {n : ℕ}
      → (P : {k : ℕ} → QH k → Set β)
      → ({k : ℕ} → (a : Atom k) → P (atom a))
      → ({k : ℕ} → {p : QH k} → P p → P (~ p))
      → ({k : ℕ} → {p₁ p₂ : QH k} → P p₁ → P p₂ → P (p₁ ∪ p₂))
      → ({k : ℕ} → {p : QH (suc k)} → P p → P ([+] p))
      → ({k : ℕ} → {p : QH (suc k)} → P p → P ([-] p))
      → (p : QH n)
      → P p
    QHrec P f-atom f-not f-or f-all f-ex (atom a)  = f-atom a
    QHrec P f-atom f-not f-or f-all f-ex (~ p)     = f-not (QHrec P f-atom f-not f-or f-all f-ex p)
    QHrec P f-atom f-not f-or f-all f-ex (p₁ ∪ p₂) = f-or  (QHrec P f-atom f-not f-or f-all f-ex p₁) (QHrec P f-atom f-not f-or f-all f-ex p₂)
    QHrec P f-atom f-not f-or f-all f-ex ([+] p)   = f-all (QHrec P f-atom f-not f-or f-all f-ex p)
    QHrec P f-atom f-not f-or f-all f-ex ([-] p)   = f-ex  (QHrec P f-atom f-not f-or f-all f-ex p)

    -- With a depth counter alongside.
    QHrec' : ∀{β γ} {n : ℕ} {C : ℕ → Set γ}
      → (s : {k : ℕ} → C k → C (suc k))
      → (P : {k : ℕ} → C k → QH k → Set β)
      → ({k : ℕ} → (i : C k) → (a : Atom k) → P i (atom a))
      → ({k : ℕ} → {p : QH k} → (i : C k) → P i p → P i (~ p))
      → ({k : ℕ} → {p₁ p₂ : QH k} → (i : C k) → P i p₁ → P i p₂ → P i (p₁ ∪ p₂))
      → ({k : ℕ} → {p : QH (suc k)} → (i : C k) → P (s i) p → P i ([+] p))
      → ({k : ℕ} → {p : QH (suc k)} → (i : C k) → P (s i) p → P i ([-] p))
      → (z : C n)
      → (p : QH n)
      → P z p
    QHrec' s P f-atom f-not f-or f-all f-ex i (atom a)  = f-atom i a
    QHrec' s P f-atom f-not f-or f-all f-ex i (~ p)     = f-not i (QHrec' s P f-atom f-not f-or f-all f-ex i p)
    QHrec' s P f-atom f-not f-or f-all f-ex i (p₁ ∪ p₂) = f-or  i (QHrec' s P f-atom f-not f-or f-all f-ex i p₁) (QHrec' s P f-atom f-not f-or f-all f-ex i p₂)
    QHrec' s P f-atom f-not f-or f-all f-ex i ([+] p)   = f-all i (QHrec' s P f-atom f-not f-or f-all f-ex (s i) p)
    QHrec' s P f-atom f-not f-or f-all f-ex i ([-] p)   = f-ex  i (QHrec' s P f-atom f-not f-or f-all f-ex (s i) p)



  -- Code where we have QH's with different atom types.
  module MixedAtom where
    open QH-Pure
   
    -- Depth-dependent map.
    mapQH' : ∀{α β γ} {A : ℕ → Set α} {B : ℕ → Set β} {C : ℕ → Set γ} {n : ℕ} (s : ∀{k} → C k → C (suc k)) → C n → (f : ∀{k} → C k → A k → B k) → QH A n → QH B n
    mapQH' s i f (atom a) = atom (f i a)
    mapQH' s i f (~ p) = ~ (mapQH' s i f p)
    mapQH' s i f (p ∪ q) = (mapQH' s i f p) ∪  (mapQH' s i f q)
    mapQH' {n} s i f ([+] p) = [+] (mapQH' s (s i) f p)
    mapQH' {n} s i f ([-] p) = [-] (mapQH' s (s i) f p) 
    
    -- Map.
    mapQH : ∀{α β} {A : ℕ → Set α} {B : ℕ → Set β} {n : ℕ} → ({k : ℕ} → A k → B k) → QH A n → QH B n
    mapQH f = mapQH' {γ = lzero} {C = const ⊤} id tt (const f)

    -- Join, à la monad.
    joinQH : ∀{α} {A : ℕ → Set α} {n : ℕ} → QH (QH A) n → QH A n
    joinQH {A = A} = QHrec (QH A) (λ {k} p → QH A k) id ~_ _∪_ [+]_ [-]_

    -- Substitute a QH in place of the atoms of another. Monadic bind.
    subQH : ∀{α β} {A : ℕ → Set α} {B : ℕ → Set β} {n : ℕ} (f : {k : ℕ} → A k → QH B k) → QH A n → QH B n
    subQH f = joinQH ∘ (mapQH f)



    

  -- Well-behaved atoms.
  record Atomic : Set1 where
    field
      Atom : ℕ → Set  -- atoms for a given depth
      X : Set         -- real variable names
      
      -- Does this atom contain real variable x?
      _∈_ : {n : ℕ} → X → Atom n → Set
      _∈?_ : {n : ℕ} → (x : X) → (atom : Atom n) → Dec (x ∈ atom)

      -- Substitute one real variable for another.
      sub : {n : ℕ} → X → X → Atom n → Atom n
      -- sub-self : {n : ℕ} → (x : X) → (atom : Atom n) → sub x x atom ≡ atom
      sub-∉ : {n : ℕ} → (x₁ x₂ : X) → ¬ (x₁ ≡ x₂) → (atom : Atom n)
        → ¬ (x₁ ∈ (sub x₁ x₂ atom))
      ∉-sub : {n : ℕ} → (x₁ x₂ : X) → (atom : Atom n)
        → ¬ (x₁ ∈ atom)
        → (sub x₁ x₂ atom) ≡ atom
      
      -- Does this atom depend on DeBuijn index i?
      depends : {n : ℕ} → ℕ → Atom n → Set
      depends? : {n : ℕ} → (i : ℕ) → (atom : Atom n) → Dec (depends i atom)

      -- Increment DeBuijn indices of level ≥ i.
      ξ : {n : ℕ} → ℕ → Atom n → Atom (suc n)
      {-
      ξ-nodep : {n : ℕ} → (i : ℕ) → (a : Atom n)
        → ¬ (depends i (ξ i a))
      ξ-inv : {n : ℕ} → (i : ℕ) → (a : Atom (suc n))
        → ¬ (depends i a)
        → Σ (Atom n) (λ a' → a ≡ ξ i a')
      -}
      ξ-comm : {n : ℕ} → (k i : ℕ) → (a : Atom n)
        → ξ k (ξ (k + i) a) ≡ ξ (suc (k + i)) (ξ k a)
        -- move ∘ break     ≡       break₊₁ ∘ move
        
      -- Change a real variable to an apparent one.
      r→a : {n : ℕ} → X → Fin n → Atom n → Atom n
      --∉-r→a : {n : ℕ} → (x : X) → (i : Fin n) → (a : Atom n) → ¬ x ∈ a → (a ≡ r→a x i a)

      -- Change an apparent variable to a real one.
      --a→r : {n : ℕ} → Fin n → X → Atom n → Atom n

      -- Increment DeBuijn indices ≥ i, replace real variable x with i.
      --bind : {n : ℕ} → (x : X) → (i : ℕ) → Atom n → Atom (suc n)
      -- Replace DeBruijn index i with a real variable x, decrement indexes > i.
      --unbind : {n : ℕ} → (x : X) → (i : ℕ) → Atom (suc n) → Atom n

      --unbind∘bind : {n : ℕ} (x : X) (i : ℕ) (a : Atom n) → unbind x i (bind x i a) ≡ a
      --bind∘unbind : {n : ℕ} (x : X) (i : ℕ) (a : Atom (suc n)) → ¬ (x ∈ a) → bind x i (unbind x i a) ≡ a

  -- QH applied to well-behaved atoms.
  module QH-Atomic (atomic : Atomic) where

    open Atomic atomic using (Atom ; X) renaming (sub to atomSub)
    module A = Atomic atomic

    open QH-Pure Atom public
    open MixedAtom public



    -- Substitute a real variable
    sub : {n : ℕ} → X → X → QH n → QH n
    sub x₁ x₂ = mapQH (Atomic.sub atomic x₁ x₂)

    
    -- Increment De Bruijn indices over a given threshold,
    -- adapting to levels. Ex: ξ zero increments "free" indices.
    -- See CoC paper.
    ξ : {n : ℕ} → ℕ → QH n → QH (suc n)
    ξ = QHrec' suc (λ {k} _ _ → QH (suc k))
        (λ i a → atom (Atomic.ξ atomic i a))
        (λ i → ~_)
        (λ i → _∪_)
        (λ i → [+]_)
        (λ i → [-]_)
    
    ξ₀ : {n : ℕ} → QH n → QH (suc n)
    ξ₀ = ξ zero
    
    -- Transform a real variable into an apparent one, with an index that will
    -- bind to a quantifier inserted before the resulting proposition.
    -- Free De Bruijn indices will be incremented with this insertion in mind.
    bind : {n : ℕ} → X → Fin (suc n) → QH n → QH (suc n)
    bind x = QHrec' suc (λ {k} _ _ → QH (suc k))
        --(λ i a → atom (Atomic.bind atomic x i a))
        (λ i a → atom (A.r→a x i (A.ξ (toℕ i) a)))
        (λ i → ~_)
        (λ i → _∪_)
        (λ i → [+]_)
        (λ i → [-]_)

    bind₀ : {n : ℕ} → X → QH n → QH (suc n)
    bind₀ x = bind x zero

    [+_]_ : {n : ℕ} → X → QH n → QH n
    [+ x ] p = [+] (bind₀ x p)
    
    [-_]_ : {n : ℕ} → X → QH n → QH n
    [- x ] p = [-] (bind₀ x p)


    TicketSystem : Set₁
    TicketSystem = QH0 → Set

    -- Proofs
    module Proofs (Ticket : TicketSystem) where 

      -- Rules of passage (p.225; the set on p.74 is incomplete)
      data Passage : {n : ℕ} → QH n → QH n → Set where
        pass₁ : {n : ℕ} {Φ : QH (suc n)} →            Passage (~ [+] Φ) ([-] ~ Φ)
        pass₂ : {n : ℕ} {Φ : QH (suc n)} →            Passage (~ [-] Φ) ([+] ~ Φ)
        pass₃ : {n : ℕ} {Φ : QH (suc n)} {p : QH n} → Passage (([+] Φ) ∪ p) ([+] (Φ ∪ (ξ₀ p)))
        pass₄ : {n : ℕ} {Φ : QH (suc n)} {p : QH n} → Passage (p ∪ ([+] Φ)) ([+] ((ξ₀ p) ∪ Φ))
        pass₅ : {n : ℕ} {Φ : QH (suc n)} {p : QH n} → Passage (([-] Φ) ∪ p) ([-] (Φ ∪ (ξ₀ p)))
        pass₆ : {n : ℕ} {Φ : QH (suc n)} {p : QH n} → Passage (p ∪ ([-] Φ)) ([-] ((ξ₀ p) ∪ Φ))
        vice-versa : {n : ℕ} {Φ₁ Φ₂ : QH n} → Passage Φ₁ Φ₂ → Passage Φ₂ Φ₁

      -- Sugar
      SP : {n : ℕ} → QH n → QH n → Set
      SP = Somewhere Passage
      SP⋆ : {n : ℕ} → QH n → QH n → Set
      SP⋆ = SP ⋆

      

      -- See "Rules of Reasoning", p74
      data ProofQH : QH0 → Set1 where
        fromFK : (p : QH0) (e : elementary p)
          → ProofFK (lower p e)
          → ProofQH p
        passage : {n : ℕ} {Φ₁ Φ₂ : QH0} → Somewhere Passage Φ₁ Φ₂
          → ProofQH Φ₁
          → ProofQH Φ₂
        gen₁ : {p : QH0} (x : X)
          → ProofQH p
          → ProofQH ([+ x ] p)
        gen₂ : {p : QH0} (x y : X)
          → ProofQH (sub y x p)
          → ProofQH ([- y ] p)
        simp : {p : QH0}
          → ProofQH (p ∪ p)
          → ProofQH p
        mp : {p q : QH0}
          → ProofQH (p ⊃ q)
          → ProofQH p
          → ProofQH q
        external : {p : QH0}
          → Ticket p
          → ProofQH p


      -- Syntactic sugar.
      infix 10 ⊢_
      ⊢_ : QH0 → Set1
      ⊢_ = ProofQH


    {-
      module NF where

        open import Data.List.NonEmpty

        data Literal (n : ℕ) : Set where
          +_ : Atom n → Literal n
          -_ : Atom n → Literal n

        L : Set → Set
        L = List⁺

        Conj : ℕ → Set
        Conj n = L (Literal n)

        Disj : ℕ → Set
        Disj n = L (Literal n)

        DNF : ℕ → Set
        DNF n = L (Conj n)

        CNF : ℕ → Set
        CNF n = L (Conj n)

        literal-interpret : {n : ℕ} → Literal n → QH n
        literal-interpret (+ a) = atom a
        literal-interpret (- a) = ~ (atom a)

        conj-interpret : {n : ℕ} → Conj n → QH n
        conj-interpret = (foldr₁ _&_) ∘ (map literal-interpret)

        disj-interpret : {n : ℕ} → Conj n → QH n
        disj-interpret = (foldr₁ _∪_) ∘ (map literal-interpret)

        dnf-interpret : {n : ℕ} → DNF n → QH n
        dnf-interpret = (foldr₁ _∪_) ∘ (map conj-interpret)

        cnf-interpret : {n : ℕ} → DNF n → QH n
        cnf-interpret = (foldr₁ _&_) ∘ (map disj-interpret)

        negate : {n : ℕ} → Literal n → Literal n
        negate (+ a) = - a
        negate (- a) = + a

        dual : {n : ℕ} → L (L (Literal n)) → L (L (Literal n))
        dual = map (map negate)

        -- mix [A, B, C] [D, E, F] = [A++D, A++E, A++F, B++D, B++E, ...]
        mix : {n : ℕ} → L (L (Literal n)) → L (L (Literal n)) → L (L (Literal n))
        mix xs ys = concat (map (λ x → map (_⁺++⁺_ x) ys) xs)

        -- Mutually-recursive
        dnf : {n : ℕ} → (p : QH n) → elementary p → DNF n
        cnf : {n : ℕ} → (p : QH n) → elementary p → DNF n

        dnf (atom a) _ = [ [ + a ] ]
        dnf (~ p) e = dual (cnf p e)
        dnf (p₁ ∪ p₂) e = (dnf p₁ (proj₁ e)) ⁺++⁺ (dnf p₂ (proj₂ e))
        dnf ([+] p) ()
        dnf ([-] p) ()

        cnf (atom a) _ = [ [ + a ] ]
        cnf (~ p) e = dual (dnf p e)
        cnf (p₁ ∪ p₂) e = dual (mix (dual (cnf p₁ (proj₁ e))) (dual (cnf p₂ (proj₂ e))))
        cnf ([+] p) ()
        cnf ([-] p) ()

        dnf-works : {n : ℕ} → (p : QH n) → (e : elementary p) → dnf-interpret (dnf p e) ∼ p
        cnf-works : {n : ℕ} → (p : QH n) → (e : elementary p) → cnf-interpret (cnf p e) ∼ p

        dnf-works = {!!}
        cnf-works = {!!}
-}
