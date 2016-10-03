
module FirstKind where

  -----------------------
  -- "The First Kind"
  -----------------------

  open import Data.Nat
  --open import Data.Vec
  open import Data.Bool
  open import Data.Unit
  open import Data.Empty
  open import Function
  --open import Relation.Binary.PropositionalEquality
  open import Agda.Primitive

  infixr 7 ~_
  infixr 6 _&_
  infixr 5 _∪_
  infixr 4 _≣_
  infixr 3 _⊃_

  data FK {α : Level} (A : Set α) : Set α where
    atom : A → FK A
    ~_ : FK A → FK A
    _∪_ : FK A → FK A → FK A

  _⊃_ : ∀{α} {A : Set α} → FK A → FK A → FK A
  p ⊃ q = (~ p) ∪ q

  _&_ : ∀{α} {A : Set α} → FK A → FK A → FK A
  p & q = ~ (~ p ∪ ~ q)

  _≣_ : ∀{α} {A : Set α} → FK A → FK A → FK A
  p ≣ q = (p ⊃ q) & (q ⊃ p)

  data ProofFK {α : Level} {A : Set α} : FK A → Set α where
    ptaut : (p : FK A) → ProofFK (p ∪ p ⊃ p)
    padd : (p q : FK A) → ProofFK (q ⊃ p ∪ q)
    pperm : (p q : FK A) → ProofFK (p ∪ q ⊃ q ∪ p)
    passoc : (p q r : FK A) → ProofFK (p ∪ (q ∪ r) ⊃ q ∪ (p ∪ r))
    psum : (p q r : FK A) → ProofFK ((q ⊃ r) ⊃ (p ∪ q ⊃ p ∪ r))
    simp : {p q : FK A} → ProofFK (p ⊃ q) → ProofFK p → ProofFK q


{-
    ptaut : ~ (p ∪ p) ∪ p
    padd : ~ q ∪ (p ∪ q)
    pperm : ~ (p ∪ q) ∪ (q ∪ p)
    passoc : ~ (p ∪ (q ∪ r)) ∪ (

    If we want ~ ~ p ⊃ p for *any* p, the last part of the proof must be mp.
    
    If it's mp, then we're applying simp to something : X ⊃ (~ ~ p ⊃ p), and X.
    
-}

  -- Replace atoms with propositions.
  fkSub : ∀{α β} {A : Set α} {B : Set β} → (A → FK B) → FK A → FK B
  fkSub f (atom x) = f x
  fkSub f (~ p) = ~ (fkSub f p)
  fkSub f (p ∪ q) = (fkSub f p) ∪ (fkSub f q)

  -- fkSub preserves truth.
  fkSubThm : ∀{α β} {A : Set α} {B : Set β} → {p : FK A} → (f : A → FK B) → ProofFK p → ProofFK (fkSub f p)
  fkSubThm f (ptaut q) = ptaut (fkSub f q)
  fkSubThm f (padd p q) = padd (fkSub f p) (fkSub f q)
  fkSubThm f (pperm p q) = pperm (fkSub f p) (fkSub f q)
  fkSubThm f (passoc p q r) = passoc (fkSub f p) (fkSub f q) (fkSub f r)
  fkSubThm f (psum p q r) = psum (fkSub f p) (fkSub f q) (fkSub f r)
  fkSubThm f (simp pq p) = simp (fkSubThm f pq) (fkSubThm f p)

  
  -- Replace atoms with other atoms.
  fkMap : ∀{α β} {A : Set α} {B : Set β} → (A → B) → FK A → FK B
  fkMap f = fkSub (atom ∘ f)

  -- fkMap preserves truth.
  fkMapThm : ∀{α β} {A : Set α} {B : Set β} → {p : FK A} → (f : A → B) → ProofFK p → ProofFK (fkMap f p)
  fkMapThm f = fkSubThm (atom ∘ f)

  -- Assign a "logical value" (Bool) to a proposition, given assignments for the atoms.
  interpret : ∀{α} {A : Set α} → (A → Bool) → FK A → Bool
  interpret iatom (atom x) = iatom x
  interpret iatom (p ∪ q) = interpret iatom p ∨ interpret iatom q
  interpret iatom (~ p) = not (interpret iatom p)

  -- If a proposition is provable, its interpretation is 'true' (regardless of interpretations of atoms).
  provableTrue : ∀{α} {A : Set α} {p : FK A} (iatom : A → Bool) (proof : ProofFK p) → T (interpret iatom p)
  provableTrue iatom (ptaut p) with interpret iatom p
  ... | true = tt
  ... | false = tt
  provableTrue iatom (padd p q) with interpret iatom p | interpret iatom q
  ... | true | true = tt
  ... | true | false = tt
  ... | false | true = tt
  ... | false | false = tt
  provableTrue iatom (pperm p q) with interpret iatom p | interpret iatom q
  ... | true | true = tt
  ... | true | false = tt
  ... | false | true = tt
  ... | false | false = tt
  provableTrue iatom (passoc p q r) with interpret iatom p | interpret iatom q | interpret iatom r
  ... | true | true | true = tt
  ... | true | true | false = tt
  ... | true | false | true = tt
  ... | true | false | false = tt
  ... | false | true | true = tt
  ... | false | true | false = tt
  ... | false | false | true = tt
  ... | false | false | false = tt
  provableTrue iatom (psum p q r) with interpret iatom p | interpret iatom q | interpret iatom r
  ... | true | true | true = tt
  ... | true | true | false = tt
  ... | true | false | true = tt
  ... | true | false | false = tt
  ... | false | true | true = tt
  ... | false | true | false = tt
  ... | false | false | true = tt
  ... | false | false | false = tt
  provableTrue iatom (simp {p} {q} p⊃q-proof p-proof) with interpret iatom p | provableTrue iatom p-proof | provableTrue iatom p⊃q-proof
  ... | false | () | _
  ... | true | _ | true-p⊃q = true-p⊃q
  
  consistent : ∀{α} {A : Set α} {p : FK A} → ProofFK p → ProofFK (~ p) → ⊥
  consistent {p = p} p-proof ~p-proof with interpret (const false) p | provableTrue (const false) p-proof | provableTrue (const false) ~p-proof
  ... | true | _ | ()
  ... | false | () | _



  _≣!_ : ∀{α} {A : Set α} → FK A → FK A → Set α
  p ≣! q = ProofFK (p ≣ q)

  module OneKind {α : Level} (A : Set α) where

    -- ⊃ is reflexive and transitive.
    ⊃-refl : (p : FK A) → ProofFK (p ⊃ p)
    ⊃-refl p = (simp (simp (psum (~ p) (p ∪ p) p) (ptaut p)) (padd p p))

    ⊃-trans : (p q r : FK A) → ProofFK ((p ⊃ q) ⊃ ((q ⊃ r) ⊃ (p ⊃ r)))
    ⊃-trans p q r = simp (passoc (~ (q ⊃ r)) (~ (p ⊃ q)) (p ⊃ r)) (psum (~ p) q r)

    -- Compose two implications; a convenient weakening of ⊃-trans.
    _⊃⊃_ : {p q r : FK A} → ProofFK (p ⊃ q) → ProofFK (q ⊃ r) → ProofFK (p ⊃ r)
    _⊃⊃_ {p = p} {q = q} {r = r} pq qr = simp (simp (⊃-trans p q r) pq) qr

    -- The law of excluded middle, in two flavors for convenience.
    lem₁ : (p : FK A) → ProofFK (~ p ∪ p)
    lem₁ = ⊃-refl
  
    lem₂ : (p : FK A) → ProofFK (p ∪ ~ p)
    lem₂ p = simp (pperm (~ p) p) (lem₁ p)

    -- Double negation introduction and elimination.
    ~~-intro : (p : FK A) → ProofFK (p ⊃ ~ ~ p)
    ~~-intro p = lem₂ (~ p)

    ~~-elim : (p : FK A) → ProofFK ((~ ~ p) ⊃ p)
    ~~-elim p = simp
      (pperm p (~ ~ ~ p))
      (simp
        (simp
          (psum p (~ p) (~ ~ ~ p))
          (~~-intro (~ p)))
        (lem₂ p))

    -- Contraposition, and a convenient weakened helper.
    contra : (p q : FK A) → ProofFK ((p ⊃ q) ⊃ (~ q ⊃ ~ p))
    contra p q = (simp (psum (~ p) q (~ ~ q)) (~~-intro q)) ⊃⊃ (pperm (~ p) (~ ~ q))

    contra' : (p q : FK A) → ProofFK (p ⊃ q) → ProofFK (~ q ⊃ ~ p)
    contra' p q = simp (contra p q)

    -- A flipped version of padd, for convenience.
    padd' : (p q : FK A) → ProofFK (p ⊃ p ∪ q)
    padd' p q = (padd q p) ⊃⊃ (pperm q p)

    -- A flipped version of psum, for convenience
    --psum' : (p q r : FK A) → ProofFK ((q ⊃ r) ⊃ ((q ∪ p) ⊃ (r ∪ p)))
    --psum' p q r = {!!}

    -- Some properties of &.
    &-refl : (p : FK A) → ProofFK (p ⊃ p & p)
    &-refl p = simp
      (simp
        (psum (~ p) (~ ~ p) (p & p))
        (simp
          (contra (~ p ∪ ~ p) (~ p))
          (ptaut (~ p))))
      (lem₂ (~ p))

    &-sym : (p q : FK A) → ProofFK (p & q ⊃ q & p)
    &-sym p q = simp
      (pperm (q & p) (~ (p & q)))
      ((pperm (~ q) (~ p)) ⊃⊃ (~~-intro (~ p ∪ ~ q)))

    &-elim₂ : (p q : FK A) → ProofFK (p & q ⊃ q)
    &-elim₂ p q = simp
      (pperm q (~ (p & q)))
      (simp
        (simp
          (psum q (~ q) (~ (p & q)))
          ((padd (~ p) (~ q)) ⊃⊃ (~~-intro (~ p ∪ ~ q))))
        (lem₂ q))

    &-elim₁ : (p q : FK A) → ProofFK (p & q ⊃ p)
    &-elim₁ p q = (&-sym p q) ⊃⊃ (&-elim₂ q p)

    &-intro : (p q : FK A) → ProofFK (p ⊃ (q ⊃ (p & q)))
    &-intro p q = simp
      (simp
        (psum (~ p) (p & q ∪ ~ q) (~ q ∪ p & q))
        (pperm (p & q) (~ q)))
      (simp
        (passoc (p & q) (~ p) (~ q))
        (lem₁ (~ p ∪ ~ q)))

    -- Conveniences
    &-elim₁' : {p q : FK A} → ProofFK (p & q) → ProofFK p
    &-elim₁' {p = p} {q = q} = simp (&-elim₁ p q)
    
    &-elim₂' : {p q : FK A} → ProofFK (p & q) → ProofFK q
    &-elim₂' {p = p} {q = q} = simp (&-elim₂ p q)

    _&!_ : {p q : FK A} → ProofFK p → ProofFK q → ProofFK (p & q)
    _&!_ {p = p} {q = q} p! q! = simp (simp (&-intro p q) p!) q!    

    


    -- Properties of equivalence
    ≣-refl : (p : FK A) → ProofFK (p ≣ p)
    ≣-refl p = (⊃-refl p) &! (⊃-refl p)

    ≣-sym : (p q : FK A) → ProofFK (p ≣ q ⊃ q ≣ p)
    ≣-sym p q = &-sym (p ⊃ q) (q ⊃ p)

    --≣-trans : (p q r : FK A) → ProofFK (p ≣ q ⊃ (q ≣ r ⊃ p ≣ r))
    --≣-trans p q r = {!!}

    ≣-supersym : (p q : FK A) → ProofFK ((p ≣ q) ≣ (q ≣ p))
    ≣-supersym p q = (≣-sym p q) &! (≣-sym q p)

    -- Probably not.
    --hmm : (p q : FK A) → (ProofFK p → ProofFK q) → ProofFK (p ⊃ q)
    --hmm p q f = {!!}


    module NF where

      open import Data.List.NonEmpty

      data Literal : Set α where
        +_ : A → Literal
        -_ : A → Literal

      L : Set α → Set α
      L = List⁺

      Conj : Set α
      Conj = L Literal

      Disj : Set α
      Disj = L Literal

      DNF : Set α
      DNF = L Disj

      CNF : Set α
      CNF = L Conj

      literal-interpret : Literal → FK A
      literal-interpret (+ a) = atom a
      literal-interpret (- a) = ~ (atom a)

      conj-interpret : Conj → FK A
      conj-interpret = (foldr₁ _&_) ∘ (map literal-interpret)

      disj-interpret : Conj → FK A
      disj-interpret = (foldr₁ _∪_) ∘ (map literal-interpret)

      dnf-interpret : DNF → FK A
      dnf-interpret = (foldr₁ _∪_) ∘ (map conj-interpret)

      cnf-interpret : CNF → FK A
      cnf-interpret = (foldr₁ _&_) ∘ (map disj-interpret)

      negate : Literal → Literal
      negate (+ a) = - a
      negate (- a) = + a

      dual : L (L Literal) → L (L Literal)
      dual = map (map negate)

      -- mix [A, B, C] [D, E, F] = [A++D, A++E, A++F, B++D, B++E, ...]
      mix : L (L Literal) → L (L Literal) → L (L Literal)
      mix xs ys = concat (map (λ x → map (_⁺++⁺_ x) ys) xs)

      -- Mutually-recursive
      dnf : (p : FK A) → DNF
      cnf : (p : FK A) → CNF

      dnf (atom a) = [ [ + a ] ]
      dnf (~ p) = dual (cnf p)
      dnf (p₁ ∪ p₂) = (dnf p₁) ⁺++⁺ (dnf p₂)

      cnf (atom a) = [ [ + a ] ]
      cnf (~ p) = dual (dnf p)
      cnf (p₁ ∪ p₂) = dual (mix (dual (cnf p₁)) (dual (cnf p₂)))

      --dnf-works : (p : FK A) → dnf-interpret (dnf p) ≣! p
      --cnf-works : (p : FK A) → cnf-interpret (cnf p) ≣! p

      --dnf-works = {!!}
      --cnf-works = {!!}

  open OneKind public
