
module FirstKind {α} where

  -----------------------
  -- "The First Kind"
  -----------------------

  open import Data.Nat
  open import Data.Vec
  open import Data.Bool
  open import Data.Unit
  open import Data.Empty
  open import Function
  open import Relation.Binary.PropositionalEquality

  infixr 4 _∪_
  infixr 4 _&_
  infixr 5 _⊃_

  data FK (A : Set α) : Set α where
    atom : A → FK A
    ~ : FK A → FK A
    _∪_ : FK A → FK A → FK A

  _⊃_ : ∀{A} → FK A → FK A → FK A
  p ⊃ q = (~ p) ∪ q

  _&_ : ∀{A} → FK A → FK A → FK A
  p & q = ~ (~ p ∪ ~ q)

  data ProofFK {A : Set α} : FK A → Set α where
    ptaut : (p : FK A) → ProofFK (p ∪ p ⊃ p)
    padd : (p q : FK A) → ProofFK (q ⊃ p ∪ q)
    pperm : (p q : FK A) → ProofFK (p ∪ q ⊃ q ∪ p)
    passoc : (p q r : FK A) → ProofFK (p ∪ (q ∪ r) ⊃ (p ∪ q) ∪ r)
    psum : (p q r : FK A) → ProofFK ((q ⊃ r) ⊃ (p ∪ q ⊃ p ∪ r))
    mp : {p q : FK A} → ProofFK (p ⊃ q) → ProofFK p → ProofFK q



  -- Replace atoms with propositions.
  fkSub : ∀{A B} → (A → FK B) → FK A → FK B
  fkSub f (atom x) = f x
  fkSub f (~ p) = ~ (fkSub f p)
  fkSub f (p ∪ q) = (fkSub f p) ∪ (fkSub f q)

  -- fkSub preserves truth.
  fkSubThm : ∀{A B} → {p : FK A} → (f : A → FK B) → ProofFK p → ProofFK (fkSub f p)
  fkSubThm f (ptaut q) = ptaut (fkSub f q)
  fkSubThm f (padd p q) = padd (fkSub f p) (fkSub f q)
  fkSubThm f (pperm p q) = pperm (fkSub f p) (fkSub f q)
  fkSubThm f (passoc p q r) = passoc (fkSub f p) (fkSub f q) (fkSub f r)
  fkSubThm f (psum p q r) = psum (fkSub f p) (fkSub f q) (fkSub f r)
  fkSubThm f (mp pq p) = mp (fkSubThm f pq) (fkSubThm f p)

  
  -- Replace atoms with other atoms.
  fkMap : ∀{A B} → (A → B) → FK A → FK B
  fkMap f = fkSub (atom ∘ f)

  -- fkMap preserves truth.
  fkMapThm : ∀{A B} → {p : FK A} → (f : A → B) → ProofFK p → ProofFK (fkMap f p)
  fkMapThm f = fkSubThm (atom ∘ f)

  -- Assign a "logical value" (Bool) to a proposition, given assignments for the atoms.
  interpret : {A : Set α} → (A → Bool) → FK A → Bool
  interpret iatom (atom x) = iatom x
  interpret iatom (p ∪ q) = interpret iatom p ∨ interpret iatom q
  interpret iatom (~ p) = not (interpret iatom p)

  -- If a proposition is provable, its interpretation is 'true' (regardless of interpretations of atoms).
  provableTrue : {A : Set α} {p : FK A} (iatom : A → Bool) (proof : ProofFK p) → T (interpret iatom p)
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
  provableTrue iatom (mp {p} {q} p⊃q-proof p-proof) with interpret iatom p | provableTrue iatom p-proof | provableTrue iatom p⊃q-proof
  ... | false | () | _
  ... | true | _ | true-p⊃q = true-p⊃q
--  provableTrue iatom (mp {p} {q} p⊃q-proof p-proof) with interpret iatom p | interpret iatom q | provableTrue iatom p-proof | provableTrue iatom p⊃q-proof
--  ... | false | _ | () | _
--  ... | true | false | _ | ()
--  ... | true | true | _ | _ = tt
  
  consistent : {A : Set α} {p : FK A} → (A → Bool) → ProofFK p → ProofFK (~ p) → ⊥
  consistent {p = p} iatom p-proof ~p-proof with interpret iatom p | provableTrue iatom p-proof | provableTrue iatom ~p-proof
  ... | true | _ | ()
  ... | false | () | _
