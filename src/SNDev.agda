open import Agda.Primitive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module SNDev {X : Set} {_X≟_ : Decidable {A = X} _≡_ } where
  open import Common
  open import Data.Nat using (ℕ ; zero ; suc) renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_)
  open import Data.Nat.Properties.Simple using (+-comm ; +-assoc)

  module QFree where
    open import Data.Bool using (Bool ; true ; false ; _∨_ ; _∧_ ; not ; if_then_else_ ; T) renaming (_≟_ to _B≟_)
    open import FirstKind
    open import SucNat.Base {X = X}
    open import SucNat.FK {X = X}
    open import SucNat.DecVar {X = X} {_≟_ = _X≟_}
    open import Data.List using (List ; [] ; _∷_ ; foldr)


    open Proofs FKAxioms

    -- Quantifier-free propositions, where atoms are of the type in SucNat.Base (S^k zero or S^k x)e
    QF : Set
    QF = FK (Atom zero)

    -- A factor for DNF, i.e. an atom or its negation.
    data Factor : Set where
      +_ : Atom zero → Factor   -- an atom ("positive" occurrence)
      -_ : Atom zero → Factor   -- the negation of an atom ("negative" occurrence)

    0=0 : Factor
    0=0 = + (theℕ zero == theℕ zero)

    0≠0 : Factor
    0≠0 = - (theℕ zero == theℕ zero)

    --------------------------------------------
    -- EVALUATING QF PROPOSITIONS (SEMANTICS) --
    --------------------------------------------
    
    evalBase : (X → ℕ) → Base zero → ℕ
    evalBase e (real x) = e x
    evalBase e (appa ())
    evalBase e tzero = zero

    evalTerm : (X → ℕ) → Term zero → ℕ
    evalTerm e (S k base) = k ℕ+ (evalBase e base)

    evalAtom : (X → ℕ) → Atom zero → Bool
    evalAtom e (t₁ == t₂) = ⌊ (evalTerm e t₁) ℕ≟ (evalTerm e t₂) ⌋

    -- Evaluating a quantifier-free proposition ⇒ use the evaluation in FirstKind.agda, giving it the above means for evaluating atoms.
    evalQF : (X → ℕ) → QF → Bool
    evalQF e = eval (evalAtom e)

    -- Handy lemmas...
    evalTerm-tsuc : (e : X → ℕ) (t : Term zero) → evalTerm e (tsuc t) ≡ suc (evalTerm e t)
    evalTerm-tsuc e (S k b) = refl

    evalTerm-+ℕ : (e : X → ℕ) (t : Term zero) (a : ℕ) → evalTerm e (t +ℕ a) ≡ a ℕ+ (evalTerm e t)
    evalTerm-+ℕ e (S k b) a with evalBase e b
    ... | ⟦b⟧ = +-assoc a k ⟦b⟧

    suc≡suc : {x y : ℕ} → suc x ≡ suc y → x ≡ y
    suc≡suc {zero} {.zero} refl = refl
    suc≡suc {suc m} {.(suc m)} refl = refl

    x≠x+1+a : (x a : ℕ) → ¬ (x ≡ x ℕ+ (suc a))
    x≠x+1+a zero a = λ ()
    x≠x+1+a (suc x) a = (x≠x+1+a x a) ∘ suc≡suc

    x≠1+a+x : (x a : ℕ) → ¬ (x ≡ (suc a) ℕ+ x)
    x≠1+a+x x a eq = x≠x+1+a x a (trans eq (+-comm (suc a) x))

    -- The axioms are valid.
    happy : {p : FK (Atom zero)} → (e : X → ℕ) → FKAxioms p → T (eval (evalAtom e) p)
    happy e (h1 x) with evalTerm e x
    happy e (h1 x) | ⟦x⟧ with ⟦x⟧ ℕ≟ ⟦x⟧
    happy e (h1 x) | ⟦x⟧ | (yes refl) = tt
    happy e (h1 x) | ⟦x⟧ | (no  fail)  = contradiction refl fail
    happy e (h2 x y) with (evalTerm e x) | (evalTerm e y) | (evalTerm e x) ℕ≟ (evalTerm e y) | (evalTerm e y) ℕ≟ (evalTerm e x)
    happy e (h2 x y) | ⟦x⟧ | .⟦x⟧ | yes refl | yes refl = tt
    happy e (h2 x y) | ⟦x⟧ | ⟦y⟧  | no  neq  | no  neq' = tt
    happy e (h2 x y) | ⟦x⟧ | .⟦x⟧ | yes refl | no  fail = contradiction refl fail
    happy e (h2 x y) | ⟦x⟧ | .⟦x⟧ | no  fail | yes refl = contradiction refl fail
    happy e (h3 x y z) with (evalTerm e x) | (evalTerm e y) | (evalTerm e z) | (evalTerm e x) ℕ≟ (evalTerm e y) | (evalTerm e y) ℕ≟ (evalTerm e z) | (evalTerm e x) ℕ≟ (evalTerm e z)
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | no _  | no _  | no _  = tt
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | no _  | no _  | yes _ = tt
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | no _  | yes _ | no _  = tt
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | no _  | yes _ | yes _ = tt
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | yes _ | no _  | no _  = tt
    happy e (h3 x y z) | ⟦x⟧ | ⟦y⟧ | ⟦z⟧ | yes _ | no _  | yes _ = tt
    happy e (h3 x y z) | ⟦x⟧ | .⟦x⟧ | .⟦x⟧ | yes refl | yes refl | no fail  = contradiction refl fail
    happy e (h3 x y z) | ⟦x⟧ | .⟦x⟧ | .⟦x⟧ | yes refl | yes refl | yes _ = tt
    happy e (h4 x y) with evalTerm e x | evalTerm e y | evalTerm e (tsuc x) | evalTerm e (tsuc y) | evalTerm-tsuc e x | evalTerm-tsuc e y | (evalTerm e x) ℕ≟ (evalTerm e y)
    happy e (h4 x y) | ⟦x⟧ | .⟦x⟧ | .(suc ⟦x⟧) | .(suc ⟦x⟧) | refl | refl | yes refl with (suc ⟦x⟧) ℕ≟ (suc ⟦x⟧)
    happy e (h4 x y) | ⟦x⟧ | .⟦x⟧ | .(suc ⟦x⟧) | .(suc ⟦x⟧) | refl | refl | yes refl | yes refl = tt
    happy e (h4 x y) | ⟦x⟧ | .⟦x⟧ | .(suc ⟦x⟧) | .(suc ⟦x⟧) | refl | refl | yes refl | no  fail = contradiction refl fail
    happy e (h4 x y) | ⟦x⟧ |  ⟦y⟧ | .(suc ⟦x⟧) | .(suc ⟦y⟧) | refl | refl | no noteq with (suc ⟦x⟧) ℕ≟ (suc ⟦y⟧)
    happy e (h4 x y) | ⟦x⟧ |  ⟦y⟧ | .(suc ⟦x⟧) | .(suc ⟦y⟧) | refl | refl | no noteq | yes suceq = contradiction suceq (noteq ∘ suc≡suc)
    happy e (h4 x y) | ⟦x⟧ |  ⟦y⟧ | .(suc ⟦x⟧) | .(suc ⟦y⟧) | refl | refl | no noteq | no  nope = tt
    happy e (h5 x) with evalTerm e x | evalTerm e (tsuc x) | evalTerm-tsuc e x
    happy e (h5 x) | ⟦x⟧ | .(suc ⟦x⟧) | refl = tt
    happy e (h6 x a) with evalTerm e x | evalTerm e (x +ℕ (suc a)) | evalTerm-+ℕ e x (suc a) 
    happy e (h6 x a) | ⟦x⟧ | .((suc a) ℕ+ ⟦x⟧) | refl with ⟦x⟧ ℕ≟ (suc a) ℕ+ ⟦x⟧
    happy e (h6 x a) | ⟦x⟧ | .((suc a) ℕ+ ⟦x⟧) | refl | yes itdoes = contradiction itdoes (x≠1+a+x ⟦x⟧ a)
    happy e (h6 x a) | ⟦x⟧ | .((suc a) ℕ+ ⟦x⟧) | refl | no _ = tt

    -- P₁ ≡ P₂ → ⟦P₁⟧ₑ ≡ ⟦P₂⟧ₑ
    -- Logically equivalence propositions have equivalent (read: identical) semantics.
    evalQF-≣ : {p₁ p₂ : QF} → (e : X → ℕ) → ⊢ p₁ ≣ p₂ → evalQF e p₁ ≡ evalQF e p₂
    evalQF-≣ {p₁} {p₂} e eq with evalQF e p₁ | evalQF e p₂ | provableTrue (evalAtom e) (happy e) (&-elim₁' eq) | provableTrue (evalAtom e) (happy e) (&-elim₂' eq)
    ... | true  | true  | 1⇒2 | 2⇒1 = refl
    ... | false | false | 1⇒2 | 2⇒1 = refl
    ... | true  | false | 1⇒2 | 2⇒1 = ⊥-elim 1⇒2
    ... | false | true  | 1⇒2 | 2⇒1 = ⊥-elim 2⇒1

    -- If P ≡ P', then (A & P) ≡ (A & P')
    &-≣ : {P P' : QF} (A : QF) → ⊢ P ≣ P' → ⊢ (A & P) ≣ (A & P')
    &-≣ {P} {P'} A eq = {!!}

    -- A variable mapping that satisfies a quantifier-free proposition.
    Sat : QF → Set
    Sat p = Σ (X → ℕ) (λ e → T (evalQF e p))

    -- Various operations on Factors
    module F where
      _∈_ : X → Factor → Set
      x ∈ (+ a) = x A.∈ a
      x ∈ (- a) = x A.∈ a
      
      _∈?_ : (x : X) → (f : Factor) → Dec (x ∈ f)
      x ∈? (+ a) = x A.∈? a
      x ∈? (- a) = x A.∈? a

      _∉_ : X → Factor → Set
      x ∉ f = ¬ (x ∈ f)

      _∉?_ : (x : X) → (f : Factor) → Dec (x ∉ f)
      x ∉? f = ¬? (x ∈? f)

      _∈L_ : X → Factor → Set
      x ∈L (+ (t₁ == t₂)) = x T.∈ t₁
      x ∈L (- (t₁ == t₂)) = x T.∈ t₁
      
      _∈L?_ : (x : X) → (f : Factor) → Dec (x ∈L f)
      x ∈L? (+ (t₁ == t₂)) = x T.∈? t₁
      x ∈L? (- (t₁ == t₂)) = x T.∈? t₁

      _∉L_ : X → Factor → Set
      x ∉L f = ¬ (x ∈L f)

      _∉L?_ : (x : X) → (f : Factor) → Dec (x ∉L f)
      x ∉L? f = ¬? (x ∈L? f)      

      interpret : Factor → QF
      interpret (+ a) = atom a
      interpret (- a) = ~ (atom a)

    -- Various operations of products of factors
    module P where

      interpret : List Factor → QF
      interpret [] = F.interpret 0=0
      interpret (f ∷ fs) = (F.interpret f) & (interpret fs)

    -- Various operations on sums of products of factors (i.e., dnf)
    module SoP where

      interpret : List (List Factor) → QF
      interpret [] = F.interpret 0≠0
      interpret (p ∷ ps) = (P.interpret p) ∪ (interpret ps)

    -- Helpful list operations
    module L {A : Set} where
      data _∈_ : A → List A → Set where
        here : (a : A) → (xs : List A) → a ∈ (a ∷ xs)
        there : {a : A} {xs : List A} (x : A) → a ∈ xs → a ∈ (x ∷ xs)

      remove : {a : A} {xs : List A} → a ∈ xs → List A
      remove (here a xs) = xs
      remove (there x a∈xs) = x ∷ remove a∈xs

      toFront : {a : A} {xs : List A} → a ∈ xs → List A
      toFront {a = a} it = a ∷ remove it

{-
      -- pull it to the front... slowly
      pull : {a : A} {xs : List A} → a ∈ xs → List A
      pull (here a xs) = a ∷ xs
      pull (there x later) with later | pull later
      ... | here a ys  | .(a ∷ ys = a ∷ x ∷ ys
      ... | there y ys | .y ∷ zs = y ∷ x ∷ ys

      -- it's actually there
      pullWorks : {a : A} {xs : List A} → (it : a ∈ xs) → pull it ≡ a ∷ remove it
      pullWorks (here a xs) = refl
      pullWorks (there x later) = ?
-}

{-
      remove' : {a : A} → (xs : List A) → a ∈ xs → List A
      remove' .(a ∷ xs) (here a xs) = xs
      remove' (.x ∷ xs) (there x a∈xs) = x ∷ (remove' xs a∈xs)
-}
    open L using (here ; there)

    -- Canonical form...
    module Canonical where

      module KindAsType where
        data Kind : Set where
          kind₀ : Kind
          kind₁ : Kind
          kind₂ : Kind
          kind₃ : Kind

        -- ... deriving Eq ...
        _≟_ : (k₁ k₂ : Kind) → Dec (k₁ ≡ k₂)
        kind₀ ≟ kind₀ = yes refl
        kind₀ ≟ kind₁ = no (λ ())
        kind₀ ≟ kind₂ = no (λ ())
        kind₀ ≟ kind₃ = no (λ ())
        kind₁ ≟ kind₀ = no (λ ())
        kind₁ ≟ kind₁ = yes refl
        kind₁ ≟ kind₂ = no (λ ())
        kind₁ ≟ kind₃ = no (λ ())
        kind₂ ≟ kind₀ = no (λ ())
        kind₂ ≟ kind₁ = no (λ ())
        kind₂ ≟ kind₂ = yes refl
        kind₂ ≟ kind₃ = no (λ ())
        kind₃ ≟ kind₀ = no (λ ())
        kind₃ ≟ kind₁ = no (λ ())
        kind₃ ≟ kind₂ = no (λ ())
        kind₃ ≟ kind₃ = yes refl

      open KindAsType renaming (_≟_ to _K≟_)


      -- A canonical factor takes one of these forms.
      data CanonicalFactor : Set where
        form₁ : (x : X) (a : ℕ) → CanonicalFactor     -- x = a
        form₂ : (z y : X) (b : ℕ) → CanonicalFactor   -- z = y + b
        form₃ : (y₁ y₂ : X) (b : ℕ) → CanonicalFactor -- y₁ ≠ y₂ + b
        form₄ : (y : X) (d : ℕ) → CanonicalFactor     -- y ≠ d
        
      -- Operations on canonical factors.
      module CF where

        _∈_ : X → CanonicalFactor → Set
        _∈_ = {!!}

        _∈?_ : (x : X) (cf : CanonicalFactor) → Dec (x ∈ cf)
        _∈?_ = {!!}

        toFactor : CanonicalFactor → Factor 
        toFactor (form₁ x a)     = + (S zero (real x)  == theℕ a)        -- x = a
        toFactor (form₂ z y b)   = + (S zero (real z)  == S b (real y))  -- z = y + b
        toFactor (form₃ y₁ y₂ b) = - (S zero (real y₁) == S b (real y₂)) -- y₁ ≠ y₂ + b
        toFactor (form₄ y d)     = - (S zero (real y)  == theℕ d)        -- y₁ ≠ d

        interpret : CanonicalFactor → QF
        interpret = F.interpret ∘ toFactor

        kindOf : X → CanonicalFactor → Kind
        kindOf w (form₁ x a) = if ⌊ w X≟ x ⌋ then kind₁ else kind₀
        kindOf w (form₂ z y b) = if ⌊ w X≟ z ⌋ then kind₃ else if ⌊ w X≟ y ⌋ then kind₂ else kind₀
        kindOf w (form₃ y₁ y₂ b) = if ⌊ w X≟ y₁ ⌋ then kind₂ else if ⌊ w X≟ y₂ ⌋ then kind₂ else kind₀
        kindOf w (form₄ y d) = if ⌊ w X≟ y ⌋ then kind₂ else kind₀

        kind₀-or : Kind → X → CanonicalFactor → Set
        kind₀-or k x f = (kindOf x f ≡ kind₀) ⊎ (kindOf x f ≡ k)

        -- Agreement between variable use (particularly, the variable 'kind's)  in two CanonicalFactors.
        -- This is decidable, but 1. we don't need that and 2. this form is easier to work with than Bool.
        -- Note: symmetric.
        -- TODO: a little unsure about inequalities and the variable indexes, see p118.
        playsNice : CanonicalFactor → CanonicalFactor → Set
        playsNice (form₁ x a) f     = kindOf x f ≡ kind₀
        playsNice (form₂ z y b) f   = (kindOf z f ≡ kind₀) × (kind₀-or kind₂ y f)
        playsNice (form₃ y₁ y₂ b) f = (kind₀-or kind₂ y₁ f) × (kind₀-or kind₂ y₂ f)
        playsNice (form₄ y d) f     = kind₀-or kind₂ y f

      -- Operations on products of canonical factors, and canonical products (the former with additional restrictions)
      module CProd where

        interpret : List CanonicalFactor → QF
        interpret [] = F.interpret 0=0
        interpret (f ∷ fs) = (CF.interpret f) & (interpret fs)

        -- Agreement between variable use in one CF and every [other] CF in a product.
        playsNice : CanonicalFactor → List CanonicalFactor → Set
        playsNice _ [] = ⊤
        playsNice cf (f ∷ fs) = (CF.playsNice cf f) × (playsNice cf fs)

        -- A canonical product: each CF plays nicely with those after it.
        -- Note: since playing nicely is symmetric, this means each CF plays nice with every other CF in the entire product.
        -- Hence, this property is invariant under permutation.
        isCanonicalProduct : List CanonicalFactor → Set
        isCanonicalProduct [] = ⊤
        isCanonicalProduct (f ∷ fs) = (playsNice f fs) × (isCanonicalProduct fs)

        {-
        record CanonicalProduct : Set where
          field
            prod : List CanonicalFactor
            canon : isCanonicalProduct prod
        -}
        
        _∈_ : X → List CanonicalFactor → Set
        x ∈ [] = ⊥
        x ∈ (cf ∷ cfs) = x CF.∈ cf ⊎ x ∈ cfs

        _∈?_ : (x : X) (cfs : List CanonicalFactor) → Dec (x ∈ cfs)
        x ∈? [] = no (λ ())
        x ∈? (cf ∷ cfs) = x CF.∈? cf ⊎-dec x ∈? cfs

        module Finders where
          -- Find the first factor containing a given variable.
          find : (x : X) (cfs : List CanonicalFactor) → x ∈ cfs → Σ CanonicalFactor (λ cf → (x CF.∈ cf) × (cf L.∈ cfs))
          find = {!!}

          -- If a factor plays nicely with a product, removing any factor in the product preserves this.
          playsNice-remove : {rm : CanonicalFactor} {cfs : List CanonicalFactor} (cf : CanonicalFactor) (it : rm L.∈ cfs)
            → playsNice cf cfs
            → playsNice cf (L.remove it)
          playsNice-remove cf (here _ rest) (_ , playsNiceRest) = playsNiceRest
          playsNice-remove cf (there x later) (playsNiceX , playsNiceRest) = (playsNiceX , playsNice-remove cf later playsNiceRest)

          removeOk : {cf : CanonicalFactor} {cfs : List CanonicalFactor} → (it : cf L.∈ cfs) → isCanonicalProduct cfs → isCanonicalProduct (L.remove it)
          removeOk (here _ rest) (_ , restCanonical) = restCanonical
          removeOk (there cf later) (cfPlaysNice , restCanonical) = (playsNice-remove cf later cfPlaysNice , removeOk later restCanonical)

          toFrontOk : {cf : CanonicalFactor} {cfs : List CanonicalFactor} (it : cf L.∈ cfs) → isCanonicalProduct cfs → isCanonicalProduct (L.toFront it)
          toFrontOk it pn = (? , removeOk it pn)

          --pull : (x : X) (cfs : List CanonicalFactor) → x ∈ cfs → (

        

        -- Add a factor to a list of canonical factors, maintaining equivalence and keeping the whole thing canonical.
        addFactor : Factor → List CanonicalFactor → List CanonicalFactor
        addFactor = {!!}

        -- addFactor keeps things properly canonical.
        addFactor-canonical : (f : Factor) (cfs : List CanonicalFactor) → isCanonicalProduct (cfs) → isCanonicalProduct (addFactor f cfs)
        addFactor-canonical = {!!}

        -- addFactor maintains equivalence.
        addFactor-equiv : (f : Factor) (cfs : List CanonicalFactor) → ⊢ (interpret (addFactor f cfs)) ≣ ((F.interpret f) & (interpret cfs))
        addFactor-equiv = {!!}

        -- Turn a product into a canonical product using the above.
        toCP : List Factor → List CanonicalFactor
        toCP = foldr (λ f cfs → addFactor f cfs) []

        -- It's indeed canonical.
        toCP-canonical : (p : List Factor) → isCanonicalProduct (toCP p)
        toCP-canonical [] = tt
        toCP-canonical (f ∷ fs) = addFactor-canonical f (toCP fs) (toCP-canonical fs)

        -- And it's equivalent to the original.
        toCP-equiv : (p : List Factor) → ⊢ (interpret (toCP p)) ≣ (P.interpret p)
        toCP-equiv [] = ≣-refl (F.interpret 0=0)
        toCP-equiv (f ∷ fs) = ≣-trans' (addFactor-equiv f (toCP fs)) (&-≣ (F.interpret f) (toCP-equiv fs))
      
        falseOrSatCP : (cp : List CanonicalFactor) → isCanonicalProduct cp → (⊢ ~ (interpret cp)) ⊎ (Sat (interpret cp))
        falseOrSatCP cp isCP = {!!}

        falseOrSat : (p : List Factor) → (⊢ ~ (P.interpret p)) ⊎ (Sat (P.interpret p))
        falseOrSat p with falseOrSatCP (toCP p) (toCP-canonical p)
        ... | inj₁ ⊢~cp = inj₁ (impl (contra' (&-elim₂' (toCP-equiv p))) ⊢~cp )
        ... | inj₂ (sys , ⟦cp⟧) = inj₂ ((sys , subst T (evalQF-≣ sys (toCP-equiv p)) ⟦cp⟧ ))

      -- Operations on/about canonical form (sum of canonical products)
      module CForm where

        -- Interpret our canonical form (dnf on CanonicalFactors).
        interpret : List (List CanonicalFactor) → QF
        interpret [] = F.interpret 0≠0
        interpret (cp ∷ cps) = (CProd.interpret cp) ∪ (interpret cps)
        
        -- Turn a sum of products into a sum of canonical products.
        dnf⇒CanonicalForm : List (List Factor) → List (List CanonicalFactor)
        dnf⇒CanonicalForm = Data.List.map CProd.toCP

        {-
        falseOrSatCForm : (dnf : List (List Factor)) → (⊢ ~ (SoP.interpret dnf)) ⊎ (Sat (SoP.interpret dnf))
        falseOrSatCForm [] = {!!}
        falseOrSatCForm ( = ?
        -}
        
      {-
      falseOrSat : (p : QF) → (⊢ ~ p) ⊎ (Σ (X → ℕ) (λ f → T (evalQF f p)))
        
      trueOrCounter : (p : QF) → (⊢ p) ⊎ (Σ (X → ℕ) (λ f → T (not (evalQF f p))))
      trueOrCounter p with falseOrSat (~ p)
      ... | inj₁ ⊢~~p = inj₁ (impl (~~-elim p) ⊢~~p)
      ... | inj₂ (sys , ⟦~p⟧) = inj₂ (sys , ⟦~p⟧)
      -}

  module QElim where

    open QFree
    
