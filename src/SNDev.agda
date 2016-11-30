open import Agda.Primitive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module SNDev {X : Set} {_X≟_ : Decidable {A = X} _≡_ } where
  open import Common
  open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _≤?_ ; _∸_ ) renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_)
  open import Data.Nat.Properties.Simple using (+-comm ; +-assoc)

  module QFree where
    open import Data.Bool using (Bool ; true ; false ; _∨_ ; _∧_ ; not ; if_then_else_ ; T) renaming (_≟_ to _B≟_)
    open import FirstKind
    open import SucNat.Base {X = X}
    open import SucNat.FK {X = X}
    open import SucNat.DecVar {X = X} {_≟_ = _X≟_}
    open import Data.List using (List ; [] ; _∷_ ; foldr ; all)


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

    evalTerm : (X → ℕ) → Term zero → ℕ
    evalTerm e (S k tzero) = k
    evalTerm e (S k (real x)) = k ℕ+ (e x)
    evalTerm e (S k (appa ()))

    evalAtom : (X → ℕ) → Atom zero → Bool
    evalAtom e (t₁ == t₂) = ⌊ (evalTerm e t₁) ℕ≟ (evalTerm e t₂) ⌋

    -- Evaluating a quantifier-free proposition ⇒ use the evaluation in FirstKind.agda, giving it the above means for evaluating atoms.
    evalQF : (X → ℕ) → QF → Bool
    evalQF e = eval (evalAtom e)

    -- Handy lemmas...
    evalTerm-tsuc : (e : X → ℕ) (t : Term zero) → evalTerm e (tsuc t) ≡ suc (evalTerm e t)
    evalTerm-tsuc e (S k tzero) = refl
    evalTerm-tsuc e (S k (appa ()))
    evalTerm-tsuc e (S k (real x)) = refl
    
    evalTerm-+ℕ : (e : X → ℕ) (t : Term zero) (a : ℕ) → evalTerm e (t +ℕ a) ≡ a ℕ+ (evalTerm e t)
    evalTerm-+ℕ e (S k tzero) a = refl
    evalTerm-+ℕ e (S k (appa ()))
    evalTerm-+ℕ e (S k (real x)) a = +-assoc a k (e x)

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

    substitute-term : X → ℕ → Term zero → Term zero
    substitute-term x a (S k tzero) = S k tzero
    substitute-term x a (S k (real y)) = if ⌊ x X≟ y ⌋ then S (k ℕ+ a) tzero else S k (real y)
    substitute-term x a (S k (appa ()))

    -- substitute a number in place of a variable
    substitute : X → ℕ → QF → QF
    substitute x a (atom (t₁ == t₂)) = atom ((substitute-term x a t₁) == (substitute-term x a t₂))
    substitute x a (~ p) = ~ substitute x a p
    substitute x a (p₁ ∪ p₂) = (substitute x a p₁) ∪ (substitute x a p₂)

    evalTerm-substitute : (x : X) (a : ℕ) (e : X → ℕ) → e x ≡ a → (t : Term zero) → evalTerm e t ≡ evalTerm e (substitute-term x a t)
    evalTerm-substitute x a e eq (S k tzero) = refl
    evalTerm-substitute x a e eq (S k (real y)) with y | x X≟ y
    ... | .x | yes refl = {!!} -- trans (cong (λ z → k ℕ+ z) eq) (+-comm zero (k ℕ+ a)) 
    ... |  _ | no  diff = refl
    evalTerm-substitute x a e eq (S k (appa ()))

    -- Replacing a variable with the value it has does not alter the semantics.
    evalQF-substitute : (x : X) (a : ℕ) (e : X → ℕ) → e x ≡ a → (p : QF) → evalQF e p ≡ evalQF e (substitute x a p)
    evalQF-substitute x a e eq (atom (t₁ == t₂)) = cong₂ (λ m n → ⌊ m ℕ≟ n ⌋) (evalTerm-substitute x a e eq t₁) (evalTerm-substitute x a e eq t₂)
    evalQF-substitute x a e eq (~ p) = cong not (evalQF-substitute x a e eq p)
    evalQF-substitute x a e eq (p₁ ∪ p₂) = cong₂ _∨_ (evalQF-substitute x a e eq p₁) (evalQF-substitute x a e eq p₂)

    -- If P ≡ P', then (A & P) ≡ (A & P')
    &-≣ : {P P' : QF} (A : QF) → ⊢ P ≣ P' → ⊢ (A & P) ≣ (A & P')
    &-≣ {P} {P'} A eq = {!!}

    module Environment where
      depends-term : Term zero → X → Set
      depends-term (S k tzero) _ = ⊥
      depends-term (S k (real x)) t = t ≡ x
      depends-term (S k (appa ()))

      depends : QF → X → Set
      depends (atom (t₁ == t₂)) x = depends-term t₁ x ⊎ depends-term t₂ x
      depends (~ p) x = depends p x
      depends (p₁ ∪ p₂) x = depends p₁ x ⊎ depends p₂ x

      Env : Set
      Env = List (X × ℕ)

      lookup : Env → X → ℕ
      lookup [] _ = zero
      lookup ((x , a) ∷ e) t = if ⌊ x X≟ t ⌋ then a else lookup e t

      evalWith : Env → QF → Bool
      evalWith e = evalQF (lookup e)

      _satisfies_ : Env → QF → Set
      e satisfies p = T (evalWith e p)

      nodep-eval-term : (t : Term zero) (e : Env) (x : X) (a : ℕ) → ¬ depends-term t x → evalTerm (lookup ((x , a) ∷ e)) t ≡ evalTerm (lookup e) t
      nodep-eval-term (S k tzero) _ _ _ _ = refl
      nodep-eval-term (S k (real y)) e x a nodep with x X≟ y
      ... | yes same = contradiction same nodep
      ... | no  diff = refl
      nodep-eval-term (S k (appa ()))

      nodep-eval : (p : QF) (e : Env) (x : X) (a : ℕ) → ¬ depends p x → evalWith ((x , a) ∷ e) p ≡ evalWith e p
      nodep-eval (atom (t₁ == t₂)) e x a nodep = cong₂ (λ s₁ s₂ → ⌊ s₁ ℕ≟ s₂ ⌋) (nodep-eval-term t₁ e x a (nodep ∘ inj₁)) (nodep-eval-term t₂ e x a (nodep ∘ inj₂))
      nodep-eval (~ p) e x a nodep = cong not (nodep-eval p e x a nodep)
      nodep-eval (p₁ ∪ p₂) e x a nodep = cong₂ _∨_ (nodep-eval p₁ e x a (nodep ∘ inj₁)) (nodep-eval p₂ e x a (nodep ∘ inj₂))

      substitute-term-nodep : (x : X) (a : ℕ) (t : Term zero) → ¬ depends-term (substitute-term x a t) x
      substitute-term-nodep x a (S k tzero) = λ ()
      substitute-term-nodep x a (S k (appa ()))
      substitute-term-nodep x a (S k (real y)) with x X≟ y
      ... | yes itis = λ ()
      ... | no  isnt = isnt

      substitute-nodep : (x : X) (a : ℕ) (p : QF) → ¬ depends (substitute x a p) x
      substitute-nodep x a (atom (t₁ == t₂)) = [ substitute-term-nodep x a t₁ , substitute-term-nodep x a t₂ ]′
      substitute-nodep x a (~ p) = substitute-nodep x a p
      substitute-nodep x a (p₁ ∪ p₂) = [ substitute-nodep x a p₁ , substitute-nodep x a p₂ ]′

      substitute-term-env : (t : Term zero) (e : Env) (x : X) (a : ℕ) → evalTerm (lookup ((x , a) ∷ e)) t ≡ evalTerm (lookup e) (substitute-term x a t)
      substitute-term-env (S k tzero) _ _ _ = refl
      substitute-term-env (S k (appa ()))
      substitute-term-env (S k (real y )) e x a with x X≟ y
      substitute-term-env (S k (real .x)) e x a | yes refl = refl
      substitute-term-env (S k (real y )) e x a | no  diff = refl

      substitute-env : (p : QF) (e : Env) (x : X) (a : ℕ) → evalWith ((x , a) ∷ e) p ≡ evalWith e (substitute x a p)
      substitute-env (atom (t₁ == t₂)) e x a = cong₂ (λ s₁ s₂ → ⌊ s₁ ℕ≟ s₂ ⌋) (substitute-term-env t₁ e x a) (substitute-term-env t₂ e x a)
      substitute-env (~ p) e x a = cong not (substitute-env p e x a)
      substitute-env (p₁ ∪ p₂) e x a = cong₂ _∨_ (substitute-env p₁ e x a) (substitute-env p₂ e x a)

      substitute-sat : (p : QF) (e : Env) (x : X) (a : ℕ) → e satisfies (substitute x a p) → ((x , a) ∷ e) satisfies p
      substitute-sat p e x a sat with evalWith e (substitute x a p) | evalWith ((x , a) ∷ e) p | substitute-env p e x a 
      ... | true  | .true | refl = tt
      ... | false | _ | _ = ⊥-elim sat
      
    open Environment


    -- A variable mapping that satisfies a quantifier-free proposition.
    Sat : QF → Set
    Sat p = Σ (X → ℕ) (λ e → T (evalQF e p))

    {-
    sat-substitute : (x : X) (a : ℕ) (p : QF) → Sat (substitute x a p) → Sat p
    sat-substitute x a p = {!!}
    -}

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

      allP : (A → Set) → List A → Set
      allP P [] = ⊤
      allP P (x ∷ xs) = (P x) × (allP P xs)

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
    open L using (here ; there ; allP)

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
        form₂ : (z y : X) (b : ℕ) → ¬ (z ≡ y) → CanonicalFactor   -- z = y + b
        form₃ : (y₁ y₂ : X) (b : ℕ) → ¬ (y₁ ≡ y₂) → CanonicalFactor -- y₁ ≠ y₂ + b
        form₄ : (y : X) (d : ℕ) → CanonicalFactor     -- y ≠ d
        failure : CanonicalFactor

      -- Operations on canonical factors.
      module CF where

        _∈_ : X → CanonicalFactor → Set
        w ∈ form₁ x a       = w ≡ x
        w ∈ form₂ z y b _   = (w ≡ z) ⊎ (w ≡ y)
        w ∈ form₃ y₁ y₂ b _ = (w ≡ y₁) ⊎ (w ≡ y₂)
        w ∈ form₄ y d       = w ≡ y
        w ∈ failure         = ⊥

        _∈?_ : (x : X) (cf : CanonicalFactor) → Dec (x ∈ cf)
        _∈?_ = {!!}

        toFactor : CanonicalFactor → Factor 
        toFactor (form₁ x a)       = + (S zero (real x)  == theℕ a)        -- x = a
        toFactor (form₂ z y b _)   = + (S zero (real z)  == S b (real y))  -- z = y + b
        toFactor (form₃ y₁ y₂ b _) = - (S zero (real y₁) == S b (real y₂)) -- y₁ ≠ y₂ + b
        toFactor (form₄ y d)       = - (S zero (real y)  == theℕ d)        -- y₁ ≠ d
        toFactor (failure)         = 0≠0

        interpret : CanonicalFactor → QF
        interpret = F.interpret ∘ toFactor

        kindOf : X → CanonicalFactor → Kind
        kindOf w (form₁ x a) = if ⌊ w X≟ x ⌋ then kind₁ else kind₀
        kindOf w (form₂ z y b _) = if ⌊ w X≟ z ⌋ then kind₃ else if ⌊ w X≟ y ⌋ then kind₂ else kind₀
        kindOf w (form₃ y₁ y₂ b _) = if ⌊ w X≟ y₁ ⌋ then kind₂ else if ⌊ w X≟ y₂ ⌋ then kind₂ else kind₀
        kindOf w (form₄ y d) = if ⌊ w X≟ y ⌋ then kind₂ else kind₀
        kindOf w failure = kind₀

        kind₀-or : Kind → X → CanonicalFactor → Set
        kind₀-or k x f = (kindOf x f ≡ kind₀) ⊎ (kindOf x f ≡ k)

        -- Agreement between variable use (particularly, the variable 'kind's)  in two CanonicalFactors.
        -- This is decidable, but 1. we don't need that and 2. this form is easier to work with than Bool.
        -- Note: symmetric.
        -- TODO: a little unsure about inequalities and the variable indexes, see p118.
        playsNice : CanonicalFactor → CanonicalFactor → Set
        playsNice (form₁ x a) f       = kindOf x f ≡ kind₀
        playsNice (form₂ z y b _) f   = (kindOf z f ≡ kind₀) × (kind₀-or kind₂ y f)
        playsNice (form₃ y₁ y₂ b _) f = (kind₀-or kind₂ y₁ f) × (kind₀-or kind₂ y₂ f)
        playsNice (form₄ y d) f       = kind₀-or kind₂ y f
        playsNice failure _           = ⊤

        is= : CanonicalFactor → Set
        is= (form₁ _ _) = ⊤
        is= (form₂ _ _ _ _) = ⊤
        is= _ = ⊥

        is≠ : CanonicalFactor → Set
        is≠ (form₃ _ _ _ _) = ⊤
        is≠ (form₄ _ _) = ⊤
        is≠ _ = ⊥

      open CF using (is= ; is≠)


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

        kindOf : X → List CanonicalFactor → Kind
        kindOf x [] = kind₀
        kindOf x (cf ∷ cfs) with CF.kindOf x cf
        ... | kind₀ = kindOf x cfs
        ... | kind₁ = kind₁
        ... | kind₂ = kind₂
        ... | kind₃ = kind₃

        module Finders where
          -- Find the first factor containing a given variable.
          find : (x : X) (cfs : List CanonicalFactor) → x ∈ cfs → Σ CanonicalFactor (λ cf → (x CF.∈ cf) × (cf L.∈ cfs))
          find = {!!}

          findKind₁ : (x : X) (cfs : List CanonicalFactor) → kindOf x cfs ≡ kind₁ → Σ CanonicalFactor (λ cf → (x CF.∈ cf) × (CF.kindOf x cf ≡ kind₁) × (cf L.∈ cfs))
          findKind₁ = {!!}

          findKind₃ : (x : X) (cfs : List CanonicalFactor) → kindOf x cfs ≡ kind₃ → Σ CanonicalFactor (λ cf → (x CF.∈ cf) × (CF.kindOf x cf ≡ kind₃) × (cf L.∈ cfs))
          findKind₃ = {!!}

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
          toFrontOk it pn = ({!!} , removeOk it pn)

        open Finders using (find)

          --pull : (x : X) (cfs : List CanonicalFactor) → x ∈ cfs → (

        replaceKind₂ : (x : X) → ℕ → (cfs : List CanonicalFactor) → List CanonicalFactor
        replaceKind₂ x a = {!!}

        -- Adding a factor of the form a=b
        caseA : ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseA a  b cfs with a ℕ≟ b
        caseA a .a cfs | yes refl = cfs          -- factor is trivially true ⇒ no effect on product
        caseA _  _ cfs | no  _    = failure ∷ [] -- factor is trivially false ⇒ product equiv to 0≠0

        -- Adding t+a = b
        caseB : X → ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseB t a b cfs with a ≤? b
        caseB t a b cfs | no  a>b = failure ∷ [] -- a>b ⇒ impossible for t+a to equal b
        caseB t a b cfs | yes a≤b with b ∸ a | t ∈? cfs
        caseB t a b cfs | yes a≤b | b-a | no _ = form₁ t b-a ∷ cfs
        caseB t a b cfs | yes a≤b | b-a | yes t∈ with find t cfs t∈
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₁ .t c , refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₂ .t s c _ , inj₁ refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₂ s .t c _ , inj₂ refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₃ .t s c _ , inj₁ refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₃ s .t c _ , inj₂ refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (form₄ .t c , refl , ptr ) = {!!}
        caseB t a b cfs | yes a≤b | b-a | yes t∈ | (failure , () , ptr )

{-
caseB t a b cfs | yes a≤b | b-a | kind₀ = 
        caseB t a b cfs | yes a≤b | b-a | kind₁ with Finders.findKind₁ t cfs refl
        caseB t a b cfs | yes a≤b | b-a | kind₁ | (form₁ .t c , refl , refl , ptr) = ?
        caseB t a b cfs | yes a≤b | b-a | kind₂ = form₁ t b-a ∷ (replaceKind₂ t b-a cfs refl)
        caseB t a b cfs | yes a≤b | b-a | kind₃ with Finders.findKind₃ t cfs refl
        caseB t a b cfs | yes a≤b | b-a | kind₃ | (form₁ s .t c _ , refl , refl , ptr) = ?
-}
        {-
        | t ∈? cfs
        caseB t a b cfs | yes a≤b | b-a | no  _ = form₁ t b-a ∷ cfs
        -- TODO: define better _∈_ for products
        -}

        -- Adding t+a = t+b
        caseC : X → ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseC _ = caseA

        -- t+a = s+b, t and s different vars, a ≤ b
        -- ⇔ t=s+(b-a)
        caseD′ : X → ℕ → X → ℕ → List CanonicalFactor → List CanonicalFactor
        caseD′ t a s b cfs = {!!}

        -- Adding t+a = s+b, with t and s different vars
        caseD : X → ℕ → X → ℕ → List CanonicalFactor → List CanonicalFactor
        caseD t a s b cfs with a ≤? b
        ... | yes a≤b = caseD′ t a s b cfs
        ... | no  a>b = caseD′ s b t a cfs
        
    
        -- Adding a factor of the form a≠b
        caseA≠ : ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseA≠ a  b cfs with a ℕ≟ b
        caseA≠ a .a cfs | yes refl = failure ∷ []
        caseA≠ _  _ cfs | no  _    = cfs

        -- Adding t+a ≠ b
        caseB≠ : X → ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseB≠ t a b cfs with a ≤? b
        caseB≠ t a b cfs | no  a>b = cfs  -- if a > b, t+a will never equal b ⇒ the inequality is trivially true
        caseB≠ t a b cfs | yes a≤b = {!!}

        -- Adding t+a ≠ t+b
        caseC≠ : X → ℕ → ℕ → List CanonicalFactor → List CanonicalFactor
        caseC≠ _ = caseA≠

        -- Adding t+a ≠ s+b, with t and s different vars
        caseD≠ : X → ℕ → X → ℕ → List CanonicalFactor → List CanonicalFactor
        caseD≠ t a s b cfs = {!!}

        -- Add a factor to a list of canonical factors, maintaining equivalence and keeping the whole thing canonical.
        addFactor : Factor → List CanonicalFactor → List CanonicalFactor
        addFactor (+ (S _ (appa ()) == _)) _
        addFactor (+ (_ == S _ (appa ()))) _
        addFactor (- (S _ (appa ()) == _)) _
        addFactor (- (_ == S _ (appa ()))) _
        addFactor (+ (S a tzero == S b tzero)) cfs = caseA a b cfs
        addFactor (+ (S a (real t) == S b tzero)) cfs = caseB t a b cfs
        addFactor (+ (S b tzero == S a (real t))) cfs = caseB t a b cfs
        addFactor (+ (S a (real t) == S b (real s)))  cfs with t X≟ s
        addFactor (+ (S a (real t) == S b (real .t))) cfs | yes refl = caseC t a b cfs
        addFactor (+ (S a (real t) == S b (real s)))  cfs | no  _    = caseD t a s b cfs
        addFactor (- (S a tzero == S b tzero)) cfs = caseA≠ a b cfs
        addFactor (- (S a (real t) == S b tzero)) cfs = {!!}
        addFactor (- (S b tzero == S a (real t))) cfs = {!!}
        addFactor (- (S a (real t) == S b (real s)))  cfs with t X≟ s
        addFactor (- (S a (real t) == S b (real .t))) cfs | yes refl = caseC≠ t a b cfs
        addFactor (- (S a (real t) == S b (real s)))  cfs | no  _    = {!!}


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



        -- CPs either equiv to 0≠0 or satisfiable

        -- Variable assignment
        --module VA where

        module Ineq where

          -- A list of canonical factors that are of form 3 or 4
          Ineqs : Set
          Ineqs = Σ (List CanonicalFactor) (allP is≠)

          cons-ineq : Σ CanonicalFactor is≠ → Ineqs → Ineqs
          cons-ineq (cf , cf≠) (cfs , cfs≠) = (cf ∷ cfs , cf≠ , cfs≠)

          avoid : X → Ineqs → List ℕ
          avoid _ ([] , _) = []
          avoid _ (form₁ _ _ ∷ _ , () , _)
          avoid _ (form₂ _ _ _ _ ∷ _ , () , _)
          avoid _ (failure ∷ _ , () , _)
          avoid w (form₃ _ _ _ _ ∷ cfs , _ , cfs≠) = avoid w (cfs , cfs≠)
          avoid w (form₄ y d ∷ cfs , _ , cfs≠) = if ⌊ w X≟ y ⌋ then d ∷ avoid w (cfs , cfs≠ ) else avoid w (cfs , cfs≠)

          --avoid-tail : {a : ℕ} {y : X} {ineq : Σ CanonicalFactor is≠} {ineqs : Ineqs} → ¬ a L.∈ (avoid y (cons-ineq ineq ineqs)) → ¬ a L.∈ (avoid y ineqs)
          avoid-tail : {a : ℕ} {y : X} (ineq : Σ CanonicalFactor is≠) (ineqs : Ineqs) → ¬ a L.∈ (avoid y (cons-ineq ineq ineqs)) → ¬ a L.∈ (avoid y ineqs)
          avoid-tail = {!!}

          -- Substitute a value in place of a variable in a set of *inequalities*.
          -- Must not break anything.
          sub-≠s : (t : X) (a : ℕ) (≠s : Ineqs) → ¬ a L.∈ (avoid t ≠s) → Ineqs 
          sub-≠s _ _ ([] , _) _ = ([] , tt)
          sub-≠s _ _ ((form₁ _ _) ∷ _ , () , _)
          sub-≠s _ _ ((form₂ _ _ _ _) ∷ _ , () , _)
          sub-≠s _ _ (failure ∷ _ , () , _)
          sub-≠s t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok = {!!}
          sub-≠s t a (form₄ y  d ∷ ≠s , _ , ≠s-≠) a-ok = if ⌊ t X≟ y ⌋
            --then sub-≠s t a (≠s , ≠s-≠) (avoid-tail a-ok)
            --else cons-ineq (form₄ y d , tt) (sub-≠s t a (≠s , ≠s-≠) (avoid-tail a-ok))
            then sub-≠s t a (≠s , ≠s-≠) (avoid-tail (form₄ y d , tt) (≠s , ≠s-≠) a-ok)
            else cons-ineq (form₄ y d , tt) (sub-≠s t a (≠s , ≠s-≠) (avoid-tail (form₄ y d , tt) (≠s , ≠s-≠) a-ok))
          
          {-
          sub-≠s w n ((form₃ y₁ y₂ b diff) ∷ ≠s , _ , ≠s-≠) = if ⌊ w X≟ y₁ ⌋
            then if ⌊ b ≤? n ⌋
              then form₄ y₂ (n ∸ b) ∷ sub-≠s w n ≠s ≠s-≠
              else sub-≠s w n ≠s ≠s-≠
            else if ⌊ w X≟ y₂ ⌋
              then form₄ y₁ (n ℕ+ b) ∷ sub-≠s w n ≠s ≠s-≠
              else form₃ y₁ y₂ b diff ∷ sub-≠s w n ≠s ≠s-≠
          sub-≠s w n ((form₄ y d) ∷ ≠s) (_ , ≠s-≠) = if ⌊ w X≟ y ⌋
            then if ⌊ n ℕ≟ d ⌋
              then failure ∷ []
              else sub-≠s w n ≠s ≠s-≠
            else form₄ y d ∷ sub-≠s w n ≠s ≠s-≠
          -}
          {-
          sub-≠s-substitute : (t : X) (a : ℕ) (≠s : List CanonicalFactor) (≠s-≠ : allP is≠ ≠s) (e : X → ℕ)
            → (evalQF e (interpret (sub-≠s t a ≠s ≠s-≠))) ≡ (evalQF e (substitute t a (interpret ≠s)))
          sub-≠s-substitute t a [] _ _ = refl
          sub-≠s-substitute t a (form₁ _ _ ∷ _) (() , _)
          sub-≠s-substitute t a (form₂ _ _ _ _ ∷ _) (() , _)
          sub-≠s-substitute t a (failure ∷ _) (() , _)
          sub-≠s-substitute t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s) (_ , ≠s-≠) e = {!!}
          sub-≠s-substitute t a (form₄ y  d ∷ ≠s) (_ , ≠s-≠) e with t X≟ y
          sub-≠s-substitute t a (form₄ .t d  ∷ ≠s) (_ , ≠s-≠) e | yes refl with a ℕ≟ d
          sub-≠s-substitute t a (form₄ .t .a ∷ ≠s) (_ , ≠s-≠) e | yes refl | yes refl = refl
          sub-≠s-substitute t a (form₄ .t d  ∷ ≠s) (_ , ≠s-≠) e | yes refl | no  a≠d  = {!sub-≠s-substitute t a ≠s ≠s-≠ e!}
          sub-≠s-substitute t a (form₄ y  d  ∷ ≠s) (_ , ≠s-≠) e | no  diff = cong (λ s → not ((not (evalQF e (CF.interpret (form₄ y d)))) ∨ (not s))) (sub-≠s-substitute t a ≠s ≠s-≠ e)
          -}
          --sub-≠s-sat : (t : X) (a : ℕ) (≠s : List CanonicalFactor) (≠s-≠ : allP is≠ ≠s)
          --  → 
                    
          {-
          solve-≠s : (ys : List X) (≠s : List CanonicalFactor) → allP is≠ ≠s → Env
          solve-≠s [] _ _ = []
          solve-≠s (y ∷ ys) ≠s ≠s-≠ with choice y ≠s ≠s-≠
          ... | a = (y , a) ∷ solve-≠s ys (sub-≠s y a ≠s ≠s-≠) (choice-ok y ≠s ≠s-≠)
          -}
          -- If a number isn't in the
--          avoid-ok : (x : X) (a : ℕ) (≠s : List CanonicalFactor) (≠s-≠ : allP is≠ ≠s) → ¬ (a L.∈ avoid x ≠s ≠s-≠) → 



          {-
          eval-sub : (f x ≡ a) → eval f (interpret cp) ≡ eval f (interpret (sub-≠s x a

          -- If we replace x with a,
          -- If sub x a p satisfiable, then p satisfiable.

          -}
          {-
          solve-y : (≠s : List CanonicalFactor) → T (all CF.is≠ ≠s) → X → ℕ
          solve-y [] _ _ = zero
          solve-y 

          solve-≠s : (≠s : List CanonicalFactor) → T (all CF.is≠ ≠s) → 
          solve-≠s [] = 
          -}


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
    
