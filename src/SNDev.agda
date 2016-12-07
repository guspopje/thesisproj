open import Agda.Primitive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module SNDev {X : Set} {_X≟_ : Decidable {A = X} _≡_ } where
  open import Common
  open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _≤?_ ; _∸_ ) renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_)
  open import Data.Nat.Properties.Simple using (+-comm ; +-assoc)

  open import SucNat.Base {X = X}
  open import Data.Bool using (Bool ; true ; false ; _∨_ ; _∧_ ; not ; if_then_else_ ; T) renaming (_≟_ to _B≟_)
  open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_ ; foldr ; all ; null)
  open import Data.Maybe using (Maybe ; just ; nothing)

  module QFree where
    
    open import FirstKind
    open import SucNat.FK {X = X}
    open import SucNat.DecVar {X = X} {_≟_ = _X≟_}

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

    -- Semantic equivalence
    _⇔_ : QF → QF → Set
    p₁ ⇔ p₂ = (f : X → ℕ) → (evalQF f p₁ ≡ evalQF f p₂)

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
    evalQF-≣ : {p₁ p₂ : QF} → ⊢ p₁ ≣ p₂ → p₁ ⇔ p₂
    evalQF-≣ {p₁} {p₂} eq e with evalQF e p₁ | evalQF e p₂ | provableTrue (evalAtom e) (happy e) (&-elim₁' eq) | provableTrue (evalAtom e) (happy e) (&-elim₂' eq)
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

      substitute-sat : (p : QF) (x : X) (a : ℕ) (e : Env) → e satisfies (substitute x a p) → ((x , a) ∷ e) satisfies p
      substitute-sat p x a e sat with evalWith e (substitute x a p) | evalWith ((x , a) ∷ e) p | substitute-env p e x a 
      ... | true  | .true | refl = tt
      ... | false | _ | _ = ⊥-elim sat

      Sat : QF → Set
      Sat p = Σ Env (λ e → e satisfies p)

    open Environment



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
    open L using (here ; there ; allP)

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
    open KindAsType public renaming (_≟_ to _K≟_)


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

      is=? : (cf : CanonicalFactor) → Dec (is= cf)
      is=? (form₁ _ _) = yes tt
      is=? (form₂ _ _ _ _) = yes tt
      is=? (form₃ _ _ _ _) = no (λ ())
      is=? (form₄ _ _) = no (λ ())
      is=? failure = no (λ ())

      is≠ : CanonicalFactor → Set
      is≠ (form₃ _ _ _ _) = ⊤
      is≠ (form₄ _ _) = ⊤
      is≠ _ = ⊥

      is≠? : (cf : CanonicalFactor) → Dec (is≠ cf)
      is≠? (form₁ _ _) = no (λ ())
      is≠? (form₂ _ _ _ _) = no (λ ())
      is≠? (form₃ _ _ _ _) = yes tt
      is≠? (form₄ _ _) = yes tt
      is≠? failure = no (λ ())

      kind₀-∉ : (t : X) (cf : CanonicalFactor) → kindOf t cf ≡ kind₀ → ¬ t ∈ cf
      kind₀-∉ t (form₁ .t _) isk₀ refl with isk₀
      kind₀-∉ t (form₁ .t _) isk₀ refl | ()
      kind₀-∉ t (form₂ .t _ _ _) isk₀ (inj₁ refl) with isk₀
      kind₀-∉ t (form₂ .t _ _ _) isk₀ (inj₁ refl) | ()
      kind₀-∉ t (form₂ _ .t _ _) isk₀ (inj₂ refl) with isk₀
      kind₀-∉ t (form₂ _ .t _ _) isk₀ (inj₂ refl) | ()
      kind₀-∉ t (form₃ .t _ _ _) isk₀ (inj₁ refl) with isk₀
      kind₀-∉ t (form₃ .t _ _ _) isk₀ (inj₁ refl) | ()
      kind₀-∉ t (form₃ _ .t _ _) isk₀ (inj₂ refl) with isk₀
      kind₀-∉ t (form₃ _ .t _ _) isk₀ (inj₂ refl) | ()
      kind₀-∉ t (form₄ .t _) isk₀ refl with isk₀
      kind₀-∉ t (form₄ .t _) isk₀ refl | ()
      kind₀-∉ t failure isk₀ ()
      
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


      -- Some useful little semantic results
      false-prod : (f : X → ℕ) (cf : CanonicalFactor) (cfs : List CanonicalFactor) → ¬ T (evalQF f (CF.interpret cf)) → ¬ T (evalQF f (interpret (cf ∷ cfs)))
      false-prod f cf cfs cf-false with evalQF f (CF.interpret cf)
      false-prod f cf cfs cf-false | true  = contradiction tt cf-false
      false-prod f cf cfs cf-false | false = λ ()

      true-prod : (f : X → ℕ) (cf : CanonicalFactor) (cfs : List CanonicalFactor) → T (evalQF f (CF.interpret cf)) → evalQF f (interpret (cf ∷ cfs)) ≡ evalQF f (interpret (cf ∷ cfs))
      true-prod f cf cfs cf-true with evalQF f (CF.interpret cf)
      true-prod f cf cfs cf-true | true  = refl
      true-prod f cf cfs cf-true | false = ⊥-elim cf-true


      module Finders where
        -- Find the first factor containing a given variable.
        find : (x : X) (cfs : List CanonicalFactor) → x ∈ cfs → Σ CanonicalFactor (λ cf → (x CF.∈ cf) × (cf L.∈ cfs))
        find t [] ()
        find t (cf ∷ cfs) (inj₂ t∈cfs) with (find t cfs t∈cfs)
        ... | (cf′ , x∈cf′ , cf′∈cfs) = (cf′ , x∈cf′ , there cf cf′∈cfs)
        find t (form₁ .t a ∷ cfs) (inj₁ refl) = (form₁ t a , refl , here (form₁ t a) cfs)
        find t (form₂ .t y b diff ∷ cfs) (inj₁ (inj₁ refl)) = (form₂ t y b diff , inj₁ refl , here (form₂ t y b diff) cfs)
        find t (form₂ z .t b diff ∷ cfs) (inj₁ (inj₂ refl)) = (form₂ z t b diff , inj₂ refl , here (form₂ z t b diff) cfs)
        find t (form₃ .t y₂ b diff ∷ cfs) (inj₁ (inj₁ refl)) = (form₃ t y₂ b diff , inj₁ refl , here (form₃ t y₂ b diff) cfs)
        find t (form₃ y₁ .t b diff ∷ cfs) (inj₁ (inj₂ refl)) = (form₃ y₁ t b diff , inj₂ refl , here (form₃ y₁ t b diff) cfs)
        find t (form₄ .t d ∷ cfs) (inj₁ refl) = (form₄ t d , refl , here (form₄ t d) cfs)
        find t (failure ∷ _) (inj₁ ())

        kind₀-head : (x : X) (cf : CanonicalFactor) (cfs : List CanonicalFactor) → kindOf x (cf ∷ cfs) ≡ kind₀ → CF.kindOf x cf ≡ kind₀
        kind₀-head x cf _ isk₀ with CF.kindOf x cf | isk₀
        ... | kind₀ | _ = refl
        ... | kind₁ | ()
        ... | kind₂ | ()
        ... | kind₃ | ()

        kind₀-tail : (x : X) (cf : CanonicalFactor) (cfs : List CanonicalFactor) → kindOf x (cf ∷ cfs) ≡ kind₀ → kindOf x cfs ≡ kind₀
        kind₀-tail x cf [] _ = refl
        kind₀-tail x cf cfs isk₀ with CF.kindOf x cf | isk₀
        ... | kind₀ | _ = isk₀
        ... | kind₁ | ()
        ... | kind₂ | ()
        ... | kind₃ | ()

        kind₀-∉ : (t : X) (cfs : List CanonicalFactor) → kindOf t cfs ≡ kind₀ → ¬ t ∈ cfs
        kind₀-∉ t [] isk₀ ()
        kind₀-∉ t (cf ∷ cfs) isk₀ (inj₁ t∈cf) = contradiction t∈cf (CF.kind₀-∉ t cf (kind₀-head t cf cfs isk₀)) 
        kind₀-∉ t (cf ∷ cfs) isk₀ (inj₂ t∈cfs) = kind₀-∉ t cfs (kind₀-tail t cf cfs isk₀) t∈cfs

{-
        ¬kind₀-∈ : (t : X) (cfs : List CanonicalFactor) → ¬ kindOf t cfs ≡ kind₀ → t ∈ cfs
        ¬kind₀-∈ t [] notk₀ = contradiction refl notk₀
        ¬kind₀-∈ t (cf ∷ cfs) notk₀ with 
        ¬kind₀-∈ t (cf ∷ cfs) notk₀ | yes t∈cf = inj₁ t∈cf        
        ¬kind₀-∈ t (cf ∷ cfs) notk₀ | no  t∉cf = inj₂ (¬kind₀-∈ t cfs {!notk₀!})
-}        
        

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

      open Finders public using (find ; kind₀-∉)

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
      --toCP-equiv : (p : List Factor) → ⊢ (interpret (toCP p)) ≣ (P.interpret p)
      --toCP-equiv [] = ≣-refl (F.interpret 0=0)
      --toCP-equiv (f ∷ fs) = ≣-trans' (addFactor-equiv f (toCP fs)) (&-≣ (F.interpret f) (toCP-equiv fs))

      -- ...at least semantically.
      toCP-sem-equiv : (p : List Factor) → (interpret (toCP p)) ⇔ (P.interpret p)
      toCP-sem-equiv = {!!}

      -- Solving the inequalities. Roughly:
      --   * Grab a variable
      --   * Substitute any value that won't make any term false
      --   * Repeat
      --
      -- One would expect this is be easy to express and prove.
      -- Hopefully there is a more elegant way.
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

        avoid-tail : {a : ℕ} {y : X} (ineq : Σ CanonicalFactor is≠) (ineqs : Ineqs) → ¬ a L.∈ (avoid y (cons-ineq ineq ineqs)) → ¬ a L.∈ (avoid y ineqs)
        avoid-tail = {!!}

        -- Substitute a value in place of a variable in a set of *inequalities*.
        -- The result is equivalent if a ∉ avoid t ≠s, as will be proven later.
        sub-≠s : (t : X) (a : ℕ) (≠s : Ineqs) → Ineqs 
        sub-≠s _ _ ([] , _) = ([] , tt)
        sub-≠s _ _ ((form₁ _ _) ∷ _ , () , _)
        sub-≠s _ _ ((form₂ _ _ _ _) ∷ _ , () , _)
        sub-≠s _ _ (failure ∷ _ , () , _)
        sub-≠s t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) =
          if ⌊ t X≟ y₁ ⌋
            then if ⌊ b ≤? a ⌋
              then cons-ineq (form₄ y₂ (a ∸ b) , tt)     (sub-≠s t a (≠s , ≠s-≠))
              else                                       (sub-≠s t a (≠s , ≠s-≠))
            else if ⌊ t X≟ y₂ ⌋
              then cons-ineq (form₄ y₁ (a ℕ+ b) , tt)    (sub-≠s t a (≠s , ≠s-≠))
              else cons-ineq (form₃ y₁ y₂ b y₁≢y₂ , tt)  (sub-≠s t a (≠s , ≠s-≠)) 
        sub-≠s t a (form₄ y  d ∷ ≠s , _ , ≠s-≠) =
          if ⌊ t X≟ y ⌋
            then                                         (sub-≠s t a (≠s , ≠s-≠)) -- this is equiv only if a≠d
            else cons-ineq (form₄ y d , tt)              (sub-≠s t a (≠s , ≠s-≠))

        notnot : {b : Bool} → b ≡ not (not b)
        notnot {true} = refl
        notnot {false} = refl

        dual-and : Bool → Bool → Bool
        dual-and a b = not ((not a) ∨ (not b))

        sub-≠s-substitute : (t : X) (a : ℕ) (≠s : Ineqs)
          → ¬ a L.∈ avoid t ≠s
          → interpret (proj₁ (sub-≠s t a ≠s)) ⇔ substitute t a (interpret (proj₁ ≠s))
        sub-≠s-substitute _ _ ([] , _) _ _ = refl
        sub-≠s-substitute _ _ ((form₁ _ _) ∷ _ , () , _)
        sub-≠s-substitute _ _ ((form₂ _ _ _ _) ∷ _ , () , _)
        sub-≠s-substitute _ _ (failure ∷ _ , () , _)
        sub-≠s-substitute t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e with t X≟ y₁
        sub-≠s-substitute t a (form₃ .t y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl with b ≤? a
        sub-≠s-substitute t a (form₃ .t y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl | yes b≤a = {!!} -- equiv factor
        sub-≠s-substitute t a (form₃ .t y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl | no  b≰a = {!!} -- factor auto-true
        sub-≠s-substitute t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | no  _ with t X≟ y₂
        sub-≠s-substitute t a (form₃ y₁ .t b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | no  _ | yes refl = {!!}
        sub-≠s-substitute t a (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) a-ok e | no  _ | no  _    = cong (dual-and (evalQF e (CF.interpret (form₃ y₁ y₂ b y₁≢y₂)))) (sub-≠s-substitute t a (≠s , ≠s-≠) a-ok e)
        sub-≠s-substitute t a (form₄ y  d  ∷ ≠s , _ , ≠s-≠) a-ok e with t X≟ y
        sub-≠s-substitute t a (form₄ .t d  ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl with a ℕ≟ d
        sub-≠s-substitute t a (form₄ .t .a ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl | yes refl = contradiction (here a (avoid t (≠s , ≠s-≠))) a-ok
        sub-≠s-substitute t a (form₄ .t d  ∷ ≠s , _ , ≠s-≠) a-ok e | yes refl | no  _    = trans (sub-≠s-substitute t a (≠s , ≠s-≠) (a-ok ∘ (there d)) e) notnot
        sub-≠s-substitute t a (form₄ y  d  ∷ ≠s , _ , ≠s-≠) a-ok e | no  _    = cong (dual-and (evalQF e (CF.interpret (form₄ y d)))) (sub-≠s-substitute t a (≠s , ≠s-≠) a-ok e)
  --          sub-≠s-substitute t a (form₄ y  d  ∷ ≠s , _ , ≠s-≠) e a-ok | no  _    = cong (dual-and (not ⌊ e y ℕ≟ d ⌋)) (sub-≠s-substitute t a (≠s , ≠s-≠) e a-ok)

        --sub-≠s- : (t : X) (a : ℕ) (≠s : Ineqs) → ¬ t ∈ (sub-≠s t a ≠s)

        fresh : List ℕ → ℕ
        fresh = {!!}

        -- The result of fresh is indeed fresh.
        fresh-fresh : (xs : List ℕ) → ¬ (fresh xs) L.∈ xs
        fresh-fresh = {!!}

        sub-≠s-env : (t : X) (a : ℕ) (≠s : Ineqs)
          → ¬ a L.∈ (avoid t ≠s)
          → (e : Env)
          → e satisfies (interpret (proj₁ (sub-≠s t a ≠s)))
          → ((t , a) ∷ e) satisfies (interpret (proj₁ ≠s))
        sub-≠s-env t a ≠s a-ok e sat = substitute-sat (interpret (proj₁ ≠s)) t a e
          (subst T (sub-≠s-substitute t a ≠s a-ok (lookup e)) sat)

        choose : X → Ineqs → ℕ
        choose y ≠s = fresh (avoid y ≠s)

        choose-ok : (y : X) (≠s : Ineqs) → ¬ choose y ≠s L.∈ avoid y ≠s
        choose-ok y ≠s = fresh-fresh (avoid y ≠s)

        hasVar : (x : X) (ys : List X) → Dec (x L.∈ ys)
        hasVar _ [] = no (λ ())
        hasVar x (y ∷ ys) with x X≟ y
        hasVar x (.x ∷ ys) | yes refl = yes (here x ys)
        hasVar x (y ∷ ys)  | no  _ with hasVar x ys
        hasVar x (y ∷ ys)  | no  _ | yes p = yes (there y p)
        hasVar x (y ∷ ys)  | no  _ | no ¬p = no {!!}

        insert-if-∉ : X → List X → List X
        insert-if-∉ x ys with hasVar x ys
        ... | yes _ = ys
        ... | no  _ = x ∷ ys

        free : Ineqs → List X
        free ([] , _) = []
        free (form₁ _ _ ∷ _ , () , _)
        free (form₂ _ _ _ _ ∷ _ , () , _)
        free (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) = insert-if-∉ y₁ (insert-if-∉ y₂ (free (≠s , ≠s-≠)))
        free (form₄ y d ∷ ≠s , _ , ≠s-≠) = insert-if-∉ y (free (≠s , ≠s-≠))
        free (failure ∷ _ , () , _)

        empty : {A : Set} → List A → Set
        empty [] = ⊤
        empty _ = ⊥

        nonempty-free : (≠s : Ineqs) → ¬ empty (proj₁ ≠s) → ¬ empty (free ≠s)
        nonempty-free = {!!}

        free-sub : (y : X) (a : ℕ) (≠s : Ineqs) (ys : List X) → (y ∷ ys) ≡ free ≠s → ys ≡ free (sub-≠s y a ≠s) 
        free-sub y a ≠s ys eq = {!!}

        solve-ys : List X → (≠s : Ineqs) → Env
        solve-ys [] _ = []
        solve-ys (y ∷ ys) ≠s = (y , choose y ≠s) ∷ (solve-ys ys (sub-≠s y (choose y ≠s) ≠s))

        solve-ys-works : (ys : List X) (≠s : Ineqs) → ys ≡ free ≠s → (solve-ys ys ≠s) satisfies (interpret (proj₁ ≠s)) 
        solve-ys-works [] ([] , _) _ = tt
        solve-ys-works [] (form₁ _ _ ∷ _ , () , _)
        solve-ys-works [] (form₂ _ _ _ _ ∷ _ , () , _)
        solve-ys-works [] (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , _ , ≠s-≠) eq = ⊥-elim (
          (nonempty-free (form₃ y₁ y₂ b y₁≢y₂ ∷ ≠s , tt , ≠s-≠) (λ ()))
          (subst empty eq tt))
        solve-ys-works [] (form₄ y d ∷ ≠s , _ , ≠s-≠) eq = ⊥-elim (
          (nonempty-free (form₄ y d ∷ ≠s , tt , ≠s-≠) (λ ()))
          (subst empty eq tt))
        solve-ys-works [] (failure ∷ _ , () , _)
        solve-ys-works (y ∷ ys) ≠s eq = sub-≠s-env y (choose y ≠s) ≠s (choose-ok y ≠s) (solve-ys ys (sub-≠s y (choose y ≠s) ≠s))
          (solve-ys-works ys (sub-≠s y (choose y ≠s) ≠s) (free-sub y (choose y ≠s) ≠s ys eq))

        sat-ys : (≠s : List CanonicalFactor) → allP is≠ ≠s → Sat (interpret ≠s)
        sat-ys ≠s ≠s-≠ = (solve-ys (free (≠s , ≠s-≠)) (≠s , ≠s-≠) , solve-ys-works (free (≠s , ≠s-≠)) (≠s , ≠s-≠) refl)

      open Ineq using (sat-ys)

      -- Prove that we can always resolve equalities as we add them (providing the product remains canonical).
      add-= : (cf : CanonicalFactor) (cfs : List CanonicalFactor) → is= cf → isCanonicalProduct (cf ∷ cfs)
        → Sat (interpret cfs) → Sat (interpret (cf ∷ cfs))
      add-= (form₁ x d) cfs _ (pn , cfsCanonical) (e , esat) = {!!}
      add-= (form₂ y₁ y₂ b y₁≢y₂) cfs _ (pn , cfsCanonical) (e , esat) = {!!}
      add-= (form₃ _ _ _ _) _ ()
      add-= (form₄ _ _) _ ()
      add-= failure _ ()
      

    -- Operations on/about canonical form (sum of canonical products)
    module CForm where

      -- Interpret our canonical form (dnf on CanonicalFactors).
      interpret : List (List CanonicalFactor) → QF
      interpret [] = F.interpret 0≠0
      interpret (cp ∷ cps) = (CProd.interpret cp) ∪ (interpret cps)
      
      -- Turn a sum of products into a sum of canonical products.
      dnf⇒CanonicalForm : List (List Factor) → List (List CanonicalFactor)
      dnf⇒CanonicalForm = Data.List.map CProd.toCP

      -- Transform a quantifier-free proposition into canonical form.
      toCF : QF → List (List CanonicalFactor)
      toCF = {!!}

      -- It is semantically equivalent.
      toCF-⇔ : (p : QF) → interpret (toCF p) ⇔ p
      toCF-⇔ = {!!}

    {-
    falseOrSat : (p : QF) → (⊢ ~ p) ⊎ (Σ (X → ℕ) (λ f → T (evalQF f p)))
      
    trueOrCounter : (p : QF) → (⊢ p) ⊎ (Σ (X → ℕ) (λ f → T (not (evalQF f p))))
    trueOrCounter p with falseOrSat (~ p)
    ... | inj₁ ⊢~~p = inj₁ (impl (~~-elim p) ⊢~~p)
    ... | inj₂ (sys , ⟦~p⟧) = inj₂ (sys , ⟦~p⟧)
    -}

    open CForm using (toCF ; toCF-⇔) public

  module QElim where

    open import SK.Base {Atom = Atom}

    QP : ℕ → Set
    QP = QH

    open QFree
    open Environment

    -- Drop all factors in which a variable occurs.
    -- Since this is only done for a variable of the first or third kind, only one term should be dropped, so there is likely a better way to formulate this.
    case-a : X → List CanonicalFactor → List CanonicalFactor
    case-a t [] = []
    case-a t (cf ∷ cfs) with t CF.∈? cf
    ... | yes _ = case-a t cfs
    ... | no  _ = cf ∷ case-a t cfs

    -- Replace a variable t of the *second kind* with s-k.
    -- Assumptions made:
    --   * s ≥ k
    --   * There is no equality z=t+j with j < k
    --   * t is of the second kind, and therefore does not occur on the LHS of equalities
    --   * s is of the first or third kind, and therefore does not occur in inequalities
    -- The latter two could later be enforced via "CF.kind₀-or".
    case-b-sub-cf : (t : X) (s : X) (k : ℕ) (cf : CanonicalFactor) → List CanonicalFactor
    case-b-sub-cf _ _ _ (form₁ x a) = [ form₁ x a ]
    case-b-sub-cf t s k (form₂ z  y  b z≢y) with t X≟ y
    case-b-sub-cf t s k (form₂ z  .t b z≢y) | yes refl with z X≟ s
    case-b-sub-cf t s k (form₂ .s .t b z≢y) | yes refl | yes refl = if ⌊ b ℕ≟ k ⌋ then [] else [ failure ]
    case-b-sub-cf t s k (form₂ z  .t b z≢y) | yes refl | no  z≢s  = [ form₂ z s (b ∸ k) z≢s ]
    case-b-sub-cf t s k (form₂ z  y  b z≢y) | no _                = [ form₂ z y b z≢y ]
    case-b-sub-cf t s k (form₃ y₁ y₂ b y₁≢y₂) with t X≟ y₁
    case-b-sub-cf t s k (form₃ .t y₂ b t≢y₂ ) | yes refl with s X≟ y₂
    case-b-sub-cf t s k (form₃ .t .s b t≢s  ) | yes refl | yes refl = if ⌊ (k ℕ+ b) ℕ≟ 0 ⌋ then [ failure ] else []
    case-b-sub-cf t s k (form₃ .t y₂ b t≢y₂ ) | yes refl | no  s≢y₂ = [ form₃ s y₂ (k ℕ+ b) s≢y₂ ]
    case-b-sub-cf t s k (form₃ y₁ y₂ b y₁≢y₂) | no _ with t X≟ y₂
    case-b-sub-cf t s k (form₃ y₁ .t b y₁≢t ) | no _ | yes refl with y₁ X≟ s
    case-b-sub-cf t s k (form₃ .s .t b y₁≢t ) | no _ | yes refl | yes refl = if ⌊ k ℕ≟ b ⌋ then [ failure ] else []
    case-b-sub-cf t s k (form₃ y₁ .t b y₁≢t ) | no _ | yes refl | no  y₁≢s = if ⌊ k ≤? b ⌋
      then [ form₃ y₁ s (b ∸ k) y₁≢s ]
      else [ form₃ s y₁ (k ∸ b) (y₁≢s ∘ sym) ]
    case-b-sub-cf t s k (form₃ y₁ y₂ b y₁≢y₂) | no _ | no _ = [ form₃ y₁ y₂ b y₁≢y₂ ]
    case-b-sub-cf t s k (form₄ y  d) with t X≟ y
    case-b-sub-cf t s k (form₄ .t d) | yes refl = [ form₄ s (k ℕ+ d) ]
    case-b-sub-cf t s k (form₄ y  d) | no  _    = [ form₄ y d ]
    case-b-sub-cf _ _ _ failure = [ failure ]

    case-b-sub : (t : X) (s : X) (k : ℕ) → List CanonicalFactor → List CanonicalFactor
    case-b-sub t s k [] = []
    case-b-sub t s k (cf ∷ cfs) = (case-b-sub-cf t s k cf) ++ (case-b-sub t s k cfs)


    -- It might be more proof-conducive to generate a candidate list then pick the best (if it's nonempty).
    smallest-sub : X → List CanonicalFactor → Maybe (X × ℕ)
    smallest-sub t [] = nothing
    smallest-sub t (form₁ _ _ ∷ cfs) = smallest-sub t cfs
    smallest-sub t (form₂ z y  b _ ∷ cfs) with t X≟ y
    smallest-sub t (form₂ z .t b _ ∷ cfs) | yes refl with smallest-sub t cfs
    smallest-sub t (form₂ z .t b _ ∷ cfs) | yes refl | nothing = just (z , b)
    smallest-sub t (form₂ z .t b _ ∷ cfs) | yes refl | just (s , k) = if ⌊ b ≤? k ⌋ then just (z , b) else just (s , k)
    smallest-sub t (form₂ z y  b _ ∷ cfs) | no  _ = smallest-sub t cfs
    smallest-sub t (form₃ _ _ _ _ ∷ cfs) = smallest-sub t cfs
    smallest-sub t (form₄ _ _ ∷ cfs) = smallest-sub t cfs
    smallest-sub t (failure ∷ cfs) = smallest-sub t cfs


    -- filter
    dropIneqsWith : X → List CanonicalFactor → List CanonicalFactor
    dropIneqsWith t [] = []
    dropIneqsWith t (cf ∷ cfs) = if ⌊ CF.is≠? cf ⌋ ∧ ⌊ t CF.∈? cf ⌋
      then dropIneqsWith t cfs
      else cf ∷ (dropIneqsWith t cfs)

    -- tail recursion might be painful for later proofs
    addIneqs : X → ℕ → List CanonicalFactor → List CanonicalFactor
    addIneqs t zero cfs = cfs
    addIneqs t (suc m) cfs = addIneqs t m (form₄ t m ∷ cfs)

    case-b : X → List CanonicalFactor → List CanonicalFactor
    case-b t cfs with smallest-sub t cfs
    ... | nothing      = dropIneqsWith t cfs
    ... | just (s , k) = addIneqs s k (case-b-sub t s k cfs)

    qe-prod : X → List CanonicalFactor → List CanonicalFactor
    qe-prod t cfs with CProd.kindOf t cfs
    qe-prod t cfs | kind₀ = cfs
    qe-prod t cfs | kind₁ = case-a t cfs
    qe-prod t cfs | kind₂ = case-b t cfs
    qe-prod t cfs | kind₃ = case-a t cfs
    
    qe-cf : X → List (List CanonicalFactor) → List (List CanonicalFactor)
    qe-cf t = Data.List.map (qe-prod t)

    -- The "expansion" of ∃t.φ. See p121.
    -- Given ∃t.φ, find an equivalent (and quantifier-free) ψ.
    -- In fact, t and φ will be given.
    -- It is assumed that φ is quantifier free.
    qe : X → QF → QF
    qe t φ = CForm.interpret (qe-cf t (toCF φ))


    qe-works-fwd : (t : X) (φ : QF) (a : ℕ) (e : Env) → ((t , a) ∷ e) satisfies φ → e satisfies (qe t φ)
    qe-works-fwd t φ a e sat = ?

    qe-works-bwd : (t : X) (φ : QF) (e : Env) → e satisfies (qe t φ) → Σ ℕ (λ a → ((t , a) ∷ e) satisfies φ)
    qe-works-bwd t φ e sat = ?
