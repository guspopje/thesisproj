open import Agda.Primitive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

module QE2 {X : Set} {_X≟_ : Decidable {A = X} _≡_ } where
  open import Common
  open import Data.Nat using (ℕ ; zero ; suc ; pred ; _≤_ ; z≤n ; s≤s ; _≤?_ ; _∸_ ; _>_) renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_)
  open import Data.Nat.Properties using (≰⇒>)
  open import Data.Nat.Properties.Simple using (+-comm ; +-assoc)


  open import Data.Bool using (Bool ; true ; false ; _∨_ ; _∧_ ; not ; if_then_else_ ; T) renaming (_≟_ to _B≟_)
  open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_ ; foldr ; all ; null)
  open import Data.Maybe using (Maybe ; just ; nothing)

  open ≡-Reasoning

{-
  open import SucNat.Base {X = X}
  open import FirstKind
  open import SucNat.FK {X = X}
  open import SucNat.DecVar {X = X} {_≟_ = _X≟_}
  open Proofs FKAxioms
-}

  data Base : Set where
    ∅ : Base
    var : X → Base

  data Term : Set where
    S : ℕ → Base → Term

  data Atom : Set where
    _==_ : Term → Term → Atom

{-
  QF : Set
  QF = FK Atom
-}

  data QF : Set where
    atom : Atom → QF
    ~_ : QF → QF
    _∪_ : QF → QF → QF

  _&_ : QF → QF → QF
  p₁ & p₂ = ~ ((~ p₁) ∪ (~ p₂))

  -- A factor for DNF, i.e. an atom or its negation.
  data Factor : Set where
    +F_ : Atom → Factor   -- an atom ("positive" occurrence)
    -F_ : Atom → Factor   -- the negation of an atom ("negative" occurrence)

  0=0 : Factor
  0=0 = +F (S zero ∅ == S zero ∅)

  0≠0 : Factor
  0≠0 = -F (S zero ∅ == S zero ∅)

  notnot : {b : Bool} → b ≡ not (not b)
  notnot {true} = refl
  notnot {false} = refl

  dual-and : Bool → Bool → Bool
  dual-and a b = not ((not a) ∨ (not b))

  ℕ≟-sym : (x y : ℕ) → ⌊ x ℕ≟ y ⌋ ≡ ⌊ y ℕ≟ x ⌋
  ℕ≟-sym x y with x ℕ≟ y | y ℕ≟ x
  ℕ≟-sym x y | yes x≡y | yes y≡x = refl
  ℕ≟-sym x y | yes x≡y | no  y≢x = contradiction x≡y (y≢x ∘ sym)
  ℕ≟-sym x y | no  x≢y | yes y≡x = contradiction y≡x (x≢y ∘ sym)
  ℕ≟-sym x y | no  x≢y | no  y≢x = refl

  dec-⇄ : {P Q : Set} {P? : Dec P} {Q? : Dec Q} → (P → Q) → (Q → P) → ⌊ P? ⌋ ≡ ⌊ Q? ⌋
  dec-⇄ {P? = P?} {Q? = Q?} f g with P? | Q?
  ... | yes _ | yes _ = refl
  ... | yes p | no ¬q = contradiction (f p) ¬q
  ... | no ¬p | yes q = contradiction (g q) ¬p
  ... | no  _ | no  _ = refl

  --ℕ≟-⇄ : {x₁ x₂ y₁ y₂ : ℕ} → ((x₁ ≡ x₂) → (y₁ ≡ y₂)) → ((y₁ ≡ y₂) → (x₁ ≡ x₂)) → ⌊ x₁ ℕ≟ x₂ ⌋ ≡ ⌊ y₁ ℕ≟ y₂ ⌋
  --ℕ≟-⇄ = dec-⇄

  ≡-+-comm : {a b c d : ℕ} → a ℕ+ b ≡ c ℕ+ d → b ℕ+ a ≡ d ℕ+ c
  ≡-+-comm {a} {b} {c} {d} eq = trans (+-comm b a) (trans eq (+-comm c d))

  pred* : {a b : ℕ} (n : ℕ) → n ℕ+ a ≡ n ℕ+ b → a ≡ b
  pred* zero refl = refl
  pred* (suc n) eq = pred* n (cong pred eq)

  pred*′ : {a b : ℕ} (n : ℕ) → a ℕ+ n ≡ b ℕ+ n → a ≡ b
  pred*′ {a} {b} n eq = pred* {a} {b} n (≡-+-comm {a} {n} {b} {n} eq)

  T≡ : {a b : ℕ} → T ⌊ a ℕ≟ b ⌋ → a ≡ b
  T≡ {a} {b} p with a ℕ≟ b
  ... | yes eq = eq
  ... | no  _  = ⊥-elim p

  ≡T : {a b : ℕ} → a ≡ b → T ⌊ a ℕ≟ b ⌋
  ≡T {a} {b} eq with a ℕ≟ b
  ... | yes _ = tt
  ... | no neq = contradiction eq neq

  --------------------------------------------
  -- EVALUATING QF PROPOSITIONS (SEMANTICS) --
  --------------------------------------------

  evalTerm : (X → ℕ) → Term → ℕ
  evalTerm e (S k ∅) = k
  evalTerm e (S k (var x)) = k ℕ+ (e x)

  evalAtom : (X → ℕ) → Atom → Bool
  evalAtom e (t₁ == t₂) = ⌊ (evalTerm e t₁) ℕ≟ (evalTerm e t₂) ⌋

  evalQF : (X → ℕ) → QF → Bool
  evalQF f (atom a) = evalAtom f a
  evalQF f (~ p) = not (evalQF f p)
  evalQF f (p₁ ∪ p₂) = (evalQF f p₁) ∨ (evalQF f p₂)

  

{-
  -- Evaluating a quantifier-free proposition ⇒ use the evaluation in FirstKind.agda, giving it the above means for evaluating atoms.
  evalQF : (X → ℕ) → QF → Bool
  evalQF e = eval (evalAtom e)
-}
  -- Semantic equivalence
--  _⇔_ : QF → QF → Set
--  p₁ ⇔ p₂ = (f : X → ℕ) → (evalQF f p₁ ≡ evalQF f p₂)

  {-
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
  ... | .x | yes refl = cong (λ z → k ℕ+ z) eq
  ... |  _ | no  diff = refl
  evalTerm-substitute x a e eq (S k (appa ()))

  -- Replacing a variable with the value it has does not alter the semantics.
  evalQF-substitute : (x : X) (a : ℕ) (e : X → ℕ) → e x ≡ a → (p : QF) → evalQF e p ≡ evalQF e (substitute x a p)
  evalQF-substitute x a e eq (atom (t₁ == t₂)) = cong₂ (λ m n → ⌊ m ℕ≟ n ⌋) (evalTerm-substitute x a e eq t₁) (evalTerm-substitute x a e eq t₂)
  evalQF-substitute x a e eq (~ p) = cong not (evalQF-substitute x a e eq p)
  evalQF-substitute x a e eq (p₁ ∪ p₂) = cong₂ _∨_ (evalQF-substitute x a e eq p₁) (evalQF-substitute x a e eq p₂)
  -}
  
  {-
  -- If P ≡ P', then (A & P) ≡ (A & P')
  &-≣ : {P P' : QF} (A : QF) → ⊢ P ≣ P' → ⊢ (A & P) ≣ (A & P')
  &-≣ {P} {P'} A eq = {!!}
  -}

  module Environment where
    depends-term : Term → X → Set
    depends-term (S k ∅) _ = ⊥
    depends-term (S k (var x)) t = t ≡ x


    Env : Set
    Env = List (X × ℕ)

    lookup : Env → X → ℕ
    lookup [] _ = zero
    lookup ((x , a) ∷ e) t = if ⌊ x X≟ t ⌋ then a else lookup e t

    eval : Env → QF → Bool
    eval e = evalQF (lookup e)

    _satisfies_ : Env → QF → Set
    e satisfies p = T (eval e p)

    _⇔_ : QF → QF → Set
    p₁ ⇔ p₂ = (e : Env) → (eval e p₁) ≡ (eval e p₂)
  
  

    {-
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

    nodep-sat-add : (p : QF) (x : X) (a : ℕ) (e : Env) → ¬ depends p x → e satisfies p → ((x , a) ∷ e) satisfies p
    nodep-sat-add p x a e nodep sat = subst T (sym (nodep-eval p e x a nodep)) sat

    nodep-sat-drop : (p : QF) (x : X) (a : ℕ) (e : Env) → ¬ depends p x → ((x , a) ∷ e) satisfies p → e satisfies p
    nodep-sat-drop p x a e nodep sat = subst T (nodep-eval p e x a nodep) sat

    Sat : QF → Set
    Sat p = Σ Env (λ e → e satisfies p)
    -}

  open Environment

  -- Some things about terms
  module T where
    _∈_ : X → Term → Set
    _ ∈ (S _ ∅) = ⊥
    x ∈ (S _ (var y)) = x ≡ y

    _∈?_ : (x : X) → (t : Term) → Dec (x ∈ t)
    _ ∈? (S _ ∅) = no (λ ())
    x ∈? (S _ (var y)) = x X≟ y

    add : ℕ → Term → Term
    add k (S a b) = S (k ℕ+ a) b

    replaceBase : Term → Term → Term
    replaceBase (S k x) (S a _) = S (a ℕ+ k) x

    dropBase : Term → Term
    dropBase (S a _) = S a ∅

    replaceBase-eval : (term : Term) (a : ℕ) (base : Base) (f : X → ℕ) → evalTerm f (replaceBase term (S a base)) ≡ a ℕ+ (evalTerm f term)
    replaceBase-eval (S b ∅) a base f = refl
    replaceBase-eval (S b (var s)) a base f = +-assoc a b (f s)

    add-eval : (k : ℕ) (term : Term) (f : X → ℕ) → evalTerm f (add k term) ≡ k ℕ+ (evalTerm f term)
    add-eval k (S a ∅) f = refl
    add-eval k (S a (var s)) f = +-assoc k a (f s)

    ∉-eval : (x : X) (t : Term) (a : ℕ) (e : Env) → ¬ x ∈ t → evalTerm (lookup ((x , a) ∷ e)) t ≡ evalTerm (lookup e) t
    ∉-eval x (S k ∅) a e _ = refl
    ∉-eval x (S k (var y)) a e x≢y with x X≟ y
    ... | yes x≡y = contradiction x≡y x≢y
    ... | no _ = refl

  -- Some things about atoms
  module A where
    _∈_ : X → Atom → Set
    x ∈ (t₁ == t₂) = (x T.∈ t₁) ⊎ (x T.∈ t₂)

    _∈?_ : (x : X) (a : Atom) → Dec (x ∈ a)
    x ∈? (t₁ == t₂) = (x T.∈? t₁) ⊎-dec (x T.∈? t₂)

    flip : Atom → Atom
    flip (t₁ == t₂) = t₂ == t₁

    flip-evalAtom : (f : X → ℕ) (a : Atom) → evalAtom f (flip a) ≡ evalAtom f a
    flip-evalAtom f (t₁ == t₂) = ℕ≟-sym (evalTerm f t₂) (evalTerm f t₁)

    i : Atom → QF
    i = atom

    ∉-eval : (t : X) (atm : Atom) (a : ℕ) (e : Env) → ¬ t ∈ atm → evalAtom (lookup ((t , a) ∷ e)) atm ≡ evalAtom (lookup e) atm
    ∉-eval t (t₁ == t₂) a e notin = cong₂ (λ x y → ⌊ x ℕ≟ y ⌋) (T.∉-eval t t₁ a e (notin ∘ inj₁)) (T.∉-eval t t₂ a e (notin ∘ inj₂))

{-
  depends : QF → X → Set
  depends (atom (t₁ == t₂)) x = depends-term t₁ x ⊎ depends-term t₂ x
  depends (~ p) x = depends p x
  depends (p₁ ∪ p₂) x = depends p₁ x ⊎ depends p₂ x
-}    

  depends : X → QF → Set
  depends x (atom a) = x A.∈ a
  depends x (~ p) = depends x p
  depends x (p₁ ∪ p₂) = depends x p₁ ⊎ depends x p₂

{-
  nodep-eval-term : (t : Term) (e : Env) (x : X) (a : ℕ) → ¬ depends-term t x → evalTerm (lookup ((x , a) ∷ e)) t ≡ evalTerm (lookup e) t
  nodep-eval-term (S k ∅) _ _ _ _ = refl
  nodep-eval-term (S k (var y)) e x a nodep with x X≟ y
  ... | yes same = contradiction same nodep
  ... | no  diff = refl
-}

  nodep-eval : (t : X) (p : QF) (a : ℕ) (e : Env) → ¬ depends t p → eval ((t , a) ∷ e) p ≡ eval e p
  nodep-eval t (atom atm) a e nodep = A.∉-eval t atm a e nodep
  nodep-eval t (~ p)      a e nodep = cong not (nodep-eval t p a e nodep)
  nodep-eval t (p₁ ∪ p₂)  a e nodep = cong₂ _∨_ (nodep-eval t p₁ a e (nodep ∘ inj₁)) (nodep-eval t p₂ a e (nodep ∘ inj₂))



  -- Various operations on Factors
  module F where
    interpret : Factor → QF
    interpret (+F a) = atom a
    interpret (-F a) = ~ (atom a)

    i : Factor → QF
    i = interpret

    _∈_ : X → Factor → Set
    x ∈ (+F a) = x A.∈ a
    x ∈ (-F a) = x A.∈ a
    
    _∈?_ : (x : X) → (f : Factor) → Dec (x ∈ f)
    x ∈? (+F a) = x A.∈? a
    x ∈? (-F a) = x A.∈? a

    _∉_ : X → Factor → Set
    x ∉ f = ¬ (x ∈ f)

    _∉?_ : (x : X) → (f : Factor) → Dec (x ∉ f)
    x ∉? f = ¬? (x ∈? f)

    lift₂ : ∀{α} {A : Set α} → (QF → QF → A) → (Factor → Factor → A)
    lift₂ g f₁ f₂ = g (interpret f₁) (interpret f₂)

    flip : Factor → Factor
    flip (+F a) = +F (A.flip a)
    flip (-F a) = -F (A.flip a)

    flip-⇔ : (f : Factor) → i (flip f) ⇔ i f
    flip-⇔ (+F a) e = A.flip-evalAtom (lookup e) a
    flip-⇔ (-F a) e = cong not (A.flip-evalAtom (lookup e) a)

{-
    depends : QF → X → Set
    depends (atom (t₁ == t₂)) x = depends-term t₁ x ⊎ depends-term t₂ x
    depends (~ p) x = depends p x
    depends (p₁ ∪ p₂) x = depends p₁ x ⊎ depends p₂ x
-}

    depends-∈ : (t : X) (f : Factor) → depends t (i f) → t ∈ f
    depends-∈ t (+F a) d = d
    depends-∈ t (-F a) d = d

    ∉-nodep : (t : X) (f : Factor) → ¬ t ∈ f → ¬ depends t (i f)
    ∉-nodep t f = contraposition (depends-∈ t f)

{-
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
    -}


  -- Various operations of products of factors
  module P where
    interpret : List Factor → QF
    interpret [] = F.interpret 0=0
    interpret (f ∷ fs) = (F.interpret f) & (interpret fs)

    i : List Factor → QF
    i = interpret

    lift₂ : ∀{α} {A : Set α} → (QF → QF → A) → (List Factor → List Factor → A)
    lift₂ g fs₁ fs₂ = g (interpret fs₁) (interpret fs₂)

    _∈_ : X → List Factor → Set
    t ∈ [] = ⊥
    t ∈ (f ∷ fs) = (t F.∈ f) ⊎ (t ∈ fs) 

    depends-∈ : (t : X) (fs : List Factor) → depends t (i fs) → t ∈ fs
    depends-∈ t [] (inj₁ ())
    depends-∈ t [] (inj₂ ())
    depends-∈ t (f ∷ fs) (inj₁ x) = inj₁ (F.depends-∈ t f x)
    depends-∈ t (f ∷ fs) (inj₂ y) = inj₂ (depends-∈ t fs y)

    ∉-nodep : (t : X) (fs : List Factor) → ¬ t ∈ fs → ¬ depends t (i fs)
    ∉-nodep t fs = contraposition (depends-∈ t fs)

    ++-∈ : (t : X) (fs₁ fs₂ : List Factor) → t ∈ (fs₁ ++ fs₂) → (t ∈ fs₁) ⊎ (t ∈ fs₂)
    ++-∈ t [] fs₂ meep = inj₂ meep
    ++-∈ t (f ∷ fs₁) fs₂ (inj₁ t∈f) = inj₁ (inj₁ t∈f)
    ++-∈ t (f ∷ fs₁) fs₂ (inj₂ t∈rest) with ++-∈ t fs₁ fs₂ t∈rest
    ++-∈ t (f ∷ fs₁) fs₂ (inj₂ t∈rest) | inj₁ t∈fs₁ = inj₁ (inj₂ t∈fs₁)
    ++-∈ t (f ∷ fs₁) fs₂ (inj₂ t∈rest) | inj₂ t∈fs₂ = inj₂ t∈fs₂


  sat-head : (e : Env) (f : Factor) (fs : List Factor) → e satisfies (P.i (f ∷ fs)) → e satisfies (F.i f)
  sat-head e f fs sat with eval e (F.i f)
  ... | true = tt
  ... | false = ⊥-elim sat

  sat-tail : (e : Env) (f : Factor) (fs : List Factor) → e satisfies (P.i (f ∷ fs)) → e satisfies (P.i fs)
  sat-tail e f fs sat with eval e (F.i f) | eval e (P.i fs)
  ... | true | true = tt
  ... | true | false = ⊥-elim sat
  ... | false | _ = ⊥-elim sat

  sat-∷ : (e : Env) (f : Factor) (fs : List Factor) → e satisfies (F.i f) → e satisfies (P.i fs) → e satisfies (P.i (f ∷ fs))
  sat-∷ e f fs satf satfs with eval e (F.i f) | eval e (P.i fs)
  sat-∷ e f fs satf satfs | true  | true = tt
  sat-∷ e f fs satf satfs | _     | false = ⊥-elim satfs
  sat-∷ e f fs satf satfs | false | true =  ⊥-elim satf
  
  

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

    mapAllP : {B : Set} {P : A → Set} (f : (a : A) → P a → B) (as : List A) → allP P as → List B
    mapAllP _ [] _ = []
    mapAllP f (a ∷ as) (pa , allpas) = f a pa ∷ mapAllP f as allpas

    remove : {a : A} {xs : List A} → a ∈ xs → List A
    remove (here a xs) = xs
    remove (there x a∈xs) = x ∷ remove a∈xs

    toFront : {a : A} {xs : List A} → a ∈ xs → List A
    toFront {a = a} it = a ∷ remove it

    catMaybes : List (Maybe A) → List A
    catMaybes [] = []
    catMaybes (nothing ∷ xs) = catMaybes xs
    catMaybes (just x ∷ xs) = x ∷ catMaybes xs

    first : (P : A → Set) (P? : (a : A) → Dec (P a))  (as : List A) → (Σ A (λ a → (P a) × (a ∈ as))) ⊎ (allP (¬_ ∘ P) as)
    first P P? [] = inj₂ tt
    first P P? (a ∷ as) with P? a
    first P P? (a ∷ as) | yes Pa = inj₁ (a , Pa , here a as)
    first P P? (a ∷ as) | no ¬Pa with first P P? as
    first P P? (a ∷ as) | no ¬Pa | inj₁ (a' , Pa' , a'∈as) = inj₁ (a' , Pa' , there a a'∈as)
    first P P? (a ∷ as) | no ¬Pa | inj₂ noneP = inj₂ (¬Pa , noneP)

  open L public using (here ; there ; allP)

  module QElim where

    subFactor : X → Factor → Set
    subFactor t (+F (term₁ == term₂)) = ((t T.∈ term₁) × (¬ (t T.∈ term₂))) ⊎ ((t T.∈ term₂) × (¬ (t T.∈ term₁)))
    subFactor _ (-F _) = ⊥

    subFactor? : (t : X) (f : Factor) → Dec (subFactor t f)
    subFactor? t (+F (term₁ == term₂)) = ((t T.∈? term₁) ×-dec (¬? (t T.∈? term₂))) ⊎-dec ((t T.∈? term₂) ×-dec (¬? (t T.∈? term₁)))
    subFactor? _ (-F _) = no (λ ())

    record Sub (t : X) : Set where
      constructor substitution
      field
        k : ℕ
        term : Term

--    data Sub (t : X) : Set where
--      substitution : ℕ → (term : Term) → Sub t

    getSub : (t : X) (f : Factor) → subFactor t f → Sub t
    getSub t (+F (S a ∅ == S b ∅)) (inj₁ (() , _))
    getSub t (+F (S a ∅ == S b ∅)) (inj₂ (() , _))
    getSub t (+F (S a ∅ == S b (var _))) (inj₁ (() , _))
    getSub t (+F (S a ∅ == S b (var .t))) (inj₂ (refl , _)) = substitution b (S a ∅)
    getSub t (+F (S a (var .t) == S b ∅)) (inj₁ (refl , _)) = substitution a (S b ∅)
    getSub t (+F (S a (var _) == S b ∅)) (inj₂ (() , _))
    getSub t (+F (S a (var .t) == S b (var s))) (inj₁ (refl , t∉R)) = substitution a (S b (var s))
    getSub t (+F (S a (var s) == S b (var .t))) (inj₂ (refl , t∉L)) = substitution b (S a (var s))
    getSub t (-F _) ()

    iSub : {t : X} → Sub t → Factor
    iSub {t} (substitution a term) = +F (S a (var t) == term)

    getSub-works : (t : X) (f : Factor) (sf : subFactor t f) → F.i (iSub (getSub t f sf)) ⇔ F.i f
    getSub-works t (+F (S a ∅ == S b ∅)) (inj₁ (() , _))
    getSub-works t (+F (S a ∅ == S b ∅)) (inj₂ (() , _))
    getSub-works t (+F (S a ∅ == S b (var _))) (inj₁ (() , _))
    getSub-works t (+F (S a ∅ == S b (var .t))) (inj₂ (refl , _)) e = F.flip-⇔ (+F (S a ∅ == S b (var t))) e
    getSub-works t (+F (S a (var .t) == S b ∅)) (inj₁ (refl , _)) e = refl
    getSub-works t (+F (S a (var _) == S b ∅)) (inj₂ (() , _))
    getSub-works t (+F (S a (var .t) == S b (var s))) (inj₁ (refl , t∉R)) e = refl 
    getSub-works t (+F (S a (var s) == S b (var .t))) (inj₂ (refl , t∉L)) e = F.flip-⇔ (+F (S a (var s) == S b (var t))) e
    getSub-works t (-F _) ()


    -- Replace a factor f with an equivalent one, under the assumption that f is not a substitution factor (and no others exist).
    -- Only job is to remove t; no need to deal with identities and contradictions.
    -- Inequalities involving just one of the variable 't' are replaced by 0=0; this is because as long as *no* subFactors exist,
    -- the only terms involving t will be tautologies (equiv to 0=0), contradictions (equiv to 0≠0), or inequalities. Thus t can
    -- be chosen to avoid violating any of the inequalities, as they are its only restrictions.
    replace-factor-nosub : (t : X) (f : Factor) → (¬ subFactor t f) → Factor
    replace-factor-nosub t (+F (S a ∅ == S b ∅)) _ = (+F (S a ∅ == S b ∅))
    replace-factor-nosub t (+F (S a ∅ == S b (var x))) _ = (+F (S a ∅ == S b (var x))) -- x≢t
    replace-factor-nosub t (+F (S a (var x) == S b ∅)) _ = (+F (S a (var x) == S b ∅)) -- x≢t
    replace-factor-nosub t (+F (S a (var x)  == S b (var y)))  nosub with t X≟ x | t X≟ y
    replace-factor-nosub t (+F (S a (var .t) == S b (var .t))) nosub | yes refl | yes refl = +F (S a ∅ == S b ∅)
    replace-factor-nosub t (+F (S a (var .t) == S b (var s)))  nosub | yes refl | no  t≢s  = contradiction (inj₁ (refl , t≢s)) nosub
    replace-factor-nosub t (+F (S a (var s)  == S b (var .t))) nosub | no  t≢s  | yes refl = contradiction (inj₂ (refl , t≢s)) nosub
    replace-factor-nosub t (+F (S a (var s)  == S b (var r)))  nosub | no  _    | no  _    = +F (S a (var s) == S b (var r))
    replace-factor-nosub t (-F (S a ∅ == S b ∅)) _ = (-F (S a ∅ == S b ∅))
    replace-factor-nosub t (-F (S a ∅ == S b (var x))) _ with t X≟ x
    replace-factor-nosub t (-F (S a ∅ == S b (var .t))) _ | yes refl = 0=0 -- can always satisfy inequality
    replace-factor-nosub t (-F (S a ∅ == S b (var x)))  _ | no _ = (-F (S a ∅ == S b (var x)))
    replace-factor-nosub t (-F (S a (var x) == S b ∅)) _ with t X≟ x
    replace-factor-nosub t (-F (S a (var .t) == S b ∅)) _ | yes refl = 0=0 -- can always satisfy inequality
    replace-factor-nosub t (-F (S a (var x) == S b ∅))  _ | no _ = (-F (S a (var x) == S b ∅))
    replace-factor-nosub t (-F (S a (var x)  == S b (var y))) _ with t X≟ x | t X≟ y
    replace-factor-nosub t (-F (S a (var .t)  == S b (var .t))) _ | yes refl | yes refl = (-F (S a ∅ == S b ∅))
    replace-factor-nosub t (-F (S a (var .t)  == S b (var y)))  _ | yes refl | no _ = 0=0
    replace-factor-nosub t (-F (S a (var x)  == S b (var .t)))  _ | no _ | yes refl = 0=0 -- same
    replace-factor-nosub t (-F (S a (var x)  == S b (var y)))   _ | no _ | no _ = (-F (S a (var x)  == S b (var y)))
    

    replace-atom-sub : (t : X) → Sub t → Atom → Atom
    replace-atom-sub t (substitution k term) (L == R) with t T.∈? L | t T.∈? R
    replace-atom-sub t (substitution k term) (L == R) | yes _ | yes _ = T.dropBase L == T.dropBase R
    replace-atom-sub t (substitution k term) (L == R) | yes _ | no  _ = T.replaceBase term L == T.add k R
    replace-atom-sub t (substitution k term) (L == R) | no  _ | yes _ = T.add k L == T.replaceBase term R
    replace-atom-sub t (substitution k term) (L == R) | no  _ | no  _ = L == R

    -- Replace instances of a variable t in an atom according to a substitution of the form t + k = term.
    replace-factor-sub : (t : X) → Sub t → Factor → Factor
    replace-factor-sub t sub (+F atm) = +F (replace-atom-sub t sub atm)
    replace-factor-sub t sub (-F atm) = -F (replace-atom-sub t sub atm)

    ineqs′ : ℕ → Term → List Factor
    ineqs′ zero _ = []
    ineqs′ (suc m) term = (-F (term == S m ∅)) ∷ (ineqs′ m term)

    -- term≠0, term≠1, ... , term≠(k-1)
    ineqs : {t : X} → Sub t → List Factor
    ineqs (substitution k term) = ineqs′ k term

    elim-prod : (t : X) → List Factor → List Factor
    elim-prod t fs with L.first (subFactor t) (subFactor? t) fs
    elim-prod t fs | inj₁ (f , fsub , _) = (ineqs (getSub t f fsub)) ++ (Data.List.map (replace-factor-sub t (getSub t f fsub)) fs)
    elim-prod t fs | inj₂ nonesub = L.mapAllP (replace-factor-nosub t) fs nonesub  

    
    

    nosub-factor-fwd : (t : X) (f : Factor) (ns : ¬ subFactor t f) (e : Env) → e satisfies (F.i f) → e satisfies (F.i (replace-factor-nosub t f ns))
    nosub-factor-fwd t (+F (S a ∅ == S b ∅)) _ e sat = sat
    nosub-factor-fwd t (+F (S a ∅ == S b (var x))) _ e sat = sat -- (+F (S a ∅ == S b (var x))) -- x≢t
    nosub-factor-fwd t (+F (S a (var x) == S b ∅)) _ e sat = sat -- (+F (S a (var x) == S b ∅)) -- x≢t
    nosub-factor-fwd t (+F (S a (var x)  == S b (var y)))  nosub e sat with t X≟ x | t X≟ y
    nosub-factor-fwd t (+F (S a (var .t) == S b (var .t))) nosub e sat | yes refl | yes refl = ≡T (pred*′ (lookup e t) (T≡ sat)) -- +F (S a ∅ == S b ∅)
    nosub-factor-fwd t (+F (S a (var .t) == S b (var s)))  nosub e sat | yes refl | no  t≢s  = contradiction (inj₁ (refl , t≢s)) nosub
    nosub-factor-fwd t (+F (S a (var s)  == S b (var .t))) nosub e sat | no  t≢s  | yes refl = contradiction (inj₂ (refl , t≢s)) nosub
    nosub-factor-fwd t (+F (S a (var s)  == S b (var r)))  nosub e sat | no  _    | no  _    = sat -- +F (S a (var s) == S b (var r))
    nosub-factor-fwd t (-F (S a ∅ == S b ∅)) _ e sat = sat -- (-F (S a ∅ == S b ∅))
    nosub-factor-fwd t (-F (S a ∅ == S b (var x))) _ e sat with t X≟ x
    nosub-factor-fwd t (-F (S a ∅ == S b (var .t))) _ e sat | yes refl = tt -- 0=0 -- can always satisfy inequality
    nosub-factor-fwd t (-F (S a ∅ == S b (var x)))  _ e sat | no _ = sat -- (-F (S a ∅ == S b (var x)))
    nosub-factor-fwd t (-F (S a (var x) == S b ∅)) _ e sat with t X≟ x
    nosub-factor-fwd t (-F (S a (var .t) == S b ∅)) _ e sat | yes refl = tt -- 0=0 -- can always satisfy inequality
    nosub-factor-fwd t (-F (S a (var x) == S b ∅))  _ e sat | no _ = sat -- (-F (S a (var x) == S b ∅))
    nosub-factor-fwd t (-F (S a (var x)  == S b (var y))) _ e sat with t X≟ x | t X≟ y
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var .t))) _ e sat | yes refl | yes refl with a ℕ≟ b -- (-F (S a ∅ == S b ∅))
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var .t))) _ e sat | yes refl | yes refl | yes a=b with a ℕ+ (lookup e t) ℕ≟ b ℕ+ (lookup e t)
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var .t))) _ e sat | yes refl | yes refl | yes a=b | yes a+t=b+t = ⊥-elim sat
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var .t))) _ e sat | yes refl | yes refl | yes a=b | no  a+t≠b+t = contradiction (cong (λ x → x ℕ+ (lookup e t)) a=b) a+t≠b+t
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var .t))) _ e sat | yes refl | yes refl | no  a≠b = tt
    nosub-factor-fwd t (-F (S a (var .t)  == S b (var y)))  _ e sat | yes refl | no _ = tt -- 0=0
    nosub-factor-fwd t (-F (S a (var x)  == S b (var .t)))  _ e sat | no _ | yes refl = tt -- 0=0 -- same
    nosub-factor-fwd t (-F (S a (var x)  == S b (var y)))   _ e sat | no _ | no _ = sat -- (-F (S a (var x)  == S b (var y)))

    nosub-fwd : (t : X) (fs : List Factor) (ns : allP (¬_ ∘ (subFactor t)) fs) (e : Env)
      → e satisfies (P.i fs)
      → e satisfies (P.i (L.mapAllP (replace-factor-nosub t) fs ns))
    nosub-fwd _ [] _ _ _ = tt
    nosub-fwd t (f ∷ fs) (fns , fsns) e sat = sat-∷ e (replace-factor-nosub t f fns) (L.mapAllP (replace-factor-nosub t) fs fsns)
      (nosub-factor-fwd t f fns e (sat-head e f fs sat))
      (nosub-fwd t fs fsns e (sat-tail e f fs sat)) 


    sub-lemma : (t : X) (k : ℕ) (term : Term) (e : Env) (a : ℕ) (foo : Term) → T (eval e (F.i (iSub (substitution k term))))
      → eval e (A.i (T.replaceBase term (S a (var t)) == T.add k foo)) ≡ eval e (A.i (S a (var t) == foo))
    sub-lemma t k term e a foo Tsub = dec-⇄
      (λ eq → pred* k (
        begin
          k ℕ+ (a ℕ+ (lookup e t))
        ≡⟨ sym (+-assoc k a (lookup e t)) ⟩
          (k ℕ+ a) ℕ+ (lookup e t)
        ≡⟨ cong (λ x → x ℕ+ (lookup e t)) (+-comm k a) ⟩
          (a ℕ+ k) ℕ+ (lookup e t)
        ≡⟨ +-assoc a k (lookup e t) ⟩
          a ℕ+ (k ℕ+ (lookup e t))
        ≡⟨ cong (λ x → a ℕ+ x) (T≡ Tsub) ⟩
          a ℕ+ (evalTerm (lookup e) term)
        ≡⟨ sym (T.replaceBase-eval term a (var t) (lookup e)) ⟩
          evalTerm (lookup e) (T.replaceBase term (S a (var t)))
        ≡⟨ eq ⟩
          evalTerm (lookup e) (T.add k foo)
        ≡⟨ T.add-eval k foo (lookup e) ⟩
          k ℕ+ (evalTerm (lookup e) foo)
        ∎))
      (λ a+t=rhs →
        begin
          evalTerm (lookup e) (T.replaceBase term (S a (var t)))
        ≡⟨ T.replaceBase-eval term a (var t) (lookup e) ⟩
          a ℕ+ (evalTerm (lookup e) term)
        ≡⟨ cong (λ x → a ℕ+ x) (sym (T≡ Tsub)) ⟩
          a ℕ+ (k ℕ+ (lookup e t))
        ≡⟨ sym (+-assoc a k (lookup e t)) ⟩
          (a ℕ+ k) ℕ+ (lookup e t)
        ≡⟨ cong (λ x → x ℕ+ (lookup e t)) (+-comm a k) ⟩
           (k ℕ+ a) ℕ+ (lookup e t)
        ≡⟨ +-assoc k a (lookup e t) ⟩
          k ℕ+ (a ℕ+ (lookup e t))
        ≡⟨ cong (λ x → k ℕ+ x) a+t=rhs ⟩ 
          k ℕ+ (evalTerm (lookup e) foo)
        ≡⟨ sym (T.add-eval k foo (lookup e)) ⟩
          evalTerm (lookup e) (T.add k foo)
        ∎)

    replace-atom-sub-equiv : (t : X) (sub : Sub t) (atm : Atom) (e : Env) → T (eval e (F.i (iSub sub)))
      → eval e (A.i (replace-atom-sub t sub atm)) ≡ eval e (A.i atm)
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub with L         | R             | t T.∈? L | t T.∈? R
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | S a (var .t) | S b (var .t)  | yes refl | yes refl = dec-⇄
      (cong (λ x → x ℕ+ (lookup e t)))
      (pred*′ (lookup e t))
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | S _ ∅        | _             | yes ()   | yes _
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | _            | S _ ∅         | yes _    | yes ()
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | S a (var .t) | R₁            | yes refl | no  _  = sub-lemma t k term e a R₁ Tsub
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | S _ ∅        | _             | yes ()   | no  _
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | L₁           | S a (var .t)  | no  _    | yes refl =
      trans (ℕ≟-sym _ _)
        (trans (sub-lemma t k term e a L₁ Tsub)
          (ℕ≟-sym _ _))
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | _            | S _ ∅         | no  _    | yes ()
    replace-atom-sub-equiv t (substitution k term) (L == R) e Tsub | L₁           | R₁            | no _     | no _     = refl



    ≤-or-≡ : {a b : ℕ} → a ≤ b → (suc a ≤ b) ⊎ (a ≡ b)
    ≤-or-≡ {zero}  {zero}  _ = inj₂ refl
    ≤-or-≡ {zero}  {suc b} _ = inj₁ (s≤s z≤n)
    ≤-or-≡ {suc a} {zero}  ()
    ≤-or-≡ {suc a} {suc b} (s≤s a≤b) with ≤-or-≡ a≤b
    ... | inj₁ sa≤b = inj₁ (s≤s sa≤b)
    ... | inj₂ a≡b  = inj₂ (cong suc a≡b)
    
    ineqs′-≤ : (k : ℕ) (term : Term) (e : Env) → e satisfies (P.i (ineqs′ k term)) → k ≤ evalTerm (lookup e) term
    ineqs′-≤ zero _ _ _ = z≤n
    ineqs′-≤ (suc k) term e sat with k ℕ≟ evalTerm (lookup e) term
    ineqs′-≤ (suc k) term e sat | yes k=term with evalTerm (lookup e) term ℕ≟ k
    ineqs′-≤ (suc k) term e sat | yes k=term | yes term=k = ⊥-elim sat
    ineqs′-≤ (suc k) term e sat | yes k=term | no  term≠k = contradiction (sym k=term) term≠k
    ineqs′-≤ (suc k) term e sat | no  k≠term with ineqs′-≤ k term e (sat-tail e (-F (term == S k ∅)) (ineqs′ k term) sat)
    ineqs′-≤ (suc k) term e sat | no  k≠term | k≤term with ≤-or-≡ k≤term
    ineqs′-≤ (suc k) term e sat | no  k≠term | k≤term | inj₁ sk≤term = sk≤term
    ineqs′-≤ (suc k) term e sat | no  k≠term | k≤term | inj₂ k=term = contradiction k=term k≠term

    subterm-∉ : (t : X) (f : Factor) (fsub : subFactor t f) → ¬ t T.∈ Sub.term (getSub t f fsub)
    subterm-∉ t (+F (S a ∅ == S b ∅)) (inj₁ (() , _))
    subterm-∉ t (+F (S a ∅ == S b ∅)) (inj₂ (() , _))
    subterm-∉ t (+F (S a ∅ == S b (var _))) (inj₁ (() , _))
    subterm-∉ t (+F (S a ∅ == S b (var .t))) (inj₂ (refl , _)) = λ ()
    subterm-∉ t (+F (S a (var .t) == S b ∅)) (inj₁ (refl , _)) = λ ()
    subterm-∉ t (+F (S a (var _) == S b ∅)) (inj₂ (() , _))
    subterm-∉ t (+F (S a (var .t) == S b (var s))) (inj₁ (refl , t∉R)) = t∉R
    subterm-∉ t (+F (S a (var s) == S b (var .t))) (inj₂ (refl , t∉L)) = t∉L
    subterm-∉ t (-F x) ()

    ineqs′-∈ : (t : X) (m : ℕ) (term : Term) → t P.∈ (ineqs′ m term) → t T.∈ term
    ineqs′-∈ t zero term ()
    ineqs′-∈ t (suc m) term (inj₁ (inj₁ t∈term)) = t∈term
    ineqs′-∈ t (suc m) term (inj₁ (inj₂ ()))
    ineqs′-∈ t (suc m) term (inj₂ y) = ineqs′-∈ t m term y

    ineqs-∉ : (t : X) (f : Factor) (fsub : subFactor t f) → ¬ t P.∈ ineqs (getSub t f fsub)
    ineqs-∉ t f fsub d = subterm-∉ t f fsub (ineqs′-∈ t (Sub.k (getSub t f fsub)) (Sub.term (getSub t f fsub)) d)

    

    elim-prod-elim : (t : X) (fs : List Factor) → ¬ t P.∈ (elim-prod t fs)
    elim-prod-elim t fs t∈ with L.first (subFactor t) (subFactor? t) fs
    elim-prod-elim t fs t∈ | inj₁ (f , fsub , _) with P.++-∈ t
      (ineqs (getSub t f fsub))
      (Data.List.map (replace-factor-sub t (getSub t f fsub)) fs)
      t∈
    elim-prod-elim t fs t∈ | inj₁ (f , fsub , _) | inj₁ t∈ineq = contradiction t∈ineq (ineqs-∉ t f fsub)
    elim-prod-elim t fs t∈ | inj₁ (f , fsub , _) | inj₂ t∈rest = {!!}
    elim-prod-elim t fs t∈ | inj₂ nonesub = {!!}


{-    

    elim-prod-drop : (t : X) (fs : List Factor) (a : ℕ) (e : Env)
      → ((t , a) ∷ e) satisfies (P.i (elim-prod t fs))
      → e satisfies (P.i (elim-prod t fs))
    elim-prod-drop t fs a e sat = subst T (nodep-eval (P.i (elim-prod t fs)) e t a (elim-prod-elim t fs)) sat

    elim-prod-fwd : (t : X) (fs : List Factor) (a : ℕ) (e : Env) → ((t , a) ∷ e) satisfies (P.i fs) → e satisfies (P.i (elim-prod t fs))
    elim-prod-fwd t fs a e sat with L.first (subFactor t) (subFactor? t) fs
    elim-prod-fwd t fs a e sat | inj₁ (f , fsub , thar) = {!!}
    elim-prod-fwd t fs a e sat | inj₂ nonesub = {!!}
-}
{-
    elim-prod : (t : X) → List Factor → List Factor
    elim-prod t fs with L.first (subFactor t) (subFactor? t) fs
    elim-prod t fs | inj₁ (f , fsub , _) = (ineqs (getSub t f fsub)) ++ (Data.List.map (replace-factor-sub t (getSub t f fsub)) fs)
    elim-prod t fs inj₂ nonesub = L.mapAllP (replace-factor-nosub t) fs nonesub  
-}
