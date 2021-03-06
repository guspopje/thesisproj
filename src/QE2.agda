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

  data Base : Set where
    ∅ : Base
    var : X → Base

  data Term : Set where
    S : ℕ → Base → Term

  data Atom : Set where
    _==_ : Term → Term → Atom

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

  F≢ : {a b : ℕ} → T (not ⌊ a ℕ≟ b ⌋) → ¬ a ≡ b
  F≢ {a} {b } p with a ℕ≟ b
  ... | yes eq = ⊥-elim p
  ... | no neq = neq

  ≢F : {a b : ℕ} → ¬ a ≡ b → T (not ⌊ a ℕ≟ b ⌋)
  ≢F {a} {b} neq with a ℕ≟ b
  ... | yes eq = contradiction eq neq
  ... | no  _  = tt



  evalTerm : (X → ℕ) → Term → ℕ
  evalTerm e (S k ∅) = k
  evalTerm e (S k (var x)) = k ℕ+ (e x)

  evalAtom : (X → ℕ) → Atom → Bool
  evalAtom e (t₁ == t₂) = ⌊ (evalTerm e t₁) ℕ≟ (evalTerm e t₂) ⌋

  evalQF : (X → ℕ) → QF → Bool
  evalQF f (atom a) = evalAtom f a
  evalQF f (~ p) = not (evalQF f p)
  evalQF f (p₁ ∪ p₂) = (evalQF f p₁) ∨ (evalQF f p₂)


  module Environment where

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

  open Environment


  module B where
    _∈_ : X → Base → Set
    _ ∈ ∅ = ⊥
    x ∈ (var y) = x ≡ y

    _∈?_ : (x : X) (b : Base) → Dec (x ∈ b)
    _ ∈? ∅ = no (λ ())
    x ∈? (var y) = x X≟ y


  -- Some things about terms
  module T where
    _∈_ : X → Term → Set
    x ∈ (S _ b) = x B.∈ b

    _∈?_ : (x : X) → (t : Term) → Dec (x ∈ t)
    x ∈? (S _ b) = x B.∈? b

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

    swap : Atom → Atom
    swap (t₁ == t₂) = t₂ == t₁

    swap-evalAtom : (f : X → ℕ) (a : Atom) → evalAtom f (swap a) ≡ evalAtom f a
    swap-evalAtom f (t₁ == t₂) = ℕ≟-sym (evalTerm f t₂) (evalTerm f t₁)

    i : Atom → QF
    i = atom

    ∉-eval : (t : X) (atm : Atom) (a : ℕ) (e : Env) → ¬ t ∈ atm → evalAtom (lookup ((t , a) ∷ e)) atm ≡ evalAtom (lookup e) atm
    ∉-eval t (t₁ == t₂) a e notin = cong₂ (λ x y → ⌊ x ℕ≟ y ⌋) (T.∉-eval t t₁ a e (notin ∘ inj₁)) (T.∉-eval t t₂ a e (notin ∘ inj₂))


  depends : X → QF → Set
  depends x (atom a) = x A.∈ a
  depends x (~ p) = depends x p
  depends x (p₁ ∪ p₂) = depends x p₁ ⊎ depends x p₂

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

    swap : Factor → Factor
    swap (+F a) = +F (A.swap a)
    swap (-F a) = -F (A.swap a)

    swap-⇔ : (f : Factor) → i (swap f) ⇔ i f
    swap-⇔ (+F a) e = A.swap-evalAtom (lookup e) a
    swap-⇔ (-F a) e = cong not (A.swap-evalAtom (lookup e) a)

    depends-∈ : (t : X) (f : Factor) → depends t (i f) → t ∈ f
    depends-∈ t (+F a) d = d
    depends-∈ t (-F a) d = d

    ∉-nodep : (t : X) (f : Factor) → ¬ t ∈ f → ¬ depends t (i f)
    ∉-nodep t f = contraposition (depends-∈ t f)

    ∉-eval : (t : X) (f : Factor) (a : ℕ) (e : Env) → ¬ t ∈ f → eval ((t , a) ∷ e) (i f) ≡ eval e (i f)
    ∉-eval t (+F atm) a e t∉f = A.∉-eval t atm a e t∉f
    ∉-eval t (-F atm) a e t∉f = cong not (A.∉-eval t atm a e t∉f)

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
  
  sat-++ : (e : Env) (fs₁ fs₂ : List Factor) → e satisfies (P.i fs₁) → e satisfies (P.i fs₂) → e satisfies (P.i (fs₁ ++ fs₂))
  sat-++ e [] fs₂ _ sat₂ = sat₂
  sat-++ e (f ∷ fs₁) fs₂ sat₁ sat₂ = sat-∷ e f (fs₁ ++ fs₂) (sat-head e f fs₁ sat₁) (sat-++ e fs₁ fs₂ (sat-tail e f fs₁ sat₁) sat₂)

  sat-++₁ : (e : Env) (fs₁ fs₂ : List Factor) → e satisfies (P.i (fs₁ ++ fs₂)) → e satisfies (P.i fs₁)
  sat-++₁ _ [] _ _ = tt
  sat-++₁ e (f ∷ fs₁) fs₂ sat = sat-∷ e f fs₁ (sat-head e f (fs₁ ++ fs₂) sat) (sat-++₁ e fs₁ fs₂ (sat-tail e f (fs₁ ++ fs₂) sat))

  sat-++₂ : (e : Env) (fs₁ fs₂ : List Factor) → e satisfies (P.i (fs₁ ++ fs₂)) → e satisfies (P.i fs₂)
  sat-++₂ _ [] _ sat = sat
  sat-++₂ e (f ∷ fs₁) fs₂ sat = sat-++₂ e fs₁ fs₂ (sat-tail e f (fs₁ ++ fs₂) sat)

  -- Various operations on sums of products of factors (i.e., dnf)
  module SoP where
    i : List (List Factor) → QF
    i [] = F.i 0≠0
    i (p ∷ ps) = (P.i p) ∪ (i ps)


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

    ∈-++₁ : (a : A) (xs ys : List A) → a ∈ xs → a ∈ (xs ++ ys)
    ∈-++₁ a [] ys ()
    ∈-++₁ a (.a ∷ xs) ys (here .a .xs) = here a (xs ++ ys)
    ∈-++₁ a (x ∷ xs) ys (there .x x∈xs) = there x (∈-++₁ a xs ys x∈xs)

    ∈-++₂ : (a : A) (xs ys : List A) → a ∈ ys → a ∈ (xs ++ ys)
    ∈-++₂ a [] ys a∈ys = a∈ys
    ∈-++₂ a (x ∷ xs) ys a∈ys = there x (∈-++₂ a xs ys a∈ys)

    first : (P : A → Set) (P? : (a : A) → Dec (P a))  (as : List A) → (Σ A (λ a → (P a) × (a ∈ as))) ⊎ (allP (¬_ ∘ P) as)
    first P P? [] = inj₂ tt
    first P P? (a ∷ as) with P? a
    first P P? (a ∷ as) | yes Pa = inj₁ (a , Pa , here a as)
    first P P? (a ∷ as) | no ¬Pa with first P P? as
    first P P? (a ∷ as) | no ¬Pa | inj₁ (a' , Pa' , a'∈as) = inj₁ (a' , Pa' , there a a'∈as)
    first P P? (a ∷ as) | no ¬Pa | inj₂ noneP = inj₂ (¬Pa , noneP)

  open L public using (here ; there ; allP)

  module QElim where

    data Dir : Set where
      LR : Dir
      RL : Dir

    orient : Dir → Term → Term → Factor
    orient LR t₁ t₂ = +F (t₁ == t₂)
    orient RL t₁ t₂ = +F (t₂ == t₁)

    data subFactor (t : X) : Factor → Set where
      -- sub : (d : Dir) (k : ℕ) (term : Term) → ¬ t T.∈ term → subFactor t (orient d (S k (var t)) term)
      subL : (k : ℕ) (term : Term) → ¬ t T.∈ term → subFactor t (+F (S k (var t) == term))
      subR : (k : ℕ) (term : Term) → ¬ t T.∈ term → subFactor t (+F (term == S k (var t)))

    -- Sufficient criteria for being a subFactor
    sub-criteria : {t : X} {L R : Term} → ((t T.∈ L) × (¬ t T.∈ R)) ⊎ ((t T.∈ R) × (¬ t T.∈ L)) → subFactor t (+F (L == R))
    sub-criteria {t} {S k (var .t)} {term} (inj₁ (refl , t∉term)) = subL k term t∉term
    sub-criteria {t} {S k ∅} {term} (inj₁ (() , _))
    sub-criteria {t} {term} {S k (var .t)} (inj₂ (refl , t∉term)) = subR k term t∉term
    sub-criteria {t} {term} {S k ∅} (inj₂ (() , _))

    -- Criteria are necessary as well
    sub-criteria′ : {t : X} {L R : Term} → subFactor t (+F (L == R)) → ((t T.∈ L) × (¬ t T.∈ R)) ⊎ ((t T.∈ R) × (¬ t T.∈ L))
    sub-criteria′ {t} {S .k (var .t)} {.term} (subL k term t∉term) = inj₁ (refl , t∉term)
    sub-criteria′ {t} {.term} {S .k (var .t)} (subR k term t∉term) = inj₂ (refl , t∉term)

    subFactor? : (t : X) (f : Factor) → Dec (subFactor t f)
    subFactor? t (+F (L == R)) with            t T.∈? L | t T.∈? R
    subFactor? t (+F (L == R))               | yes t∈L  | yes t∈R  = no
      ([ contradiction t∈R ∘ proj₂ , contradiction t∈L ∘ proj₂ ]′ ∘ sub-criteria′)
    subFactor? t (+F (S k (var .t) == term)) | yes refl | no  t∉R  = yes (subL k term t∉R)
    subFactor? t (+F (S _ ∅ == _))           | yes ()   | no _
    subFactor? t (+F (term == S k (var .t))) | no  t∉L  | yes refl = yes (subR k term t∉L)
    subFactor? t (+F (_ == S _ ∅))           | no  _    | yes ()
    subFactor? t (+F (L == R))               | no  t∉L  | no  t∉R  = no
      ([ flip contradiction t∉L ∘ proj₁ , flip contradiction t∉R ∘ proj₁ ]′ ∘ sub-criteria′)
    subFactor? t (-F _) = no (λ ())    

    record Sub (t : X) : Set where
      constructor substitution
      field
        k : ℕ
        term : Term

    getSub : (t : X) (f : Factor) → subFactor t f → Sub t
    getSub t _ (subL k term _) = substitution k term
    getSub t _ (subR k term _) = substitution k term

    iSub : {t : X} → Sub t → Factor
    iSub {t} (substitution k term) = +F (S k (var t) == term)

    getSub-works : (t : X) (f : Factor) (sf : subFactor t f) → F.i (iSub (getSub t f sf)) ⇔ F.i f
    getSub-works t (+F (S .k (var .t) == .term)) (subL k term _) e = refl
    getSub-works t (+F (.term == S .k (var .t))) (subR k term _) e = F.swap-⇔ (+F (term == S k (var t))) e


    -- Replace a factor f with an equivalent one, under the assumption that f is not a substitution factor (and no others exist).
    -- Only job is to remove t; no need to deal with identities and contradictions.
    -- Inequalities involving just one of the variable 't' are replaced by 0=0; this is because as long as *no* subFactors exist,
    -- the only terms involving t will be tautologies (equiv to 0=0), contradictions (equiv to 0≠0), or inequalities. Thus t can
    -- be chosen to avoid violating any of the inequalities, as they are its only restrictions.
    replace-factor-nosub : (t : X) (f : Factor) → (¬ subFactor t f) → Factor
    replace-factor-nosub t (+F (L == R)) ns with t T.∈? L | t T.∈? R
    replace-factor-nosub t (+F (L == R)) ns | yes _   | yes _   = +F (T.dropBase L == T.dropBase R)
    replace-factor-nosub t (+F (L == R)) ns | yes t∈L | no  t∉R = contradiction (sub-criteria (inj₁ (t∈L , t∉R))) ns
    replace-factor-nosub t (+F (L == R)) ns | no  t∉L | yes t∈R = contradiction (sub-criteria (inj₂ (t∈R , t∉L))) ns
    replace-factor-nosub t (+F (L == R)) ns | no  _   | no  _   = +F (L == R)
    replace-factor-nosub t (-F (L == R)) ns with t T.∈? L | t T.∈? R
    replace-factor-nosub t (-F (L == R)) ns | yes _ | yes _ = -F (T.dropBase L == T.dropBase R)
    replace-factor-nosub t (-F (L == R)) ns | yes _ | no  _ = 0=0
    replace-factor-nosub t (-F (L == R)) ns | no  _ | yes _ = 0=0
    replace-factor-nosub t (-F (L == R)) ns | no  _ | no  _ = -F (L == R)

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

  open QElim  
    

  -- ∉
  module DoesElim where

    subterm-∉ : (t : X) (f : Factor) (fsub : subFactor t f) → ¬ t T.∈ Sub.term (getSub t f fsub)
    subterm-∉ t _ (subL _ term t∉term) = t∉term
    subterm-∉ t _ (subR _ term t∉term) = t∉term

    dropBase-∉ : (t : X) (term : Term) → ¬ t T.∈ T.dropBase term
    dropBase-∉ t (S a ∅) = λ ()
    dropBase-∉ t (S a b) = λ ()

    ineqs′-∈ : (t : X) (m : ℕ) (term : Term) → t P.∈ (ineqs′ m term) → t T.∈ term
    ineqs′-∈ t zero term ()
    ineqs′-∈ t (suc m) term (inj₁ (inj₁ t∈term)) = t∈term
    ineqs′-∈ t (suc m) term (inj₁ (inj₂ ()))
    ineqs′-∈ t (suc m) term (inj₂ y) = ineqs′-∈ t m term y

    ineqs-∉ : (t : X) (f : Factor) (fsub : subFactor t f) → ¬ t P.∈ ineqs (getSub t f fsub)
    ineqs-∉ t f fsub d = subterm-∉ t f fsub (ineqs′-∈ t (Sub.k (getSub t f fsub)) (Sub.term (getSub t f fsub)) d)

    replaceBase-∈ : (t : X) (term : Term) (term₀ : Term) → t T.∈ (T.replaceBase term term₀) → t T.∈ term
    replaceBase-∈ t (S k b) (S a _) t∈ = t∈

    replace-atom-sub-∈ : (t : X) (s : Sub t) (a : Atom) → t A.∈ replace-atom-sub t s a → t T.∈ Sub.term s
    replace-atom-sub-∈ t (substitution k term) (L == R) t∈ with t T.∈? L | t T.∈? R
    replace-atom-sub-∈ t (substitution k term) (L == R) t∈ | yes _ | yes _ = ⊥-elim ([ dropBase-∉ t L , dropBase-∉ t R ]′ t∈)
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | yes _  | no t∉R with t∈
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | yes _  | no t∉R | inj₁ t∈L' = replaceBase-∈ t term (S a l) t∈L'
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | yes _  | no t∉R | inj₂ t∈R' = contradiction t∈R' t∉R
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | no t∉L | yes _  with t∈
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | no t∉L | yes _  | inj₁ t∈L' = contradiction t∈L' t∉L
    replace-atom-sub-∈ t (substitution k term) (S a l == S b r) t∈ | no t∉L | yes _  | inj₂ t∈R' = replaceBase-∈ t term (S b r) t∈R'
    replace-atom-sub-∈ t (substitution k term) (L == R) t∈ | no t∉L | no t∉R = ⊥-elim ([ t∉L , t∉R ]′ t∈)
    
    replace-factor-sub-∈ : (t : X) (s : Sub t) (f : Factor) → t F.∈ replace-factor-sub t s f → t T.∈ Sub.term s
    replace-factor-sub-∈ t s (+F atm) = replace-atom-sub-∈ t s atm
    replace-factor-sub-∈ t s (-F atm) = replace-atom-sub-∈ t s atm

    replace-prod-sub-∈ : (t : X) (s : Sub t) (fs : List Factor) → t P.∈ (Data.List.map (replace-factor-sub t s) fs) → t T.∈ Sub.term s
    replace-prod-sub-∈ _ _ [] ()
    replace-prod-sub-∈ t s (f ∷ fs) (inj₁ t∈f')  = replace-factor-sub-∈ t s f t∈f'
    replace-prod-sub-∈ t s (f ∷ fs) (inj₂ t∈fs') = replace-prod-sub-∈ t s fs t∈fs'

    replace-factor-nosub-∉ : (t : X) (f : Factor) (ns : ¬ subFactor t f) → ¬ t F.∈ replace-factor-nosub t f ns
    replace-factor-nosub-∉ t (+F (L == R)) ns with t T.∈? L | t T.∈? R
    replace-factor-nosub-∉ t (+F (L == R)) ns | yes _   | yes _   = [ dropBase-∉ t L , dropBase-∉ t R ]′
    replace-factor-nosub-∉ t (+F (L == R)) ns | yes t∈L | no  t∉R = contradiction (sub-criteria (inj₁ (t∈L , t∉R))) ns
    replace-factor-nosub-∉ t (+F (L == R)) ns | no  t∉L | yes t∈R = contradiction (sub-criteria (inj₂ (t∈R , t∉L))) ns
    replace-factor-nosub-∉ t (+F (L == R)) ns | no  t∉L | no  t∉R = [ t∉L , t∉R ]′ -- +F (L == R)
    replace-factor-nosub-∉ t (-F (L == R)) ns with t T.∈? L | t T.∈? R
    replace-factor-nosub-∉ t (-F (L == R)) ns | yes _   | yes _  = [ dropBase-∉ t L , dropBase-∉ t R ]′ -- -F (T.dropBase L == T.dropBase R)
    replace-factor-nosub-∉ t (-F (L == R)) ns | yes _   | no  _  = [ (λ ()) , (λ ()) ]′
    replace-factor-nosub-∉ t (-F (L == R)) ns | no  _   | yes _  = [ (λ ()) , (λ ()) ]′
    replace-factor-nosub-∉ t (-F (L == R)) ns | no  t∉L | no t∉R = [ t∉L , t∉R ]′ -- -F (L == R)

    replace-prod-nosub-∉ : (t : X) (fs : List Factor) (ns : allP (¬_ ∘ subFactor t) fs)
      → ¬ t P.∈ L.mapAllP (replace-factor-nosub t) fs ns
    replace-prod-nosub-∉ _ [] _ ()
    replace-prod-nosub-∉ t (f ∷ fs) (fns , fsns) = [ replace-factor-nosub-∉ t f fns , replace-prod-nosub-∉ t fs fsns ]′

    elim-prod-∉ : (t : X) (fs : List Factor) → ¬ t P.∈ (elim-prod t fs)
    elim-prod-∉ t fs t∈ with L.first (subFactor t) (subFactor? t) fs
    elim-prod-∉ t fs t∈ | inj₁ (f , fsub , _) with P.++-∈ t
      (ineqs (getSub t f fsub))
      (Data.List.map (replace-factor-sub t (getSub t f fsub)) fs)
      t∈
    elim-prod-∉ t fs t∈ | inj₁ (f , fsub , _) | inj₁ t∈ineq = contradiction t∈ineq (ineqs-∉ t f fsub)
    elim-prod-∉ t fs t∈ | inj₁ (f , fsub , _) | inj₂ t∈rest = contradiction
      (replace-prod-sub-∈ t (getSub t f fsub) fs t∈rest)
      (subterm-∉ t f fsub)
    elim-prod-∉ t fs t∈ | inj₂ nonesub = replace-prod-nosub-∉ t fs nonesub t∈

  open DoesElim

  module Equiv where

    nosub-factor-fwd : (t : X) (f : Factor) (ns : ¬ subFactor t f) (e : Env) → e satisfies (F.i f) → e satisfies (F.i (replace-factor-nosub t f ns))
    nosub-factor-fwd t (+F (L == R)) ns e sat with t T.∈? L | t T.∈? R
    nosub-factor-fwd t (+F ((S a (var .t)) == (S b (var .t)))) ns e sat | yes refl | yes refl = ≡T (pred*′ (lookup e t) (T≡ sat)) -- +F (T.dropBase L == T.dropBase R)
    nosub-factor-fwd t (+F ((S _ ∅) == _)) ns e sat | yes () | yes _
    nosub-factor-fwd t (+F (_ == (S _ ∅))) ns e sat | yes _ | yes ()
    nosub-factor-fwd t (+F (L == R)) ns e sat | yes t∈L | no  t∉R = contradiction (sub-criteria (inj₁ (t∈L , t∉R))) ns
    nosub-factor-fwd t (+F (L == R)) ns e sat | no  t∉L | yes t∈R = contradiction (sub-criteria (inj₂ (t∈R , t∉L))) ns
    nosub-factor-fwd t (+F (L == R)) ns e sat | no  _   | no  _   = sat -- +F (L == R)
    nosub-factor-fwd t (-F (L == R)) ns e sat with t T.∈? L | t T.∈? R
    nosub-factor-fwd t (-F ((S a (var .t)) == (S b (var .t)))) ns e sat | yes refl | yes refl = ≢F ((F≢ sat) ∘ cong (λ x → x ℕ+ (lookup e t))) -- -F (T.dropBase L == T.dropBase R)
    nosub-factor-fwd t (-F ((S _ ∅) == _)) ns e sat | yes () | yes _
    nosub-factor-fwd t (-F (_ == (S _ ∅))) ns e sat | yes _ | yes ()
    nosub-factor-fwd t (-F (L == R)) ns e sat | yes _ | no  _ = tt -- 0=0
    nosub-factor-fwd t (-F (L == R)) ns e sat | no  _ | yes _ = tt -- 0=0
    nosub-factor-fwd t (-F (L == R)) ns e sat | no  _ | no  _ = sat -- -F (L == R)

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

    replace-atom-sub-equiv : (t : X) (sub : Sub t) (atm : Atom) (e : Env) → e satisfies (F.i (iSub sub))
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

    replace-factor-sub-equiv : (t : X) (sub : Sub t) (f : Factor) (e : Env) → e satisfies (F.i (iSub sub))
      → eval e (F.i (replace-factor-sub t sub f)) ≡ eval e (F.i f)
    replace-factor-sub-equiv t sub (+F atm) e Tsub = replace-atom-sub-equiv t sub atm e Tsub
    replace-factor-sub-equiv t sub (-F atm) e Tsub = cong not (replace-atom-sub-equiv t sub atm e Tsub)

    replace-prod-sub-equiv : (t : X) (sub : Sub t) (fs : List Factor) (e : Env)
      → e satisfies (F.i (iSub sub))
      → eval e (P.i (Data.List.map (replace-factor-sub t sub) fs)) ≡ eval e (P.i fs)
    replace-prod-sub-equiv _ _ [] _ _ = refl
    replace-prod-sub-equiv t sub (f ∷ fs) e Tsub = cong₂ dual-and (replace-factor-sub-equiv t sub f e Tsub) (replace-prod-sub-equiv t sub fs e Tsub)

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

    pred≤ : {a b : ℕ} → (suc a) ≤ b → a ≤ b
    pred≤ {zero} _ = z≤n
    pred≤ {suc a} {zero} ()
    pred≤ {suc a} {suc b} (s≤s sa≤b) = s≤s (pred≤ sa≤b)

    <-≢ : {a b : ℕ} → (suc a) ≤ b → ¬ a ≡ b
    <-≢ {_} {zero} ()
    <-≢ {zero} {suc b} _ = λ ()
    <-≢ {suc a} {suc b} (s≤s sa≤b) = (<-≢ sa≤b) ∘ (cong pred)

    ≤-ineqs′-helper : (k : ℕ) (term : Term) (e : Env) → (suc k) ≤ (evalTerm (lookup e) term) → e satisfies (F.i (-F (term == S k ∅)))
    ≤-ineqs′-helper k term e sk≤term with evalTerm (lookup e) term
    ≤-ineqs′-helper k term e sk≤y | y = ≢F ((<-≢ sk≤y) ∘ sym)

    ≤-ineqs′ : (k : ℕ) (term : Term) (e : Env) → k ≤ (evalTerm (lookup e) term) → e satisfies (P.i (ineqs′ k term))
    ≤-ineqs′ zero _ _ _ = tt
    ≤-ineqs′ (suc k) term e sk≤term = sat-∷ e (-F (term == S k ∅)) (ineqs′ k term) (≤-ineqs′-helper k term e sk≤term) (≤-ineqs′ k term e (pred≤ sk≤term))
    
    ∈-sat : (f : Factor) (fs : List Factor) → f L.∈ fs → (e : Env) → e satisfies (P.i fs) → e satisfies (F.i f)
    ∈-sat _ [] ()
    ∈-sat f (.f ∷ .fs) (here .f fs)  e = sat-head e f fs
    ∈-sat f (f' ∷ fs) (there _ f∈fs) e = ∈-sat f fs f∈fs e ∘ sat-tail e f' fs

    -- Unrelated the the previous, confusing naming
    ∉-sat : (t : X) (fs : List Factor) (a : ℕ) (e : Env) → ¬ t P.∈ fs → ((t , a) ∷ e) satisfies (P.i fs) → e satisfies (P.i fs)
    ∉-sat t fs a e t∉fs sat = subst T (nodep-eval t (P.i fs) a e (P.∉-nodep t fs t∉fs)) sat

    ∉-sat′ : (t : X) (fs : List Factor) (a : ℕ) (e : Env) → ¬ t P.∈ fs → e satisfies (P.i fs) → ((t , a) ∷ e) satisfies (P.i fs)
    ∉-sat′ t fs a e t∉fs sat = subst T (sym (nodep-eval t (P.i fs) a e (P.∉-nodep t fs t∉fs))) sat

    ≡-≤ : {a b : ℕ} → a ≡ b → a ≤ b
    ≡-≤ {zero} {.zero} refl = z≤n
    ≡-≤ {suc a} {suc .a} refl = s≤s (≡-≤ refl)

    ≤-suc : {a b : ℕ} → a ≤ b → a ≤ suc b
    ≤-suc z≤n = z≤n
    ≤-suc (s≤s a≤b) = s≤s (≤-suc a≤b)

    suc-≰ : (a : ℕ) → ¬ (suc a) ≤ a
    suc-≰ zero ()
    suc-≰ (suc a) (s≤s sa≤a) = suc-≰ a sa≤a

    +≤₂ : (a b c : ℕ) → a ℕ+ b ≤ c → b ≤ c
    +≤₂ zero b c b≤c = b≤c
    +≤₂ (suc a) b zero ()
    +≤₂ (suc a) b (suc c) (s≤s a+b≤c) = ≤-suc (+≤₂ a b c a+b≤c)

    +≤₁ : (a b c : ℕ) → a ℕ+ b ≤ c → a ≤ c
    +≤₁ a b c a+b≤c = +≤₂ b a c (subst (λ z → z ≤ c) (+-comm a b) a+b≤c)

    ≤-lemma′ : (a b c : ℕ) → a ℕ+ b ≡ c → b ≤ c
    ≤-lemma′ zero b c eq = ≡-≤ eq
    ≤-lemma′ (suc a) b (suc c) eq = ≤-suc (≤-lemma′ a b c (cong pred eq))
    ≤-lemma′ (suc _) _ zero ()

    ≤-lemma : (a b c : ℕ) → a ℕ+ b ≡ c → a ≤ c
    ≤-lemma a b c eq = ≤-lemma′ b a c (trans (+-comm b a) eq)

    ineqs-sub : (t : X) (f : Factor) (fsub : subFactor t f) (e : Env) → e satisfies (F.i f) → e satisfies (P.i (ineqs (getSub t f fsub)))
    ineqs-sub t (+F (S .k (var .t) == .term)) (subL k term _) e sat = ≤-ineqs′ k term e
      (≤-lemma k (lookup e t) (evalTerm (lookup e) term) (T≡ sat))
    ineqs-sub t (+F (.term == S .k (var .t))) (subR k term _) e sat = ≤-ineqs′ k term e
      (≤-lemma k (lookup e t) (evalTerm (lookup e) term) (sym (T≡ sat)))

    elim-fwd′ : (t : X) (fs : List Factor) (e : Env)
      → e satisfies (P.i fs)
      → e satisfies (P.i (elim-prod t fs))
    elim-fwd′ t fs e sat with L.first (subFactor t) (subFactor? t) fs
    elim-fwd′ t fs e sat | inj₁ (f , fsub , loc) = sat-++ e
      (ineqs (getSub t f fsub))
      (Data.List.map (replace-factor-sub t (getSub t f fsub)) fs)
      (ineqs-sub t f fsub e (∈-sat f fs loc e sat))
      (subst T (sym (replace-prod-sub-equiv t (getSub t f fsub) fs e (subst T (sym (getSub-works t f fsub e)) (∈-sat f fs loc e sat)))) sat)
    elim-fwd′ t fs e sat | inj₂ nonesub = nosub-fwd t fs nonesub e sat



    a+b-a=b : {a b : ℕ} → a ≤ b → a ℕ+ (b ∸ a) ≡ b
    a+b-a=b {zero} _ = refl
    a+b-a=b {suc a} {zero} ()
    a+b-a=b {suc a} {suc b} (s≤s a≤b) = cong suc (a+b-a=b a≤b)

    foo : (t : X) (k : ℕ) (term : Term) → ¬ t T.∈ term → (e : Env) → k ≤ (evalTerm (lookup e) term) → ((t , (evalTerm (lookup e) term ∸ k)) ∷ e) satisfies (F.i (+F (S k (var t) == term)))
    foo t k term t∉term e k≤term with evalTerm (lookup e) term | evalTerm (lookup ((t , (evalTerm (lookup e) term ∸ k)) ∷ e)) term | T.∉-eval t term (evalTerm (lookup e) term ∸ k) e t∉term | t X≟ t
    foo t k term t∉term e k≤term | eterm | .eterm | refl | yes _ = ≡T (a+b-a=b k≤term)
    foo t k term t∉term e k≤term | _ | _ | _ | no t≠t = contradiction refl t≠t

    bar : (a b c : ℕ) → b ℕ+ a ≡ c → a ≡ c ∸ b
    bar a zero c eq = eq
    bar a (suc b) zero ()
    bar a (suc b) (suc c) eq = bar a b c (cong pred eq)

    forbidden : (t : X) (f : Factor) (e : Env) → List ℕ
    forbidden t (+F _) e = []
    forbidden t (-F (L == R)) e with t T.∈? L | t T.∈? R
    forbidden t (-F (_ == _)) e | yes _ | yes _ = []
    forbidden t (-F (S k (var .t) == term)) e | yes refl | no _ = (evalTerm (lookup e) term ∸ k) ∷ []
    forbidden t (-F (S _ ∅ == _)) e | yes () | no _
    forbidden t (-F (term == S k (var .t))) e | no _ | yes refl = (evalTerm (lookup e) term ∸ k) ∷ []
    forbidden t (-F (_ == S _ ∅)) e | no _ | yes ()
    forbidden t (-F (_ == _)) e | no _ | no _ = []

    ¬forbidden-sat : (t : X) (f : Factor) (a : ℕ) (e : Env) (ns : ¬ subFactor t f) → ¬ a L.∈ (forbidden t f e)
      → e satisfies (F.i (replace-factor-nosub t f ns))
      → ((t , a) ∷ e) satisfies (F.i f)
    ¬forbidden-sat t (+F (L == R)) a e ns nf sat with t T.∈? L | t T.∈? R
    ¬forbidden-sat t (+F (S _ ∅ == _)) _ _ _ _ _ | yes () | _
    ¬forbidden-sat t (+F (_ == S _ ∅)) _ _ _ _ _ | _ | yes ()
    ¬forbidden-sat t (+F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl with t X≟ t
    ¬forbidden-sat t (+F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl | no t≠t = contradiction refl t≠t
    ¬forbidden-sat t (+F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl | yes _ =
      ≡T (cong (λ z → z ℕ+ a) (T≡ sat))
    ¬forbidden-sat t (+F (S k (var .t) == term)) a e ns nf sat | yes refl | no t∉term = contradiction (subL k term t∉term) ns
    ¬forbidden-sat t (+F (term == S k (var .t))) a e ns nf sat | no t∉term | yes refl = contradiction (subR k term t∉term) ns
    ¬forbidden-sat t (+F (L == R)) a e ns nf sat | no t∉L | no t∉R = subst T (sym (A.∉-eval t (L == R) a e [ t∉L , t∉R ]′)) sat
    ¬forbidden-sat t (-F (L == R)) a e ns nf sat with t T.∈? L | t T.∈? R
    ¬forbidden-sat t (-F (S _ ∅ == _)) _ _ _ _ _ | yes () | _
    ¬forbidden-sat t (-F (_ == S _ ∅)) _ _ _ _ _ | _ | yes ()
    ¬forbidden-sat t (-F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl with t X≟ t
    ¬forbidden-sat t (-F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl | yes _ =
      ≢F ((F≢ sat) ∘ (pred*′ {x} {y} a))
    ¬forbidden-sat t (-F (S x (var .t) == S y (var .t))) a e ns nf sat | yes refl | yes refl | no t≠t = contradiction refl t≠t
    ¬forbidden-sat t (-F (S k (var .t) == term)) a e ns nf sat | yes refl | no t∉term with t X≟ t
    ¬forbidden-sat t (-F (S k (var .t) == term)) a e ns nf sat | yes refl | no t∉term | yes _ with evalTerm (lookup e) term | evalTerm (lookup ((t , a) ∷ e)) term | T.∉-eval t term a e t∉term
    ¬forbidden-sat t (-F (S k (var .t) == term)) a e ns nf sat | yes refl | no t∉term | yes _ | eterm | .eterm | refl =
      ≢F (λ k+a=term → nf (subst (λ z → a L.∈ (z ∷ [])) (bar a k eterm k+a=term) (here a [])))
    ¬forbidden-sat t (-F (S k (var .t) == term)) a e ns nf sat | yes refl | no t∉term | no t≠t = contradiction refl t≠t
    ¬forbidden-sat t (-F (term == S k (var .t))) a e ns nf sat | no t∉term | yes refl with t X≟ t
    ¬forbidden-sat t (-F (term == S k (var .t))) a e ns nf sat | no t∉term | yes refl | yes _ with evalTerm (lookup e) term | evalTerm (lookup ((t , a) ∷ e)) term | T.∉-eval t term a e t∉term
    ¬forbidden-sat t (-F (term == S k (var .t))) a e ns nf sat | no t∉term | yes refl | yes _  | eterm | .eterm | refl =
      ≢F ((λ k+a=term → nf (subst (λ z → a L.∈ (z ∷ [])) (bar a k eterm k+a=term) (here a []))) ∘ sym)
    ¬forbidden-sat t (-F (term == S k (var .t))) a e ns nf sat | no t∉term | yes refl | no t≠t = contradiction refl t≠t
    ¬forbidden-sat t (-F (L == R)) a e ns nf sat | no t∉L | no t∉R = subst T (cong not (sym (A.∉-eval t (L == R) a e [ t∉L , t∉R ]′))) sat
    
    forbiddens : (t : X) (fs : List Factor) (e : Env) → List ℕ
    forbiddens _ [] _ = []
    forbiddens t (f ∷ fs) e = (forbidden t f e) ++ (forbiddens t fs e)

    ¬forbiddens-sat : (t : X) (fs : List Factor) (a : ℕ) (e : Env) (ns : allP (¬_ ∘ subFactor t) fs) → ¬ a L.∈ (forbiddens t fs e)
      → e satisfies (P.i (L.mapAllP (replace-factor-nosub t) fs ns))
      → ((t , a) ∷ e) satisfies (P.i fs)
    ¬forbiddens-sat t [] a e _ _ _ = tt
    ¬forbiddens-sat t (f ∷ fs) a e (fns , fsns) nf sat = sat-∷ ((t , a) ∷ e) f fs
      (¬forbidden-sat t f a e fns (nf ∘ (L.∈-++₁ a (forbidden t f e) (forbiddens t fs e))) (sat-head e (replace-factor-nosub t f fns) (L.mapAllP (replace-factor-nosub t) fs fsns) sat))
      (¬forbiddens-sat t fs a e fsns (nf ∘ (L.∈-++₂ a (forbidden t f e) (forbiddens t fs e))) (sat-tail e (replace-factor-nosub t f fns) (L.mapAllP (replace-factor-nosub t) fs fsns) sat))

    fresh : List ℕ → ℕ
    fresh [] = zero
    fresh (x ∷ xs) = (fresh xs) ℕ+ (suc x)

    fresh-≤ : (xs : List ℕ) (y : ℕ) → fresh xs ≤ y → ¬ y L.∈ xs
    fresh-≤ [] _ _ ()
    fresh-≤ (.y ∷ xs) y f≤y (here .y .xs) = suc-≰ y (+≤₂ (fresh xs) (suc y) y f≤y)
    fresh-≤ (x ∷ xs) y f≤y (there .x y∈xs) = fresh-≤ xs y (+≤₁ (fresh xs) (suc x) y f≤y) y∈xs

    fresh-∉ : (xs : List ℕ) → ¬ (fresh xs) L.∈ xs
    fresh-∉ xs = fresh-≤ xs (fresh xs) (≡-≤ refl)


    -----------------
    -- And finally --
    -----------------

    elim-fwd : (t : X) (fs : List Factor) (a : ℕ) (e : Env)
      → ((t , a) ∷ e) satisfies (P.i fs)
      → e satisfies (P.i (elim-prod t fs))
    -------------------------------------------------------
    elim-fwd t fs a e = ∉-sat t (elim-prod t fs) a e (elim-prod-∉ t fs) ∘ elim-fwd′ t fs ((t , a) ∷ e)


    elim-bwd : (t : X) (fs : List Factor) (e : Env)
      → e satisfies (P.i (elim-prod t fs))
      → Σ ℕ (λ a → ((t , a) ∷ e) satisfies (P.i fs))
    ------------------------------------------------
    elim-bwd t fs e sat with L.first (subFactor t) (subFactor? t) fs
    elim-bwd t fs e sat | inj₁ ((+F (S .k (var .t) == .term)) , subL k term t∉term , loc) =
      ((evalTerm (lookup e) term) ∸ k ,
        subst T (replace-prod-sub-equiv t (substitution k term) fs ((t , (evalTerm (lookup e) term ∸ k)) ∷ e)
                  (foo t k term t∉term e (ineqs′-≤ k term e
                    ((sat-++₁ e (ineqs′ k term) (Data.List.map (replace-factor-sub t (substitution k term)) fs) sat)))))
                (∉-sat′ t (Data.List.map (replace-factor-sub t (substitution k term)) fs) (evalTerm (lookup e) term ∸ k) e
                  (t∉term  ∘ replace-prod-sub-∈ t (substitution k term) fs)
                  (sat-++₂ e (ineqs′ k term) (Data.List.map (replace-factor-sub t (substitution k term)) fs) sat)))
    elim-bwd t fs e sat | inj₁ ((+F (.term == S .k (var .t))) , subR k term t∉term , loc) =
      ((evalTerm (lookup e) term) ∸ k ,
        subst T (replace-prod-sub-equiv t (substitution k term) fs ((t , (evalTerm (lookup e) term ∸ k)) ∷ e)
                  (foo t k term t∉term e (ineqs′-≤ k term e
                    ((sat-++₁ e (ineqs′ k term) (Data.List.map (replace-factor-sub t (substitution k term)) fs) sat)))))
                (∉-sat′ t (Data.List.map (replace-factor-sub t (substitution k term)) fs) (evalTerm (lookup e) term ∸ k) e
                  (t∉term  ∘ replace-prod-sub-∈ t (substitution k term) fs)
                  (sat-++₂ e (ineqs′ k term) (Data.List.map (replace-factor-sub t (substitution k term)) fs) sat)))
    elim-bwd t fs e sat | inj₂ nonesub =
      (fresh (forbiddens t fs e) ,
      ¬forbiddens-sat t fs (fresh (forbiddens t fs e)) e nonesub (fresh-∉ (forbiddens t fs e)) sat)

