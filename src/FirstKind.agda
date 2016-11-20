
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

  data FK (A : Set) : Set where
    atom : A → FK A
    ~_ : FK A → FK A
    _∪_ : FK A → FK A → FK A

  _⊃_ : {A : Set} → FK A → FK A → FK A
  p ⊃ q = (~ p) ∪ q

  _&_ : {A : Set} → FK A → FK A → FK A
  p & q = ~ (~ p ∪ ~ q)

  _≣_ : {A : Set} → FK A → FK A → FK A
  p ≣ q = (p ⊃ q) & (q ⊃ p)

  module Proofs {A : Set} (Axioms : FK A → Set) where

    data ProofFK : FK A → Set where
      ptaut : (p : FK A) → ProofFK (p ∪ p ⊃ p)
      padd : (p q : FK A) → ProofFK (q ⊃ p ∪ q)
      pperm : (p q : FK A) → ProofFK (p ∪ q ⊃ q ∪ p)
      passoc : (p q r : FK A) → ProofFK (p ∪ (q ∪ r) ⊃ q ∪ (p ∪ r))
      psum : (p q r : FK A) → ProofFK ((q ⊃ r) ⊃ (p ∪ q ⊃ p ∪ r))
      impl : {p q : FK A} → ProofFK (p ⊃ q) → ProofFK p → ProofFK q
      axiom : {p : FK A} → Axioms p → ProofFK p

    infixr 2 ⊢_
    ⊢_ : FK A → Set
    ⊢_ = ProofFK

    infixr 4 _≣!_
    _≣!_ : FK A → FK A → Set
    p ≣! q = ProofFK (p ≣ q)



    
    {-
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
    fkSubThm f (impl pq p) = impl (fkSubThm f pq) (fkSubThm f p)


    -- Replace atoms with other atoms.
    fkMap : {A B : Set} → (A → B) → FK A → FK B
    fkMap f = fkSub (atom ∘ f)

    -- fkMap preserves truth.
    fkMapThm : {A B : Set} → {p : FK A} → (f : A → B) → ProofFK p → ProofFK (fkMap f p)
    fkMapThm f = fkSubThm (atom ∘ f)
    -}
    
    -- Assign a "logical value" (Bool) to a proposition, given assignments for the atoms.
    eval : (A → Bool) → FK A → Bool
    eval iatom (atom x) = iatom x
    eval iatom (p ∪ q) = eval iatom p ∨ eval iatom q
    eval iatom (~ p) = not (eval iatom p)

    -- If a proposition is provable, its interpretation is 'true' (regardless of interpretations of atoms).
    provableTrue : {p : FK A} (iatom : A → Bool) (happyAxioms : ({q : FK A} → Axioms q → T (eval iatom q))) (proof : ProofFK p) → T (eval iatom p)
    provableTrue iatom _ (ptaut p) with eval iatom p
    ... | true = tt
    ... | false = tt
    provableTrue iatom _ (padd p q) with eval iatom p | eval iatom q
    ... | true | true = tt
    ... | true | false = tt
    ... | false | true = tt
    ... | false | false = tt
    provableTrue iatom _ (pperm p q) with eval iatom p | eval iatom q
    ... | true | true = tt
    ... | true | false = tt
    ... | false | true = tt
    ... | false | false = tt
    provableTrue iatom _ (passoc p q r) with eval iatom p | eval iatom q | eval iatom r
    ... | true | true | true = tt
    ... | true | true | false = tt
    ... | true | false | true = tt
    ... | true | false | false = tt
    ... | false | true | true = tt
    ... | false | true | false = tt
    ... | false | false | true = tt
    ... | false | false | false = tt
    provableTrue iatom _ (psum p q r) with eval iatom p | eval iatom q | eval iatom r
    ... | true | true | true = tt
    ... | true | true | false = tt
    ... | true | false | true = tt
    ... | true | false | false = tt
    ... | false | true | true = tt
    ... | false | true | false = tt
    ... | false | false | true = tt
    ... | false | false | false = tt
    provableTrue iatom ha (impl {p} {q} p⊃q-proof p-proof) with eval iatom p | provableTrue iatom ha p-proof | provableTrue iatom ha p⊃q-proof
    ... | false | () | _
    ... | true | _ | true-p⊃q = true-p⊃q
    provableTrue iatom ha (axiom ax) = ha ax

    {-
    consistent : {p : FK A} → ProofFK p → ProofFK (~ p) → ⊥
    consistent {p = p} p-proof ~p-proof with eval (const false) p | provableTrue (const false) p-proof | provableTrue (const false) ~p-proof
    ... | true | _ | ()
    ... | false | () | _
    -}


    -- ⊃ is reflexive and transitive.
    ⊃-refl : (p : FK A) → ProofFK (p ⊃ p)
    ⊃-refl p = (impl (impl (psum (~ p) (p ∪ p) p) (ptaut p)) (padd p p))

    ⊃-trans : (p q r : FK A) → ProofFK ((p ⊃ q) ⊃ ((q ⊃ r) ⊃ (p ⊃ r)))
    ⊃-trans p q r = impl (passoc (~ (q ⊃ r)) (~ (p ⊃ q)) (p ⊃ r)) (psum (~ p) q r)

    -- Compose two implications; a convenient weakening of ⊃-trans.
    _⊃⊃_ : {p q r : FK A} → ProofFK (p ⊃ q) → ProofFK (q ⊃ r) → ProofFK (p ⊃ r)
    _⊃⊃_ {p = p} {q = q} {r = r} pq qr = impl (impl (⊃-trans p q r) pq) qr

    -- The law of excluded middle, in two flavors for convenience.
    lem₁ : (p : FK A) → ProofFK (~ p ∪ p)
    lem₁ = ⊃-refl
  
    lem₂ : (p : FK A) → ProofFK (p ∪ ~ p)
    lem₂ p = impl (pperm (~ p) p) (lem₁ p)

    -- Double negation introduction and elimination.
    ~~-intro : (p : FK A) → ProofFK (p ⊃ ~ ~ p)
    ~~-intro p = lem₂ (~ p)

    ~~-elim : (p : FK A) → ProofFK ((~ ~ p) ⊃ p)
    ~~-elim p = impl
      (pperm p (~ ~ ~ p))
      (impl
        (impl
          (psum p (~ p) (~ ~ ~ p))
          (~~-intro (~ p)))
        (lem₂ p))

    -- Contraposition, and a convenient weakened helper.
    contra : (p q : FK A) → ProofFK ((p ⊃ q) ⊃ (~ q ⊃ ~ p))
    contra p q = (impl (psum (~ p) q (~ ~ q)) (~~-intro q)) ⊃⊃ (pperm (~ p) (~ ~ q))

    contra' : {p q : FK A} → ProofFK (p ⊃ q) → ProofFK (~ q ⊃ ~ p)
    contra' {p = p} {q = q} = impl (contra p q)

    -- A flipped version of padd, for convenience.
    padd' : (p q : FK A) → ProofFK (p ⊃ p ∪ q)
    padd' p q = (padd q p) ⊃⊃ (pperm q p)

    -- A flipped version of psum, for convenience
    --psum' : (p q r : FK A) → ProofFK ((q ⊃ r) ⊃ ((q ∪ p) ⊃ (r ∪ p)))
    --psum' p q r = {!!}

    -- Some properties of &.
    &-refl : (p : FK A) → ProofFK (p ⊃ p & p)
    &-refl p = impl
      (impl
        (psum (~ p) (~ ~ p) (p & p))
        (impl
          (contra (~ p ∪ ~ p) (~ p))
          (ptaut (~ p))))
      (lem₂ (~ p))

    &-sym : (p q : FK A) → ProofFK (p & q ⊃ q & p)
    &-sym p q = impl
      (pperm (q & p) (~ (p & q)))
      ((pperm (~ q) (~ p)) ⊃⊃ (~~-intro (~ p ∪ ~ q)))

    &-elim₂ : (p q : FK A) → ProofFK (p & q ⊃ q)
    &-elim₂ p q = impl
      (pperm q (~ (p & q)))
      (impl
        (impl
          (psum q (~ q) (~ (p & q)))
          ((padd (~ p) (~ q)) ⊃⊃ (~~-intro (~ p ∪ ~ q))))
        (lem₂ q))

    &-elim₁ : (p q : FK A) → ProofFK (p & q ⊃ p)
    &-elim₁ p q = (&-sym p q) ⊃⊃ (&-elim₂ q p)

    &-intro : (p q : FK A) → ProofFK (p ⊃ (q ⊃ (p & q)))
    &-intro p q = impl
      (impl
        (psum (~ p) (p & q ∪ ~ q) (~ q ∪ p & q))
        (pperm (p & q) (~ q)))
      (impl
        (passoc (p & q) (~ p) (~ q))
        (lem₁ (~ p ∪ ~ q)))

    -- Conveniences
    &-elim₁' : {p q : FK A} → ProofFK (p & q) → ProofFK p
    &-elim₁' {p = p} {q = q} = impl (&-elim₁ p q)
    
    &-elim₂' : {p q : FK A} → ProofFK (p & q) → ProofFK q
    &-elim₂' {p = p} {q = q} = impl (&-elim₂ p q)

    _&!_ : {p q : FK A} → ProofFK p → ProofFK q → ProofFK (p & q)
    _&!_ {p = p} {q = q} p! q! = impl (impl (&-intro p q) p!) q!    

    


    -- Properties of equivalence
    ≣-refl : (p : FK A) → ProofFK (p ≣ p)
    ≣-refl p = (⊃-refl p) &! (⊃-refl p)

    ≣-sym : (p q : FK A) → ProofFK (p ≣ q ⊃ q ≣ p)
    ≣-sym p q = &-sym (p ⊃ q) (q ⊃ p)

    ≣-sym' : {p q : FK A} → ⊢ p ≣ q → ⊢ q ≣ p
    ≣-sym' {p} {q} eq = impl (≣-sym p q) eq

    --≣-trans : (p q r : FK A) → ProofFK (p ≣ q ⊃ (q ≣ r ⊃ p ≣ r))
    --≣-trans p q r = {!!}

    ≣-trans' : {p q r : FK A} → ⊢ p ≣ q → ⊢ q ≣ r → ⊢ p ≣ r
    ≣-trans' pq qr = (&-elim₁' pq ⊃⊃ &-elim₁' qr) &! (&-elim₂' qr ⊃⊃ &-elim₂' pq)

    ≣-supersym : (p q : FK A) → ProofFK ((p ≣ q) ≣ (q ≣ p))
    ≣-supersym p q = (≣-sym p q) &! (≣-sym q p)

    -- Probably not.
    --hmm : (p q : FK A) → (ProofFK p → ProofFK q) → ProofFK (p ⊃ q)
    --hmm p q f = {!!}

{-
  ~p₁ ≣ ~p₂
= ~p₁ ⊃ ~p₂ & ~p₂ ⊃ ~p₁
= ~~p₁ ∨ ~p₂ & ~~p₂ ∨ ~p₁
-}

-- ~p ∨ q₁   ~p ∨ q₂
-- &-intro q₁ q₂ :      ⊢ q₁ ⊃ (q₂ ⊃ (q₁ & q₂))
--
{-
    ⊃-&' : (p q₁ q₂ : FK A) → ⊢ p ⊃ q₁ → ⊢ p ⊃ q₂ → ⊢ p ⊃ (q₁ & q₂)
    ⊃-&' p q₁ q₂ p⊃q₁ p⊃q₂ = {!!} 

    
--    &-⊃ : (p₁ p₂ p₃ p₄ : FK A) → ⊢ (p₁ ⊃ p₃) ⊃ (p₂ ⊃ p₄) ⊃ (p₁ & p₂ ⊃ p₃ & p₄)
    &-⊃' : (p₁ p₂ p₃ p₄ : FK A) → ⊢ p₁ ⊃ p₃ → ⊢ p₂ ⊃ p₄ → ⊢ (p₁ & p₂ ⊃ p₃ & p₄)
    &-⊃' p₁ p₂ p₃ p₄ 1⊃3 2⊃4 = {!!}

    ≣-~ : (p₁ p₂ : FK A) → ⊢ (p₁ ≣ p₂) ⊃ (~ p₁ ≣ ~ p₂)
    ≣-~ p₁ p₂ = (≣-sym p₁ p₂) ⊃⊃ &-⊃' (p₂ ⊃ p₁) (p₁ ⊃ p₂) (~ p₁ ⊃ ~ p₂) (~ p₂ ⊃ ~ p₁) (contra p₂ p₁) (contra p₁ p₂)
-}

    -- Contexts and substitution
    data Context : Set where
      ∙ : Context
      _~∙ : Context → Context
      _⟨∙∪_⟩ : Context → FK A → Context
      _⟨_∪∙⟩ : Context → FK A → Context

    _◂_ : Context → FK A → FK A
    ∙ ◂ p = p
    (c ~∙) ◂ p = c ◂ (~ p)
    (c ⟨∙∪ q ⟩) ◂ p = c ◂ (p ∪ q)
    (c ⟨ q ∪∙⟩) ◂ p = c ◂ (q ∪ p)

{-
    ≣-sub : (p₁ p₂ : FK A) → (c : Context) → ⊢ p₁ ≣ p₂ ⊃ (c ◂ p₁) ≣ (c ◂ p₂)
    ≣-sub p₁ p₂ ∙ = ⊃-refl (p₁ ≣ p₂)
    ≣-sub p₁ p₂ (c ~∙) = (≣-~ p₁ p₂) ⊃⊃ (≣-sub (~ p₁) (~ p₂) c)
    ≣-sub p₁ p₂ (c ⟨∙∪ q ⟩) = {!!}
    ≣-sub p₁ p₂ (c ⟨ q ∪∙⟩) = {!!}
-}    
    {-

have: for all q₁, q₂, c : ⊢ (q₁ ⊃ q₂) & (q₂ ⊃ q₁) ⊃ (c ◂ q₁ ⊃ c ◂ q₂) & (c ◂ q₂ ⊃ c ◂ q₁)
want: ⊢ (p₁ ⊃ p₂) & (p₂ ⊃ p₁) ⊃ (c ◂ ~p₁ ⊃ c ◂ ~p₂) & (c ◂ ~p₂ ⊃ c ◂ ~p₁)

recursive call using ~p₁ and ~p₂ gives us:
⊢ (~p₁ ⊃ ~p₂) & (~p₂ ⊃ ~p₁) ⊃ (c ◂ ~p₁ ⊃ c ◂ ~p₂) & (c ◂ ~p₂ ⊃ c ◂ ~p₁)


    -}


    module NF where

      open import Data.List.NonEmpty

      data Literal : Set where
        +_ : A → Literal
        -_ : A → Literal

      L : Set → Set
      L = List⁺

      Conj : Set
      Conj = L Literal

      Disj : Set
      Disj = L Literal

      DNF : Set
      DNF = L Disj

      CNF : Set
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

{-
      conj-++ : (c₁ c₂ : Conj) → ⊢ conj-interpret (c₁ ⁺++⁺ c₂) ≣ (conj-interpret c₁) ∪ (conj-interpret c₂)
      conj-++ c₁ c₂ = {!!}
-}




      -- Mutually recursive
      dnf : (p : FK A) → DNF
      cnf : (p : FK A) → CNF

      dnf (atom a) = [ [ + a ] ]
      dnf (~ p) = dual (cnf p)
      dnf (p₁ ∪ p₂) = (dnf p₁) ⁺++⁺ (dnf p₂)

      cnf (atom a) = [ [ + a ] ]
      cnf (~ p) = dual (dnf p)
      cnf (p₁ ∪ p₂) = dual (mix (dual (cnf p₁)) (dual (cnf p₂)))

{-
      dnf-works : (p : FK A) → ⊢ dnf-interpret (dnf p) ≣ p
      cnf-works : (p : FK A) → ⊢ cnf-interpret (cnf p) ≣ p

      dnf-works (atom a) = ≣-refl (atom a)
      dnf-works (~ p) = {!!}
      dnf-works (p₁ ∪ p₂) = {!!}

      cnf-works (atom a) = ≣-refl (atom a)
      cnf-works (~ p) = {!!}
      cnf-works (p₁ ∪ p₂) = {!!}
-}
  --open OneKind public
