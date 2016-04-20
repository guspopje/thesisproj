module SecondKind where

  open import Common
  open import FirstKind renaming (_⊃_ to _⊃₁_; _&_ to _&₁_)

  open import Agda.Primitive
  open import Function
  open import Function.Injection using (_↣_; Injection)
  open import Function.Equality using (_⟨$⟩_)
  open import Data.Bool
  open import Data.Empty
  open import Data.Unit
  open import Data.Nat hiding (_⊔_)
  open import Data.Sum
  open import Data.Vec hiding (_∈_)
  open import Data.Product
  open import Relation.Binary
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Sum
  open import Relation.Nullary.Negation
  open import Relation.Binary.PropositionalEquality

  import Data.List
  
  module SK {α₁ α α' β : Level} (DSA : DecSetoid α α') (B : ℕ → Set β) where
  
    open DecSetoid hiding (trans; refl)

    A : Set _
    A = Carrier DSA

    --B : ℕ → Set _
    --B n = Carrier (DSB n)

    _≟A_ : Decidable (_≈_ DSA)
    _≟A_ = DecSetoid._≟_ DSA

    _==A_ : A → A → Bool
    x ==A y = ⌊ x ≟A y ⌋

    _≈A_ : (Rel A _)
    _≈A_ = DecSetoid._≈_ DSA

    module DV = DecVec {α} {α'} {DSA}


    -----------------------
    -- "The Second Kind"
    -----------------------

    infixr 4 _&_
    infixr 4 _∪_
    infixr 5 _⊃_

    -- An application of an atomic propositional function.
    fnApp : Set (α ⊔ β)
    fnApp = Σ ℕ (λ n → (B n × Vec A n))

    -- A proposition of the second kind.
    data SK : Set (α ⊔ β) where
      apply : fnApp → SK
      ~ : SK → SK
      _∪_ : SK → SK → SK
      [+_]_ : A → SK → SK
      [-_]_ : A → SK → SK

    -- Implication
    _⊃_ : SK → SK → SK
    p ⊃ q = (~ p) ∪ q

    -- Conjunction
    _&_ : SK → SK → SK
    p & q = ~ (~ p ∪ ~ q)
    

    -- An elementary (quantifier-free) proposition
    data Elementary : SK → Set (α ⊔ β) where
      eapply : (ap : fnApp) → Elementary (apply ap)
      enot : {x : SK} → Elementary x → Elementary (~ x)
      eor : {x y : SK} → Elementary x → Elementary y → Elementary (x ∪ y)
      
    -- Map an *elementary* proposition of the second kind to a proposition of the first kind
    mapSF : {C : Set α₁} → (fnApp → C) → (p : SK) → Elementary p → FK C
    mapSF f (apply ap) _ = atom (f ap)
    mapSF f (~ p) (enot e) = ~ (mapSF f p e)
    mapSF f (p ∪ q) (eor ep eq) = (mapSF f p ep) ∪ (mapSF f q eq)
    mapSF f ([+ _ ] _) ()
    mapSF f ([- _ ] _) ()

    -- Map a prop of the first kind to one of the second kind
    mapFS : {C : Set α₁} → (C → fnApp) → FK C → SK
    mapFS f (atom a) = apply (f a)
    mapFS f (~ p) = ~ (mapFS f p)
    mapFS f (p ∪ q) = (mapFS f p) ∪ (mapFS f q)

    -- Lemma: mapFS only produces elementary propositions.
    mapFS-elem : {C : Set α₁} → (f : C → fnApp) → (p : FK C) → Elementary (mapFS f p)
    mapFS-elem f (atom a) = eapply (f a)
    mapFS-elem f (~ p) = enot (mapFS-elem f p)
    mapFS-elem f (p ∪ q) = eor (mapFS-elem f p) (mapFS-elem f q)

    -- A context for identifying a location ("hole") in an SK, à la zipper.
    -- The first argument to each constructor is the parent context.
    data ContextSK : Set (α ⊔ β) where
      ∙ : ContextSK
      _~∙ : ContextSK → ContextSK
      _⟨∙∪_⟩ : ContextSK → SK → ContextSK
      _⟨_∪∙⟩ : ContextSK → SK → ContextSK
      _[+_]∙ : ContextSK → A → ContextSK
      _[-_]∙ : ContextSK → A → ContextSK

    -- Insert an SK into a context.
    _◂_ : ContextSK → SK → SK
    ∙ ◂ p = p
    (c ~∙) ◂ p = c ◂ (~ p)
    (c ⟨∙∪ q ⟩) ◂ p = c ◂ (p ∪ q)
    (c ⟨ p ∪∙⟩) ◂ q = c ◂ (p ∪ q)
    (c [+ t ]∙) ◂ p = c ◂ ([+ t ] p)
    (c [- t ]∙) ◂ p = c ◂ ([- t ] p)

{-
    hasParent : ContextSK → Set
    hasParent ∙ = ⊥
    hasParent _ = ⊤

    hasParent? : (c : ContextSK) → Dec (hasParent c)
    hasParent? ∙ = no (λ ())
    hasParent? (_ ~∙) = yes tt
    hasParent? (_ ⟨∙∪ _ ⟩) = yes tt
    hasParent? (_ ⟨ _ ∪∙⟩) = yes tt
    hasParent? (_ [+ _ ]∙) = yes tt
    hasParent? (_ [- _ ]∙) = yes tt

    parent : (c : ContextSK) → (hasParent c) → ContextSK
    parent ∙ ()
    parent (par ~∙) _ = par
    parent (par ⟨∙∪ _ ⟩) _ = par
    parent (par ⟨ _ ∪∙⟩) _ = par
    parent (par [+ _ ]∙) _ = par
    parent (par [- _ ]∙) _ = par


    data Free (x : A) : ContextSK → Set (α ⊔ β ⊔ α') where
      ∙-free : Free x ∙
      ~∙-free : {ct : ContextSK} → Free x ct → Free x (ct ~∙)
      ∙∪-free : {ct : ContextSK} → Free x ct → (q : SK) → Free x (ct ⟨∙∪ q ⟩)
      ∪∙-free : {ct : ContextSK} → Free x ct → (q : SK) → Free x (ct ⟨ q ∪∙⟩)
      [+]∙-free : {ct : ContextSK} {t : A} → Free x ct → ¬ (t ≈A x) → Free x (ct [+ t ]∙)
      [-]∙-free : {ct : ContextSK} {t : A} → Free x ct → ¬ (t ≈A x) → Free x (ct [- t ]∙)

    free-parent : {x : A} {c : ContextSK} → Free x c → (p : hasParent c) → Free x (parent c p)
    free-parent {c = ∙} f () 
    free-parent {c = ct ~∙} (~∙-free f) p = f
    free-parent {c = ct ⟨∙∪ .x₁ ⟩} (∙∪-free f x₁) hp = f
    free-parent {c = ct ⟨ .x₁ ∪∙⟩} (∪∙-free f x₁) hp = f
    free-parent {c = ct [+ t ]∙} ([+]∙-free f x₁) hp = f
    free-parent {c = ct [- t ]∙} ([-]∙-free f x₁) hp = f

    [+]∙-free-neq : {x t : A} {c : ContextSK} → Free x (c [+ t ]∙) → ¬ (t ≈A x)
    [+]∙-free-neq ([+]∙-free _ neq) = neq

    [-]∙-free-neq : {x t : A} {c : ContextSK} → Free x (c [- t ]∙) → ¬ (t ≈A x)
    [-]∙-free-neq ([-]∙-free _ neq) = neq

    free? : (x : A) → (c : ContextSK) → Dec (Free x c)
    free? x ∙ = yes ∙-free
    free? x (c ~∙) with free? x c
    ... | yes parFree = yes (~∙-free parFree)
    ... | no ¬parFree = no (λ free → ¬parFree (free-parent free tt))
    free? x (c ⟨∙∪ q ⟩) with free? x c
    ... | yes parFree = yes (∙∪-free parFree q)
    ... | no ¬parFree = no (λ free → ¬parFree (free-parent free tt))
    free? x (c ⟨ q ∪∙⟩) with free? x c
    ... | yes parFree = yes (∪∙-free parFree q)
    ... | no ¬parFree = no (λ free → ¬parFree (free-parent free tt))
    free? x (c [+ t ]∙) with free? x c | t ≟A x
    ... | yes parFree | yes eq = no (λ free → [+]∙-free-neq free eq) 
    ... | yes parFree | no neq = yes ([+]∙-free parFree neq)
    ... | no ¬parFree | _ = no (λ free → ¬parFree (free-parent free tt))
    free? x (c [- t ]∙) with free? x c | t ≟A x
    ... | yes parFree | yes eq = no (λ free → [-]∙-free-neq free eq) 
    ... | yes parFree | no neq = yes ([-]∙-free parFree neq)
    ... | no ¬parFree | _ = no (λ free → ¬parFree (free-parent free tt))
-}

    _∈_ : A → SK → Set
    x ∈ apply (_ , _ , v) = DV._∈_ x v
    x ∈ ~ p = x ∈ p
    x ∈ (p ∪ q) = (x ∈ p) ⊎ (x ∈ q)
    x ∈ ([+ t ] p) with t ≟A x
    ... | yes _ = ⊤
    ... | no _ = x ∈ p
    x ∈ ([- t ] p) with t ≟A x
    ... | yes _ = ⊤
    ... | no _ = x ∈ p

    _∈?_ : (x : A) → (p : SK) → Dec (x ∈ p)
    x ∈? (apply (_ , _ , v)) = DV._∈?_ x v
    x ∈? (~ p) = x ∈? p
    x ∈? (p ∪ q) = (x ∈? p) ⊎-dec (x ∈? q)
    x ∈? ([+ t ] p) with t ≟A x | x ∈? p
    ... | yes proof | _ = yes tt
    ... | no _ | d = d
    x ∈? ([- t ] p) with t ≟A x | x ∈? p
    ... | yes _ | _ = yes tt
    ... | no _ | d = d
    
    _∉_ : A → SK → Set
    x ∉ p = ¬ (x ∈ p)

    _∉?_ : (x : A) → (p : SK) → Dec (x ∉ p)
    x ∉? p = ¬? (x ∈? p)

    -- Variable substitution. Only substitutes free occurences (i.e. "real variables").
    _[_/_] : SK → A → A → SK
    (apply (n , f , v)) [ y / x ] = (apply (n , f , DV._[_/_] v y x))
    (~ p) [ y / x ] = ~ (p [ y / x ])
    (p ∪ q) [ y / x ] = (p [ y  / x ]) ∪ (q [ y  / x ])
    ([+ t ] p) [ y / x ] = [+ t ] (if ⌊ t ≟A x ⌋ then p else p [ y / x ])
    ([- t ] p) [ y / x ] = [- t ] (if ⌊ t ≟A x ⌋ then p else p [ y / x ])

    
    -- Proofs on propositions of the second kind. "Rules of passage", "rules of generalization", "rule of simplification", "rule of implication" (modus ponens).
    -- From page 74, supplemental rules of passage on page 225.
    data ProofSK : SK → Set (α ⊔ β ⊔ lsuc α₁) where
      --fromFK : {C : Set α₁} → (p' : FK C) → (p : SK) → (e : Elementary p) → (f : fnApp ↣ C) → p' ≡ mapSF (_⟨$⟩_ (Injection.to f)) p e → ProofFK p' → ProofSK p
      fromFK : {C : Set α₁} → (p : SK) → (e : Elementary p) → (f : fnApp ↣ C) → ProofFK (mapSF (_⟨$⟩_ (Injection.to f)) p e) → ProofSK p
      pas1  : {t : A} {Φ : SK} → (c : ContextSK) → ProofSK (c ◂ (~ ([+ t ] Φ))) → ProofSK (c ◂ ([- t ] ~ Φ))
      pas1' : {t : A} {Φ : SK} → (c : ContextSK) → ProofSK (c ◂ ([- t ] ~ Φ)) → ProofSK (c ◂ (~ ([+ t ] Φ)))
      pas2  : {t : A} {Φ : SK} → (c : ContextSK) → ProofSK (c ◂ (~ ([- t ] Φ))) → ProofSK (c ◂ ([+ t ] ~ Φ))
      pas2' : {t : A} {Φ : SK} → (c : ContextSK) → ProofSK (c ◂ ([+ t ] ~ Φ)) → ProofSK (c ◂ (~ ([- t ] Φ)))
      pas3  : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ (([+ t ] Φ) ∪ p)) → ProofSK (c ◂ ([+ t ] (Φ ∪ p)))
      pas3' : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ ([+ t ] (Φ ∪ p))) → ProofSK (c ◂ (([+ t ] Φ) ∪ p))
      pas4  : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ (p ∪ ([+ t ] Φ))) → ProofSK (c ◂ ([+ t ] (p ∪ Φ)))
      pas4' : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ ([+ t ] (p ∪ Φ))) → ProofSK (c ◂ (p ∪ ([+ t ] Φ)))
      pas5  : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ (([- t ] Φ) ∪ p)) → ProofSK (c ◂ ([- t ] (Φ ∪ p)))
      pas5' : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ ([- t ] (Φ ∪ p))) → ProofSK (c ◂ (([- t ] Φ) ∪ p))
      pas6  : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ (p ∪ ([- t ] Φ))) → ProofSK (c ◂ ([- t ] (p ∪ Φ)))
      pas6' : {t : A} {Φ : SK} {p : SK} → (t ∉ p) → (c : ContextSK) → ProofSK (c ◂ ([- t ] (p ∪ Φ))) → ProofSK (c ◂ (p ∪ ([- t ] Φ)))
      
      gen1 : {Φ : SK} → (x : A) → ProofSK Φ → ProofSK ([+ x ] Φ)
      gen2 : {Φ : SK} → {x y : A} → ProofSK (Φ [ x / y ]) → ProofSK ([- y ] Φ)
      simp : {P : SK} → ProofSK (P ∪ P) → ProofSK P
      mp : {P Q : SK} → ProofSK (P ⊃ Q) → ProofSK P → ProofSK Q

    
    sub-∉ : (p : SK) (x y : A) → x ∉ p → p [ y / x ] ≡ p
    sub-∉ (apply ap) x y proof = {!!}
    sub-∉ (~ p) x y proof = cong ~ (sub-∉ p x y proof)
    sub-∉ (p ∪ q) x y proof = cong₂ _∪_ (sub-∉ p x y (proof ∘ inj₁)) ((sub-∉ q x y (proof ∘ inj₂)))
    sub-∉ ([+ t ] p) x y proof with t ≟A x
    ... | yes eq = ⊥-elim (proof tt)
    ... | no _ = cong (λ q → [+ t ] q) (sub-∉ p x y proof)
    sub-∉ ([- t ] p) x y proof with t ≟A x
    ... | yes eq = ⊥-elim (proof tt)
    ... | no _ = cong (λ q → [- t ] q) (sub-∉ p x y proof)
    
    gen3 : {x y z : A} {Φ : SK} → ProofSK (Φ [ y / x ] ∪ Φ [ z / x ]) → ProofSK ([- x ] Φ)
    gen3 = {!!}
