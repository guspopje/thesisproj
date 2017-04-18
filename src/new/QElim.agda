-- Jeremy Pope
-- April 4, 2017


open import Boiler


module QElim where

  -- (Decidable) Atom and friends
  record DecAtom : Set₁ where
    field
      Y : Set                                                      -- value type (e.g. ℕ)
      Atom : ℕ → Set                                               -- atoms, indexed by DeBruijn depth
      ⟦_⟧ₐ : {n : ℕ} → Atom n → Vec Y n → Set                      -- semantics of atoms
      ⟦_⟧ₐ? : {n : ℕ} (a : Atom n) (e : Vec Y n) → Dec (⟦ a ⟧ₐ e)  -- decidability of semantics of an atom


  -- Prerequisite I: decidable atoms
  module WithDecAtom (da : DecAtom) where
    open DecAtom da

    -- Propositions
    data Prop : ℕ → Set where
      atom : {n : ℕ} → Atom n → Prop n
      ~_   : {n : ℕ} → Prop n → Prop n
      _∪_  : {n : ℕ} → Prop n → Prop n → Prop n
      _&_  : {n : ℕ} → Prop n → Prop n → Prop n
      _⇒_  : {n : ℕ} → Prop n → Prop n → Prop n
      E_   : {n : ℕ} → Prop (suc n) → Prop n
      A_   : {n : ℕ} → Prop (suc n) → Prop n

    -- Constructive semantics of Prop
    ⟦_⟧ : {n : ℕ} → Prop n → Vec Y n → Set
    ⟦ atom atm ⟧ as = ⟦ atm ⟧ₐ as
    ⟦ ~ p ⟧ as      = ¬ (⟦ p ⟧ as)
    ⟦ p₁ ∪ p₂ ⟧ as  = (⟦ p₁ ⟧ as) ⊎ (⟦ p₂ ⟧ as)
    ⟦ p₁ & p₂ ⟧ as  = (⟦ p₁ ⟧ as) × (⟦ p₂ ⟧ as)
    ⟦ p₁ ⇒ p₂ ⟧ as  = (⟦ p₁ ⟧ as) → (⟦ p₂ ⟧ as)
    ⟦ E p ⟧ as      = Σ Y (λ a → ⟦ p ⟧ (a ∷ as))
    ⟦ A p ⟧ as      = (a : Y) → (⟦ p ⟧ (a ∷ as))

    -- Quantifier free propositions
    data QFree : {n : ℕ} → Prop n → Set where
      atom : {n : ℕ} (a : Atom n) → QFree (atom {n} a)
      ~_ :   {n : ℕ} {p : Prop n} → QFree p → QFree (~ p)
      _∪_ :  {n : ℕ} {p₁ p₂ : Prop n} → QFree p₁ → QFree p₂ → QFree (p₁ ∪ p₂)
      _&_ :  {n : ℕ} {p₁ p₂ : Prop n} → QFree p₁ → QFree p₂ → QFree (p₁ & p₂)
      _⇒_ :  {n : ℕ} {p₁ p₂ : Prop n} → QFree p₁ → QFree p₂ → QFree (p₁ ⇒ p₂)


    -- A single-step ∃ elimination procedure
    record QE : Set where
      field
        qe       : {n : ℕ} (p : Prop (suc n)) → QFree p → Prop n
        qe-qfree : {n : ℕ} (p : Prop (suc n)) (qf : QFree p) → QFree (qe p qf)
        fwd      : {n : ℕ} (p : Prop (suc n)) (qf : QFree p) (e : Vec Y n) → ⟦ E p ⟧ e → ⟦ qe p qf ⟧ e
        bwd      : {n : ℕ} (p : Prop (suc n)) (qf : QFree p) (e : Vec Y n) → ⟦ qe p qf ⟧ e → ⟦ E p ⟧ e



    qfree-dec : {n : ℕ} → (p : Prop n) → QFree p → (e : Vec Y n) → Dec (⟦ p ⟧ e)
    qfree-dec _ (atom a) e = ⟦ a ⟧ₐ? e
    qfree-dec (~ p) (~ qf) e = ¬? (qfree-dec p qf e)
    qfree-dec (p₁ ∪ p₂) (qf₁ ∪ qf₂) e = (qfree-dec p₁ qf₁ e) ⊎? (qfree-dec p₂ qf₂ e)
    qfree-dec (p₁ ⇒ p₂) (qf₁ ⇒ qf₂) e = (qfree-dec p₁ qf₁ e) ⇒? (qfree-dec p₂ qf₂ e)
    qfree-dec (p₁ & p₂) (qf₁ & qf₂) e = (qfree-dec p₁ qf₁ e) ×? (qfree-dec p₂ qf₂ e)

    qfree-stable : {n : ℕ} (p : Prop n) (qf : QFree p) (e : Vec Y n) → ¬ ¬ (⟦ p ⟧ e) → ⟦ p ⟧ e
    qfree-stable p qf e ¬¬x with qfree-dec p qf e
    ... | yes x = x
    ... | no ¬x = contradiction ¬x ¬¬x

    A→¬E¬ : {n : ℕ} (p : Prop (suc n)) (e : Vec Y n) → ⟦ A p ⟧ e → ⟦ ~ E (~ p) ⟧ e
    A→¬E¬ p e f (a , ¬pa) = ¬pa (f a)

    ¬E¬→A : {n : ℕ} (p : Prop (suc n)) (qf : QFree p) (e : Vec Y n) → ⟦ ~ E (~ p) ⟧ e → ⟦ A p ⟧ e
    ¬E¬→A p qf e x a = qfree-stable p qf (a ∷ e) (λ ¬p → x ((a , ¬p)))

    E-impl : {n : ℕ} {p p' : Prop (suc n)} → ((e : Vec Y (suc n)) → ⟦ p ⟧ e → ⟦ p' ⟧ e) → (e : Vec Y n) → ⟦ E p ⟧ e → ⟦ E p' ⟧ e
    E-impl f e (a , ⟦p⟧) = (a , f (a ∷ e) ⟦p⟧)


    -- General quantifier elimination
    lift-qe : {n : ℕ} → QE → Prop n → Prop n
    lift-qe-qfree : {n : ℕ} (qe : QE) (p : Prop n) → QFree (lift-qe qe p)

    lift-qe _ (atom atm) = atom atm
    lift-qe qe (~ p) = ~ (lift-qe qe p)
    lift-qe qe (p₁ ∪ p₂) = (lift-qe qe p₁) ∪ (lift-qe qe p₂)
    lift-qe qe (p₁ & p₂) = (lift-qe qe p₁) & (lift-qe qe p₂)
    lift-qe qe (p₁ ⇒ p₂) = (lift-qe qe p₁) ⇒ (lift-qe qe p₂)
    lift-qe qe (E p) = QE.qe qe (lift-qe qe p) (lift-qe-qfree qe p)
    lift-qe qe (A p) = ~ (QE.qe qe (~ lift-qe qe p) (~ lift-qe-qfree qe p))

    lift-qe-qfree qe (atom atm) = atom atm
    lift-qe-qfree qe (~ p) = ~ (lift-qe-qfree qe p)
    lift-qe-qfree qe (p₁ ∪ p₂) = (lift-qe-qfree qe p₁) ∪ (lift-qe-qfree qe p₂)
    lift-qe-qfree qe (p₁ & p₂) = (lift-qe-qfree qe p₁) & (lift-qe-qfree qe p₂)
    lift-qe-qfree qe (p₁ ⇒ p₂) = (lift-qe-qfree qe p₁) ⇒ (lift-qe-qfree qe p₂)
    lift-qe-qfree qe (E p) = QE.qe-qfree qe (lift-qe qe p) (lift-qe-qfree qe p)
    lift-qe-qfree qe (A p) = ~ QE.qe-qfree qe (~ lift-qe qe p) (~ lift-qe-qfree qe p)


    -- Correctness of general quantifier elimination
    lift-qe-fwd : {n : ℕ} (qe : QE) (p : Prop n) (e : Vec Y n) → ⟦ p ⟧ e → ⟦ lift-qe qe p ⟧ e
    lift-qe-bwd : {n : ℕ} (qe : QE) (p : Prop n) (e : Vec Y n) → ⟦ lift-qe qe p ⟧ e → ⟦ p ⟧ e

    lift-qe-fwd qe (atom a) e  = id
    lift-qe-fwd qe (~ p) e     = contraposition (lift-qe-bwd qe p e)
    lift-qe-fwd qe (p₁ ∪ p₂) e = Sum.map (lift-qe-fwd qe p₁ e) (lift-qe-fwd qe p₂ e)
    lift-qe-fwd qe (p₁ & p₂) e = Product.map (lift-qe-fwd qe p₁ e) (lift-qe-fwd qe p₂ e)
    lift-qe-fwd qe (p₁ ⇒ p₂) e = λ f → lift-qe-fwd qe p₂ e ∘ f ∘ lift-qe-bwd qe p₁ e
    lift-qe-fwd qe (E p) e     = QE.fwd qe (lift-qe qe p) (lift-qe-qfree qe p) e ∘ (E-impl {p = p} {p' = lift-qe qe p} (lift-qe-fwd qe p) e)
                                 -- λ x → QE.fwd qe (lift-qe qe p) (lift-qe-qfree qe p) e (( proj₁ x , lift-qe-fwd qe p (proj₁ x ∷ e) (proj₂ x) ))
    lift-qe-fwd qe (A p) e     = contraposition (E-impl {p = ~ lift-qe qe p} {p' = ~ p} (λ e' → contraposition (lift-qe-fwd qe p e')) e ∘ QE.bwd qe (~ lift-qe qe p) (lift-qe-qfree qe (~ p)) e) ∘ (A→¬E¬ p e)
                                 -- λ f → contraposition (QE.bwd qe (~ lift-qe qe p) (~ lift-qe-qfree qe p) e) (λ pair → proj₂ pair (lift-qe-fwd qe p (proj₁ pair ∷ e) (f (proj₁ pair))))

    lift-qe-bwd qe (atom a) e  = id
    lift-qe-bwd qe (~ p) e     = contraposition (lift-qe-fwd qe p e)
    lift-qe-bwd qe (p₁ ∪ p₂) e = Sum.map (lift-qe-bwd qe p₁ e) (lift-qe-bwd qe p₂ e)
    lift-qe-bwd qe (p₁ & p₂) e = Product.map (lift-qe-bwd qe p₁ e) (lift-qe-bwd qe p₂ e)
    lift-qe-bwd qe (p₁ ⇒ p₂) e = λ f → lift-qe-bwd qe p₂ e ∘ f ∘ lift-qe-fwd qe p₁ e
    lift-qe-bwd qe (E p) e     = λ x → E-impl {p = lift-qe qe p} {p' = p} (lift-qe-bwd qe p) e (QE.bwd qe (lift-qe qe p) (lift-qe-qfree qe p) e x)
                                 -- λ x → Product.map id (λ {a : ℕ} → lift-qe-bwd qe p (a ∷ e)) (QE.bwd qe (lift-qe qe p) (lift-qe-qfree qe p) e x)
    lift-qe-bwd qe (A p) e     = λ x → λ a → lift-qe-bwd qe p (a ∷ e) (qfree-stable (lift-qe qe p) (lift-qe-qfree qe p) (a ∷ e) (x ∘ QE.fwd qe (~ lift-qe qe p) (~ lift-qe-qfree qe p) e ∘ (λ ¬p → (a , ¬p))))



    -- Prerequisite II: a single-step QE
    module WithQE (qe : QE) where

      -- Constructive semantics are decidable
      ⟦_⟧? : {n : ℕ} → (p : Prop n) → (e : Vec Y n) → Dec (⟦ p ⟧ e)
      ⟦ p ⟧? e with qfree-dec (lift-qe qe p) (lift-qe-qfree qe p) e
      ... | yes ⟦p'⟧e = yes (lift-qe-bwd qe p e ⟦p'⟧e)
      ... | no ¬⟦p'⟧e = no (¬⟦p'⟧e ∘ lift-qe-fwd qe p e)






  -- And then it gets less pretty


  
