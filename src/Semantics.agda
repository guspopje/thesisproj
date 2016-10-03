open import Relation.Binary
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
  
module Semantics {X : Set} {X-dec : Decidable {A = X} _≡_ } where

  open import Function
  open import Data.Nat hiding (_⊔_)
  open import Data.Fin using (Fin)
  open import Data.Bool
  open import Data.Vec
  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Data.Unit

  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation
  open import Relation.Nullary.Decidable
  open import Common
  
  -- open import SecondKind
  open import SucNat {X} {X-dec}

  -- Environments, indexed by permitted binding depth.
  -- Real → value, apparent → value
  Env : ℕ → Set
  Env n = ((X → ℕ) × Vec ℕ n)

  evalReal : {n : ℕ} → X → Env n → ℕ
  evalReal i e = proj₁ e i
  
  evalAppa : {n : ℕ} → Fin n → Env n → ℕ
  evalAppa i e = lookup i (proj₂ e)
  
  empty : (X → ℕ) → Env zero
  empty f = (f , [])
  
  _∷ₑ_ : {n : ℕ} → ℕ → Env n → Env (suc n)
  _∷ₑ_ a (r , as) = (r , a ∷ as)

  {-
  changeReal : {n : ℕ} → X → ℕ → Env n → Env n
  changeReal x a (f , as) = ((λ y → if (⌊ x ≟X y ⌋) then a else f y) , as)

  changeReal-prop : {n : ℕ} → (x : X) → (a : ℕ) → (e : Env n) → evalReal (changeReal x a e) x ≡ a
  changeReal-prop x a (f , as) = {!!}
  -}
  
  ⟦_⟧t : {n : ℕ} → Term n → Env n → ℕ
  ⟦ real x ⟧t = evalReal x
  ⟦ appa n ⟧t = evalAppa n
  ⟦ tzero ⟧t = const zero
  ⟦ tsuc t ⟧t = suc ∘ ⟦ t ⟧t

  ⟦_⟧ₐ : {n : ℕ} → Atom n → Env n → Set
  ⟦ t == t' ⟧ₐ e = (⟦ t ⟧t e) ≡ (⟦ t' ⟧t e)
  
  -- Standard semantics.
  ⟦_⟧ : {n : ℕ} → QH n → Env n → Set
  ⟦ atom a ⟧        = ⟦ a ⟧ₐ
  ⟦ ~ p ⟧           = ¬_ ∘ ⟦ p ⟧
  ⟦ p ∪ q ⟧         = λ e → (⟦ p ⟧ e) ⊎ (⟦ q ⟧ e)
  ⟦ [+] p ⟧         = λ e → (a : ℕ) → ⟦ p ⟧ (a ∷ₑ e)
  ⟦ [-] p ⟧         = λ e → Σ ℕ (λ a → ⟦ p ⟧ (a ∷ₑ e))
  
  -- Gödel-Gentzen double negation translation (GG) semantics.
  ⟦_⟧* : {n : ℕ} → QH n → Env n → Set
  ⟦ atom a ⟧*        = ¬_ ∘ ¬_ ∘ ⟦ a ⟧ₐ                           -- a ==> ¬¬a
  ⟦ ~ p ⟧*           = ¬_ ∘ ⟦ p ⟧*
  ⟦ p ∪ q ⟧*         = λ e → ¬ ((¬ (⟦ p ⟧* e)) × (¬ (⟦ q ⟧* e)))  -- p ∨ q  ==>  ¬(¬p ∧ ¬q)
  ⟦ [+] p ⟧*         = λ e → (a : ℕ) → ⟦ p ⟧* (a ∷ₑ e)
  ⟦ [-] p ⟧*         = λ e → ¬ ((a : ℕ) → ¬ (⟦ p ⟧* (a ∷ₑ e)))   -- ∃x.p ==> ¬(∀x.¬p)

  {-
  _* : {n : ℕ} {p : QH n} {e : Env n} → ⟦ p ⟧ e → ⟦ p ⟧* e
  _* {p = p} {e = e} s with p
  ... | atom a = ¬2 s
  ... | ~ p' = {!!} -- impossible? would need ⟦ p' ⟧* e → ⟦ p' ⟧ e?
  ... | _ = {!!}
  -}

{-
  ⟦ ~ [+] p ⟧* = ¬_ ∘ (λ e → (a : ℕ) → ⟦ p ⟧* (a ∷ₑ e))
               = λ e → ¬ ((a : ℕ) →      ⟦ p ⟧* (a ∷ₑ e))
  ⟦ [-] ~ p ⟧* = λ e → ¬ ((a : ℕ) → ¬ (⟦ ¬ p ⟧* (a ∷ₑ e)))
               = λ e → ¬ ((a : ℕ) → ¬ ¬ (⟦ p ⟧* (a ∷ₑ e)))
-}
  
  -- ¬¬∀x:A.B ⊢ ∀x:A.¬¬B
  ¬¬∀ : {A : Set} {B : A → Set} → (¬ ¬ ((x : A) → (B x))) → ((x : A) → (¬ ¬ (B x)))
  ¬¬∀ f = (λ x → λ ¬Bx → f (λ ∀xB → ¬Bx (∀xB x)))

  -- Reductio ad Absurdum is valid over GG.
  raa* : {n : ℕ} (e : Env n) (p : QH n) → ¬ ¬ (⟦ p ⟧* e) → ⟦ p ⟧* e
  raa* e (atom a) ¬¬s = ¬₃ ¬¬s
  raa* e (~ p) ¬¬s = ¬₃ ¬¬s
  raa* e (p ∪ q) ¬¬s = ¬₃ ¬¬s
  raa* e ([+] p) ¬¬s = λ x → raa* (x ∷ₑ e) p ((¬¬∀ ¬¬s) x)
  raa* e ([-] q) ¬¬s = ¬₃ ¬¬s
  
  {-
  raa** : {n : ℕ} (p : QH n) → (¬_ ∘ ¬_ ∘ ⟦ p ⟧*) ≡ ⟦ p ⟧*
  raa** (atom a) ¬¬s = ¬3 ¬¬s
  raa** (~ p) ¬¬s = ¬3 ¬¬s
  raa** (p ∪ q) ¬¬s = ¬3 ¬¬s
  raa** ([+] p) ¬¬s = λ x → raa* (x ∷ₑ e) p ((¬¬∀ ¬¬s) x)
  raa** ([-] q) ¬¬s = ¬3 ¬¬s
  -}
  
  {-
  ξ₀-lemma : {n : ℕ} (e : Env n) (p : QH n) → (x : ℕ) → (insert x e) ⟦ ξ₀ p ⟧* ≡  e ⟦ p ⟧*
  ξ₀-lemma = {!!}
  -}
  {-
  bind-prop : {n : ℕ} (e : Env n) (x : X) (p : QH n) → e ⟦ p ⟧* ≡ (insert (evalReal e x) e) ⟦ bind x p ⟧*
  bind-prop e x p = {!!}

  flop : ∀ {α} → {T T' : Set α} → T ≡ T' → T → T'
  flop (_≡_.refl) t = t
  -}

  -- Insertion into a context preserves ≡.
  _◂-≡ : {m n : ℕ} {p p' : QH m} (c : Context m n)
    → ⟦ p ⟧* ≡ ⟦ p' ⟧*
    → ⟦ c ◂ p ⟧* ≡ ⟦ c ◂ p' ⟧*
  ∙           ◂-≡ = id
  (c ~∙)      ◂-≡ = c ◂-≡ ∘ cong (_∘_ ¬_)
  (c ⟨∙∪ q ⟩) ◂-≡ = c ◂-≡ ∘ cong (λ s → λ e → ¬ ((¬ (s e)) × (¬ (⟦ q ⟧* e))))
  (c ⟨ p ∪∙⟩) ◂-≡ = c ◂-≡ ∘ cong (λ s → λ e → ¬ ((¬ (⟦ p ⟧* e)) × (¬ (s e))))
  (c [+]∙)    ◂-≡ = c ◂-≡ ∘ cong (λ s → λ e → (a : ℕ) → s (a ∷ₑ e))
  (c [-]∙)    ◂-≡ = c ◂-≡ ∘ cong (λ s → λ e → ¬ ((a : ℕ) → ¬ (s (a ∷ₑ e))))

  -- Insertion into a context preserves ⇄.
  _◂-⇄_ : {m n : ℕ} {p₁ p₂ : QH m} (c : Context m n)
    → ((e : Env m) → ⟦ p₁ ⟧* e ⇄ ⟦ p₂ ⟧* e)
    → ((e : Env n) → ⟦ c ◂ p₁ ⟧* e ⇄ ⟦ c ◂ p₂ ⟧* e)
  ∙           ◂-⇄ eq = eq
  (c ~∙)      ◂-⇄ eq = c ◂-⇄ (λ e → ¬⇄ (eq e))
  (c ⟨∙∪ q ⟩) ◂-⇄ eq = c ◂-⇄ (λ e → ¬⇄ ((¬⇄ (eq e)) ⇄×⇄ (id :⇄: id)))
  (c ⟨ p ∪∙⟩) ◂-⇄ eq = c ◂-⇄ (λ e → ¬⇄ ((id :⇄: id) ⇄×⇄ (¬⇄ (eq e))))
  (c [+]∙)    ◂-⇄ eq = c ◂-⇄ (λ e → Π⇄ (eq ∘ (λ a → a ∷ₑ e)))
  (c [-]∙)    ◂-⇄ eq = c ◂-⇄ (λ e → ¬⇄ (Π⇄ (¬⇄ ∘ eq ∘ (λ a → a ∷ₑ e))))

  ξ₀-∷ₑ : {n : ℕ} → (p : QH n) → (a : ℕ)
    → (λ e → ⟦ ξ₀ p ⟧* (a ∷ₑ e)) ≡ (λ e → ⟦ p ⟧* e)
  ξ₀-∷ₑ = {!!}

  ξ₀-∷ₑ' : {n : ℕ} → (p : QH n) → (a : ℕ) → (e : Env n)
    → ⟦ ξ₀ p ⟧* (a ∷ₑ e) ≡ ⟦ p ⟧* e
  ξ₀-∷ₑ' p a e = cong (λ f → f e) (ξ₀-∷ₑ p a)

  {-
  test : {n : ℕ} → (p : QH n) → (e : Env n)
    → ¬ ⟦ p ⟧* e
    → ((a : ℕ) → ¬ ⟦ ξ₀ p ⟧* (a ∷ₑ e))
  test p e proof a = flop (cong ¬_ (sym (ξ₀-∷ₑ' p a e))) proof
  -}

  ∪-swap : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → ⟦ p₁ ∪ p₂ ⟧* e
    → ⟦ p₂ ∪ p₁ ⟧* e
  ∪-swap p₁ p₂ e s₁₂ = λ pair → s₁₂ (proj₂ pair , proj₁ pair)
    
  ∪⇄ : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → ⟦ p₁ ∪ p₂ ⟧* e ⇄ ⟦ p₂ ∪ p₁ ⟧* e
  ∪⇄ p₁ p₂ e = (∪-swap p₁ p₂ e)
           :⇄: (∪-swap p₂ p₁ e)
  
  private
    module PassageSoundOld where -- ...a bunch of (needlessly?) ugly proofs are given

      

      ~[+]⇄[-]~ : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ ~ [+] Φ ⟧* e ⇄ ⟦ [-] ~ Φ ⟧* e
      ~[+]⇄[-]~ Φ e = (contraposition (λ s → λ a → raa* (a ∷ₑ e) Φ (s a))) :⇄: (contraposition (_∘_ ¬¬-intro))

      ~[-]⇄[+]~ : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ ~ [-] Φ ⟧* e ⇄ ⟦ [+] ~ Φ ⟧* e
      ~[-]⇄[+]~ Φ e = raa* e ([+] ~ Φ) :⇄: ¬¬-intro

      [+]∪-⇄ : {n : ℕ} → (p : QH n) (Φ : QH (suc n)) → (e : Env n)
        → ⟦ ([+] Φ) ∪ p ⟧* e ⇄ ⟦ [+] (Φ ∪ (ξ₀ p)) ⟧* e
      [+]∪-⇄ p Φ e = (λ h → λ a → λ pair → h ((λ g → proj₁ pair (g a)) , (λ s → proj₂ pair (subst id (sym (ξ₀-∷ₑ' p a e)) s))))
                 :⇄: (λ h → λ pair → proj₁ pair (λ a → raa* (a ∷ₑ e) Φ (λ nope → h a (nope , (λ sp → proj₂ pair (subst id (ξ₀-∷ₑ' p a e) sp))))))

      ∪[+]-⇄ : {n : ℕ} → (p : QH n) (Φ : QH (suc n)) → (e : Env n)
        → ⟦ p ∪ ([+] Φ) ⟧* e ⇄ ⟦ [+] ((ξ₀ p) ∪ Φ) ⟧* e
      ∪[+]-⇄ p Φ e = (∪⇄ p ([+] Φ) e)
                  ⇄⇄ ([+]∪-⇄ p Φ e)
                  ⇄⇄ (Π⇄ (λ a → ∪⇄ Φ (ξ₀ p) (a ∷ₑ e)))
      
      [-]∪-⇄ : {n : ℕ} → (p : QH n) (Φ : QH (suc n)) → (e : Env n)
        → ⟦ ([-] Φ) ∪ p ⟧* e ⇄ ⟦ [-] (Φ ∪ (ξ₀ p)) ⟧* e
      [-]∪-⇄ p Φ e = (λ h → λ k → h (¬¬-intro (¬₃ ∘ proj₁ ∘ ¬¬× ∘ k) , subst id (cong ¬_ (ξ₀-∷ₑ' p zero e)) (¬₃ (proj₂ (¬¬× (k zero))))))
                 :⇄: (λ h → λ pair → h (λ a → ¬¬-intro (((raa* e ([+] ~ Φ) (proj₁ pair) a) , ((proj₂ pair) ∘ (subst id (ξ₀-∷ₑ' p a e)))))))

      ∪[-]-⇄ : {n : ℕ} → (p : QH n) (Φ : QH (suc n)) → (e : Env n)
        → ⟦ p ∪ ([-] Φ) ⟧* e ⇄ ⟦ [-] ((ξ₀ p) ∪ Φ) ⟧* e
      ∪[-]-⇄ p Φ e = (∪⇄ p ([-] Φ) e)
                  ⇄⇄ ([-]∪-⇄ p Φ e)
                  ⇄⇄ ¬⇄ (Π⇄ (λ a → ¬⇄ (∪⇄ Φ (ξ₀ p) (a ∷ₑ e))))
                 
    {-
       [+] p    ↦  λ e →       (a : ℕ) →     ⟦ p ⟧* (a ∷ₑ e)
       [+] ~ p  ↦  λ e →       (a : ℕ) →  ¬ (⟦ p ⟧* (a ∷ₑ e))
       ~ [+] p  ↦  λ e →    ¬ ((a : ℕ) →     ⟦ p ⟧* (a ∷ₑ e))      s is one of these, sends a function f : (a : ℕ) → ⟦ p ⟧* (a ∷ₑ e) to ⊥.

       [-] p    ↦  λ e →    ¬ ((a : ℕ) →    ¬ (⟦ p ⟧* (a ∷ₑ e)))
       [-] ~ p  ↦  λ e →    ¬ ((a : ℕ) →  ¬ ¬ (⟦ p ⟧* (a ∷ₑ e)))   need to show
       ~ [-] p  ↦  λ e →  ¬ ¬ ((a : ℕ) →    ¬ (⟦ p ⟧* (a ∷ₑ e)))
    -}

    module PassageSound where
      pass₁-sound : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ ~ [+] Φ ⟧* e → ⟦ [-] ~ Φ ⟧* e
      pass₁-sound Φ e = contraposition (λ s → λ a → raa* (a ∷ₑ e) Φ (s a))

      pass₁'-sound : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ [-] ~ Φ ⟧* e → ⟦ ~ [+] Φ ⟧* e
      pass₁'-sound Φ e = contraposition (_∘_ ¬¬-intro)

      pass₂-sound : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ ~ [-] Φ ⟧* e → ⟦ [+] ~ Φ ⟧* e
      pass₂-sound Φ e = raa* e ([+] ~ Φ)

      pass₂'-sound : {n : ℕ} (Φ : QH (suc n)) → (e : Env n) → ⟦ [+] ~ Φ ⟧* e → ⟦ ~ [-] Φ ⟧* e
      pass₂'-sound Φ e = ¬¬-intro

      pass₃-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ ([+] Φ) ∪ p ⟧* e → ⟦ [+] (Φ ∪ (ξ₀ p)) ⟧* e
      pass₃-sound Φ p e = λ h → λ a → λ pair → h
        ( (λ g → proj₁ pair (g a))
        , (λ s → proj₂ pair (subst id (sym (ξ₀-∷ₑ' p a e)) s)))

      pass₃'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [+] (Φ ∪ (ξ₀ p)) ⟧* e → ⟦ ([+] Φ) ∪ p ⟧* e
      pass₃'-sound Φ p e = λ h → λ pair → proj₁ pair (λ a → raa* (a ∷ₑ e) Φ (λ nope → h a
        (nope , (λ sp → proj₂ pair (subst id (ξ₀-∷ₑ' p a e) sp)))))

      pass₄-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ p ∪ ([+] Φ) ⟧* e → ⟦ [+] ((ξ₀ p) ∪ Φ) ⟧* e
      pass₄-sound Φ p e s = λ a → ∪-swap Φ (ξ₀ p) (a ∷ₑ e) (pass₃-sound Φ p e (∪-swap p ([+] Φ) e s) a)

      pass₄'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [+] ((ξ₀ p) ∪ Φ) ⟧* e → ⟦ p ∪ ([+] Φ) ⟧* e
      pass₄'-sound Φ p e s = ∪-swap ([+] Φ) p e (pass₃'-sound Φ p e (λ a → ∪-swap (ξ₀ p) Φ (a ∷ₑ e) (s a)))

      pass₅-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ ([-] Φ) ∪ p ⟧* e → ⟦ [-] (Φ ∪ (ξ₀ p)) ⟧* e
      pass₅-sound Φ p e = λ h → λ k → h
        ( (¬¬-intro (¬₃ ∘ proj₁ ∘ ¬¬× ∘ k))
        , subst id (cong ¬_ (ξ₀-∷ₑ' p zero e)) (¬₃ (proj₂ (¬¬× (k zero)))))

      pass₅'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [-] (Φ ∪ (ξ₀ p)) ⟧* e → ⟦ ([-] Φ) ∪ p ⟧* e
      pass₅'-sound Φ p e = λ h → λ pair → h (λ a → ¬¬-intro
        ( (raa* e ([+] ~ Φ) (proj₁ pair) a)
        , ((proj₂ pair) ∘ (subst id (ξ₀-∷ₑ' p a e)))))

      pass₆-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ p ∪ ([-] Φ) ⟧* e → ⟦ [-] ((ξ₀ p) ∪ Φ) ⟧* e
      pass₆-sound Φ p e s = λ a → ∪-swap Φ (ξ₀ p) (a ∷ₑ e) (pass₅-sound Φ p e (∪-swap p ([-] Φ) e s) a)

      pass₆'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [-] ((ξ₀ p) ∪ Φ) ⟧* e → ⟦ p ∪ ([-] Φ) ⟧* e
      pass₆'-sound Φ p e s = ∪-swap ([-] Φ) p e (pass₅'-sound Φ p e (λ a → ∪-swap (ξ₀ p) Φ (a ∷ₑ e) (s a)))

--  open PassageSemantics public
{-
  {-

  Reminder

  ⟦_⟧* : {n : ℕ} → QH n → Env n → Set
  ⟦ atom a ⟧*        = ¬_ ∘ ¬_ ∘ ⟦ a ⟧ₐ                           -- atoms get ¬¬
  ⟦ ~ p ⟧*           = ¬_ ∘ ⟦ p ⟧*
  ⟦ p ∪ q ⟧*         = λ e → ¬ ((¬ (⟦ p ⟧* e)) × (¬ (⟦ q ⟧* e)))  -- p ∨ q  ==>  ¬(¬p ∧ ¬q)
  ⟦ [+] p ⟧*         = λ e → (a : ℕ) → ⟦ p ⟧* (a ∷ₑ e)
  ⟦ [-] p ⟧*         = λ e → ¬ ((a : ℕ) → ¬ (⟦ p ⟧* (a ∷ₑ e)))   -- ∃x.p ==> ¬(∀x.¬p)
  -}

  →-⊃ : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → (⟦ p₁ ⟧* e → ⟦ p₂ ⟧* e)
    → (⟦ p₁ ⊃ p₂ ⟧* e)
  →-⊃ _ _ _ f = λ k → proj₁ k (proj₂ k ∘ f)

  arithSound* : {p : QH0} → Ticket p → (e : Env zero) → ⟦ p ⟧* e
  arithSound* (h1 x) e = ¬¬-intro refl
  arithSound* (h2 x y) e = →-⊃
    (atom ((real x) == (real y)))
    (atom ((real y) == (real x)))
    e
    (¬¬-map sym)
  {-
    h1 : (x : X) → Ticket (x ==' x)
        h2 : (x y : X) → Ticket ((x ==' y) ⊃ (y ==' x))
        h3 : (x y z : X) → Ticket (((x ==' y) & (y ==' z)) ⊃ (x ==' z))
        h4 : (x y : X) → Ticket ((x ==' y) ≡≡ atom ((tsuc (real x)) == (tsuc (real y))))
        h5 : (x : X) → Ticket (~ atom (tsuc (real x) == tzero))
        h6 : (x : X) → (n : ℕ) → Ticket (~ atom ((real x) == ((real x) +' (suc n))))
        h7 : (x : X) → Ticket ((atom ((real x) == tzero)) ∪ ([-] (atom ((real x) == (tsuc (appa zero))))))
  -}
  arithSound* _ e = {!!}
  
  -- SucNat is sound under the GG semantics.
  soundness* : {p : QH0} → ProofQH p → (e : Env zero) → ⟦ p ⟧* e
  soundness* (fromFK p elem f proof) e = {!!}
    -- rules of passage
  soundness* (~[+]/[-]~ {Φ = Φ} c proof) e = fwd ((c ◂-⇄ (~[+]⇄[-]~ Φ)) e) (soundness* proof e)
  soundness* ([-]~/~[+] {Φ = Φ} c proof) e = bck ((c ◂-⇄ (~[+]⇄[-]~ Φ)) e) (soundness* proof e)
  soundness* (~[-]/[+]~ {Φ = Φ} c proof) e = fwd ((c ◂-⇄ (~[-]⇄[+]~ Φ)) e) (soundness* proof e)
  soundness* ([+]~/~[-] {Φ = Φ} c proof) e = bck ((c ◂-⇄ (~[-]⇄[+]~ Φ)) e) (soundness* proof e)
  soundness* ([+]∪-in  {Φ = Φ} {p = p} c proof) e = fwd ((c ◂-⇄ ([+]∪-⇄ p Φ)) e) (soundness* proof e)
  soundness* ([+]∪-out {Φ = Φ} {p = p} c proof) e = bck ((c ◂-⇄ ([+]∪-⇄ p Φ)) e) (soundness* proof e)
  soundness* (∪[+]-in  {Φ = Φ} {p = p} c proof) e = fwd ((c ◂-⇄ (∪[+]-⇄ p Φ)) e) (soundness* proof e)
  soundness* (∪[+]-out {Φ = Φ} {p = p} c proof) e = bck ((c ◂-⇄ (∪[+]-⇄ p Φ)) e) (soundness* proof e)
  soundness* ([-]∪-in  {Φ = Φ} {p = p} c proof) e = fwd ((c ◂-⇄ ([-]∪-⇄ p Φ)) e) (soundness* proof e)
  soundness* ([-]∪-out {Φ = Φ} {p = p} c proof) e = bck ((c ◂-⇄ ([-]∪-⇄ p Φ)) e) (soundness* proof e)
  soundness* (∪[-]-in  {Φ = Φ} {p = p} c proof) e = fwd ((c ◂-⇄ (∪[-]-⇄ p Φ)) e) (soundness* proof e)
  soundness* (∪[-]-out {Φ = Φ} {p = p} c proof) e = bck ((c ◂-⇄ (∪[-]-⇄ p Φ)) e) (soundness* proof e)
  soundness* (gen1 {p} x proof) e = {!!}
  soundness* (gen2 {p} x y proofyx) e = {!!}
  soundness* (simp {p} p∪pProof) e = raa* e p (λ ¬⟦p⟧* → (soundness* p∪pProof e) (¬⟦p⟧* , ¬⟦p⟧*))
  soundness* (mp {p} {q} pqProof pProof) e = raa* e q (λ ¬⟦q⟧* → soundness* pqProof e (¬2 (soundness* pProof e) , ¬⟦q⟧*))
  soundness* (external t) e = arithSound* t e

  {-
  data ProofQH : QH0 → Set1 where
        fromFK : {C : Set} (p : QH0) (e : elementary p) (f : Atom zero ↣ C)
          → ProofFK (mapSF (_⟨$⟩_ (Injection.to f)) p e)
          → ProofQH p
        ~[+]-rule : {n : ℕ} {Φ : QH (suc n)} → (c : Context n zero)
          → ProofQH (c ◂ (~ [+] Φ))
          → ProofQH (c ◂ ([-] ~ Φ))
        [-]~-rule : {n : ℕ} {Φ : QH (suc n)} → (c : Context n zero)
          → ProofQH (c ◂ ([-] ~ Φ))
          → ProofQH (c ◂ (~ [+] Φ))
        ~[-]-rule : {n : ℕ} {Φ : QH (suc n)} → (c : Context n zero)
          → ProofQH (c ◂ (~ [-] Φ))
          → ProofQH (c ◂ ([+] ~ Φ))
        [+]~-rule : {n : ℕ} {Φ : QH (suc n)} → (c : Context n zero)
          → ProofQH (c ◂ ([+] ~ Φ))
          → ProofQH (c ◂ (~ [-] Φ))
        [+]∪-in  : {n : ℕ} {Φ : QH (suc n)} {p : QH n} →
          → ProofQH (c ◂ (([+] Φ) ∪ p))
          → ProofQH (c ◂ ([+] (Φ ∪ (ξ₀ p))))
        [+]∪-out : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ ([+] (Φ ∪ (ξ₀ p))))
          → ProofQH (c ◂ (([+] Φ) ∪ p))
        ∪[+]-in  : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ (p ∪ ([+] Φ)))
          → ProofQH (c ◂ ([+] ((ξ₀ p) ∪ Φ)))
        ∪[+]-out : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ ([+] ((ξ₀ p) ∪ Φ)))
          → ProofQH (c ◂ (p ∪ ([+] Φ)))
        [-]∪-in  : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ (([-] Φ) ∪ p))
          → ProofQH (c ◂ ([-] (Φ ∪ (ξ₀ p))))
        [-]∪-out : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ ([-] (Φ ∪ (ξ₀ p))))
          → ProofQH (c ◂ (([-] Φ) ∪ p))
        ∪[-]-in  : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ (p ∪ ([-] Φ)))
          → ProofQH (c ◂ ([-] ((ξ₀ p) ∪ Φ)))
        ∪[-]-out : {n : ℕ} {c : Context n zero} {Φ : QH (suc n)} {p : QH n}
          → ProofQH (c ◂ ([-] ((ξ₀ p) ∪ Φ)))
          → ProofQH (c ◂ (p ∪ ([-] Φ)))
        gen1 : {p : QH0} (x : X)
          → ProofQH p
          → ProofQH ([+] (bind x p))
        gen2 : {p : QH0} (x y : X)
          → ProofQH (sub y x p)
          → ProofQH ([-] (bind y p))
        simp : {p : QH0}
          → ProofQH (p ∪ p)
          → ProofQH p
        mp : {p q : QH0}
          → ProofQH (p ⊃ q)
          → ProofQH p
          → ProofQH q
        external : {p : QH0}
          → Ticket p
          → ProofQH p
  -}

  
  {-
    
    Need to give an element of type:
        e ⟦ [+] (bind x p) ⟧*
      = λ a → (insert a e) ⟦ bind x p ⟧*

    So for a given y, we must give an element of type:

      (insert a e) ⟦ bind x p ⟧*

    This is equivalent to the semantics of p under e modified such that variable x maps to the number a:

      e' = adjust x a e
      e' ⟦ p ⟧* ≡ (insert a e) ⟦ bind x p ⟧*

    But that may be hard to prove.

      
    So first let's show that:

      ∀ (x, p) → x ∉ bind x p
      
      ∀ (x, p) → (e e' : Env) → (e and e' only differ at x) → x ∉ p → e ⟦ p ⟧* ≡ e' ⟦ p ⟧*

      THM : ∀ (e, x, p) → e ⟦ p ⟧* ≡ (insert (evalReal e x) e) ⟦ bind x p ⟧*

      Then since x ∉ bind x p, we can do:

        e' = e modified so that x ↦ a
          evalReal e' x = a
          e' differs from e only at x
          (insert a e') differs from (insert a e) only at x
        
        ==> (insert a e') ⟦ bind x p ⟧ ≡ (insert a e) ⟦ bind x p ⟧
      
      Then we apply THM with e':

        ==> e' ⟦ p ⟧* ≡ (insert (evalReal e' x) e') ⟦ bind x p ⟧*
          = e' ⟦ p ⟧* ≡ (insert a e') ⟦ bind x p ⟧*
        
      Then by trans prop we get:

        e' ⟦ p ⟧* ≡ (insert a e) ⟦ bind x p ⟧

      A recursive call gets us an element of the former type, and we're done.
      
      
  -}
-}
