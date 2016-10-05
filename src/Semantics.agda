open import Relation.Binary
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
  
module Semantics {X : Set} {X-dec : Decidable {A = X} _≡_ } where

  open import Function
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties using (m≢1+m+n)
  open import Data.Nat.Properties.Simple using (+-comm)
  open import Data.Fin using (Fin)
  open import Data.Bool
  open import Data.Vec
  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Data.Unit

  open import Relation.Nullary
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

  adjustReal : {n : ℕ} → X → ℕ → Env n → Env n
  adjustReal x₀ a (reals , appas) = ((λ x → if ⌊ X-dec x x₀ ⌋ then a else reals x) , appas)

  adjustReal= : {n : ℕ} → (x₀ : X) → (a : ℕ) → (e : Env n) →
    (x : X) → x ≡ x₀ → evalReal x (adjustReal x₀ a e) ≡ a
  adjustReal= x₀ a e x x≡x₀ with X-dec x x₀
  ... | yes _    = refl
  ... | no  x≢x₀ = contradiction x≡x₀ x≢x₀

  adjustReal≠ : {n : ℕ} → (x₀ : X) → (a : ℕ) → (e : Env n) →
    (x : X) → x ≢ x₀ → evalReal x (adjustReal x₀ a e) ≡ evalReal x e
  adjustReal≠ x₀ a e x x≢x₀ with X-dec x x₀
  ... | yes x≡x₀ = contradiction x≡x₀ x≢x₀
  ... | no  _    = refl

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

  -- Semantics of ∪ and & have the usual injections and projections
  inj₁* : {n : ℕ} {p₁ p₂ : QH n} {e : Env n} → ⟦ p₁ ⟧* e → ⟦ p₁ ∪ p₂ ⟧* e
  inj₁* = flip proj₁

  inj₂* : {n : ℕ} {p₁ p₂ : QH n} {e : Env n} → ⟦ p₂ ⟧* e → ⟦ p₁ ∪ p₂ ⟧* e
  inj₂* = flip proj₂

  proj₁* : {n : ℕ} {p₁ p₂ : QH n} {e : Env n} → ⟦ p₁ & p₂ ⟧* e → ⟦ p₁ ⟧* e
  proj₁* {p₁ = p₁} {e = e} s = raa* e p₁ (¬₃ (proj₁ (¬¬× s)))
  
  proj₂* : {n : ℕ} {p₁ p₂ : QH n} {e : Env n} → ⟦ p₁ & p₂ ⟧* e → ⟦ p₂ ⟧* e
  proj₂* {p₂ = p₂} {e = e} s = raa* e p₂ (¬₃ (proj₂ (¬¬× s)))

{-
⟦ p ∪ q ⟧* e = ¬ ((¬ (⟦ p ⟧* e)) × (¬ (⟦ q ⟧* e)))  -- p ∨ q  ==>  ¬(¬p ∧ ¬q)

⟦ p & q ⟧* e = ¬ ⟦ ¬ p ∪ ¬ q ⟧* = ¬ ¬ ((¬ ¬ (⟦ p ⟧* e)) × (¬ ¬ (⟦ q ⟧* e)))
-}

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

  ¬∪-swap : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → ¬ ⟦ p₁ ∪ p₂ ⟧* e
    → ¬ ⟦ p₂ ∪ p₁ ⟧* e
  ¬∪-swap p₁ p₂ e = contraposition (∪-swap p₂ p₁ e)



  ∪⇄ : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → ⟦ p₁ ∪ p₂ ⟧* e ⇄ ⟦ p₂ ∪ p₁ ⟧* e
  ∪⇄ p₁ p₂ e = (∪-swap p₁ p₂ e)
           :⇄: (∪-swap p₂ p₁ e)
  
  private
    
    module PassageSound where

      -- Helpful for showing symmetrical versions.
      ◂-∪ : {m n : ℕ} → (c : Context m n) → (p₁ p₂ : QH m) → (e : Env n)
        → ⟦ c ◂ (p₁ ∪ p₂) ⟧* e
        → ⟦ c ◂ (p₂ ∪ p₁) ⟧* e
      ◂-∪ c Φ₁ Φ₂ e s = fwd ((_◂-⇄_ {p₁ = Φ₁ ∪ Φ₂} {p₂ = Φ₂ ∪ Φ₁} c (∪⇄ Φ₁ Φ₂) ) e) s

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
      pass₄-sound Φ p e s = ◂-∪ (∙ [+]∙) Φ (ξ₀ p) e (pass₃-sound Φ p e (∪-swap p ([+] Φ) e s))

      pass₄'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [+] ((ξ₀ p) ∪ Φ) ⟧* e → ⟦ p ∪ ([+] Φ) ⟧* e
      pass₄'-sound Φ p e s = ∪-swap ([+] Φ) p e (pass₃'-sound Φ p e (◂-∪ (∙ [+]∙) (ξ₀ p) Φ e s))

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
      pass₆-sound Φ p e s = ◂-∪ (∙ [-]∙) Φ (ξ₀ p) e (pass₅-sound Φ p e (∪-swap p ([-] Φ) e s)) 

      pass₆'-sound : {n : ℕ} → (Φ : QH (suc n)) (p : QH n) → (e : Env n)
        → ⟦ [-] ((ξ₀ p) ∪ Φ) ⟧* e → ⟦ p ∪ ([-] Φ) ⟧* e
      pass₆'-sound Φ p e s = ∪-swap ([-] Φ) p e (pass₅'-sound Φ p e (◂-∪ (∙ [-]∙) (ξ₀ p) Φ e s))

{-
      passage-sound : {n : ℕ} → {p₁ p₂ : QH n} → (e : Env n) → Passage p₁ p₂ → ⟦ p₁ ⟧* e → ⟦ p₂ ⟧* e
      passage-sound e (pass₁ {Φ = Φ}) = pass₁-sound Φ e
      passage-sound e (pass₂ {Φ = Φ}) = pass₂-sound Φ e
      passage-sound e (pass₃ {Φ = Φ} {p = p}) = pass₃-sound Φ p e
      passage-sound e (pass₄ {Φ = Φ} {p = p}) = pass₄-sound Φ p e
      passage-sound e (pass₅ {Φ = Φ} {p = p}) = pass₅-sound Φ p e
      passage-sound e (pass₆ {Φ = Φ} {p = p}) = pass₆-sound Φ p e
      passage-sound e (vice-versa (pass₁ {Φ = Φ})) = pass₁'-sound Φ e
      passage-sound e (vice-versa (pass₂ {Φ = Φ})) = pass₂'-sound Φ e
      passage-sound e (vice-versa (pass₃ {Φ = Φ} {p = p})) = pass₃'-sound Φ p e
      passage-sound e (vice-versa (pass₄ {Φ = Φ} {p = p})) = pass₄'-sound Φ p e
      passage-sound e (vice-versa (pass₅ {Φ = Φ} {p = p})) = pass₅'-sound Φ p e
      passage-sound e (vice-versa (pass₆ {Φ = Φ} {p = p})) = pass₆'-sound Φ p e
      passage-sound e (vice-versa (vice-versa pass)) = passage-sound e pass
-}

      passage-sound : {n : ℕ} → {p₁ p₂ : QH n} → Passage p₁ p₂ → (e : Env n) → ⟦ p₁ ⟧* e ⇄ ⟦ p₂ ⟧* e
      passage-sound (pass₁ {Φ = Φ}) e = pass₁-sound Φ e :⇄: pass₁'-sound Φ e
      passage-sound (pass₂ {Φ = Φ}) e = pass₂-sound Φ e :⇄: pass₂'-sound Φ e
      passage-sound (pass₃ {Φ = Φ} {p = p}) e = pass₃-sound Φ p e :⇄: pass₃'-sound Φ p e
      passage-sound (pass₄ {Φ = Φ} {p = p}) e = pass₄-sound Φ p e :⇄: pass₄'-sound Φ p e
      passage-sound (pass₅ {Φ = Φ} {p = p}) e = pass₅-sound Φ p e :⇄: pass₅'-sound Φ p e
      passage-sound (pass₆ {Φ = Φ} {p = p}) e = pass₆-sound Φ p e :⇄: pass₆'-sound Φ p e
      passage-sound (vice-versa pass) e = ⇄-flip (passage-sound pass e)

  open PassageSound

  {-

  Reminder

  ⟦_⟧* : {n : ℕ} → QH n → Env n → Set
  ⟦ atom a ⟧*        = ¬_ ∘ ¬_ ∘ ⟦ a ⟧ₐ                           -- atoms get ¬¬
  ⟦ ~ p ⟧*           = ¬_ ∘ ⟦ p ⟧*
  ⟦ p ∪ q ⟧*         = λ e → ¬ ((¬ (⟦ p ⟧* e)) × (¬ (⟦ q ⟧* e)))  -- p ∨ q  ==>  ¬(¬p ∧ ¬q)
  ⟦ [+] p ⟧*         = λ e → (a : ℕ) → ⟦ p ⟧* (a ∷ₑ e)
  ⟦ [-] p ⟧*         = λ e → ¬ ((a : ℕ) → ¬ (⟦ p ⟧* (a ∷ₑ e)))   -- ∃x.p ==> ¬(∀x.¬p)

  Env : ℕ → Set
  Env n = ((X → ℕ) × Vec ℕ n)

  evalReal : {n : ℕ} → X → Env n → ℕ
  evalReal i e = proj₁ e i
  
  evalAppa : {n : ℕ} → Fin n → Env n → ℕ
  evalAppa i e = lookup i (proj₂ e)

  ⟦_⟧t : {n : ℕ} → Term n → Env n → ℕ
  ⟦ real x ⟧t = evalReal x
  ⟦ appa n ⟧t = evalAppa n
  ⟦ tzero ⟧t = const zero
  ⟦ tsuc t ⟧t = suc ∘ ⟦ t ⟧t

  ⟦_⟧ₐ : {n : ℕ} → Atom n → Env n → Set
  ⟦ t == t' ⟧ₐ e = (⟦ t ⟧t e) ≡ (⟦ t' ⟧t e)
  -}

  →-⊃ : {n : ℕ} → (p₁ p₂ : QH n) → (e : Env n)
    → (⟦ p₁ ⟧* e → ⟦ p₂ ⟧* e)
    → (⟦ p₁ ⊃ p₂ ⟧* e)
  →-⊃ _ _ _ f = λ k → proj₁ k (proj₂ k ∘ f)

{-
  foldsuc-suc : (k x : ℕ) → (fold (suc x) suc k) ≡ suc (fold x suc k)
  foldsuc-suc zero x = refl
  foldsuc-suc (suc k) x = cong suc (foldsuc-suc k x)

  ≡-pred : {m n : ℕ} → suc m ≡ suc n → m ≡ n
  ≡-pred refl = refl

  no-cycles : (k x : ℕ) → x ≢ (fold x suc (suc k))
  no-cycles k zero = λ ()
  no-cycles k (suc x) = contraposition (λ s → subst (λ y → x ≡ y) (foldsuc-suc k x) (≡-suc s)) (no-cycles k x)
-}

  +'-eval : {n : ℕ} → (e : Env n) (x : X) (k : ℕ) → ⟦ (real x) +' k ⟧t e ≡ k + ⟦ real x ⟧t e
  +'-eval e x zero = refl
  +'-eval e x (suc k) = cong suc (+'-eval e x k)

  ≡-pred : {m n : ℕ} → suc m ≡ suc n → m ≡ n
  ≡-pred {m} {.m} refl = refl

  m≢1+n+m : (m n : ℕ) → m ≢ suc (n + m)
  m≢1+n+m m n = subst (λ x → m ≢ suc x) (+-comm m n) (m≢1+m+n m)

  ==-≡ : {n : ℕ} {t₁ t₂ : Term n} {e : Env n} → ⟦ atom (t₁ == t₂) ⟧* e → ⟦ t₁ ⟧t e ≡ ⟦ t₂ ⟧t e
  ==-≡ {t₁ = t₁} {t₂ = t₂} {e = e} ¬¬⟦⟧ with ((⟦ t₁ ⟧t e) Data.Nat.≟ (⟦ t₂ ⟧t e))
  ... | yes eq = eq
  ... | no neq = contradiction neq ¬¬⟦⟧


  arithSound* : {p : QH0} → Ticket p → (e : Env zero) → ⟦ p ⟧* e
  arithSound* (h1 x) e = ¬¬-intro refl
  arithSound* (h2 x y) e = →-⊃ (atom ((real x) == (real y))) (atom ((real y) == (real x))) e (¬¬-map sym)
  arithSound* (h3 x y z) e = →-⊃ ((x ==' y) & (y ==' z)) (x ==' z) e
    (λ both → ¬¬-intro (trans
      (==-≡ {t₁ = real x} {t₂ = real y} {e = e} (proj₁* {p₁ = x ==' y} {p₂ = y ==' z} {e = e} both))
      (==-≡ {t₁ = real y} {t₂ = real z} {e = e} (proj₂* {p₁ = x ==' y} {p₂ = y ==' z} {e = e} both))))
  arithSound* (h4 x y) e = ¬¬-intro
    ( ¬¬-intro (→-⊃ (x ==' y) (atom (tsuc (real x) == tsuc (real y))) e (λ s → ¬¬-intro (cong suc (==-≡ {t₁ = real x} {t₂ = real y} {e = e} s))))
    , ¬¬-intro ((→-⊃ (atom (tsuc (real x) == tsuc (real y))) (x ==' y) e (λ s → ¬¬-intro (≡-pred (==-≡ {t₁ = tsuc (real x)} {t₂ = tsuc (real y)} {e = e} s))))))
  arithSound* (h5 x) e with ⟦ real x ⟧t e
  arithSound* (h5 x) e | ⟦x⟧ = ¬¬-intro (λ ())
  arithSound* (h6 x k) e = ¬¬-intro (λ eq → m≢1+n+m (⟦ real x ⟧t e) k (trans eq (+'-eval e x (suc k))))
  arithSound* (h7 x) e with ⟦ real x ⟧t e
  arithSound* (h7 x) e | zero    = λ pair → proj₁ pair (¬¬-intro refl)
  arithSound* (h7 x) e | (suc m) = λ pair → proj₂ pair (λ h → h m (¬¬-intro refl))
  {-
        h1 : (x : X) → Ticket (x ==' x)
        h2 : (x y : X) → Ticket ((x ==' y) ⊃ (y ==' x))
        h3 : (x y z : X) → Ticket (((x ==' y) & (y ==' z)) ⊃ (x ==' z))
        h4 : (x y : X) → Ticket ((x ==' y) ≡≡ atom ((tsuc (real x)) == (tsuc (real y))))
        h5 : (x : X) → Ticket (~ atom (tsuc (real x) == tzero))
        h6 : (x : X) → (n : ℕ) → Ticket (~ atom ((real x) == ((real x) +' (suc n))))
        h7 : (x : X) → Ticket ((atom ((real x) == tzero)) ∪ ([-] (atom ((real x) == (tsuc (appa zero))))))
  -}

  gen₁-helper-term : {n : ℕ} (x : X) (t : Term n) (e : Env n) (a : ℕ) →
    ⟦ t ⟧t (adjustReal x a e) ≡ ⟦ T.r→a x Data.Fin.zero (T.ξ zero t) ⟧t (a ∷ₑ e)
  gen₁-helper-term x t e a = {!!}

  gen₁-helper : {n : ℕ} (x : X) (p : QH n) (e : Env n) (a : ℕ) →
    ⟦ p ⟧* (adjustReal x a e) ≡ ⟦ bind₀ x p ⟧* (a ∷ₑ e)
  gen₁-helper x (atom (t₁ == t₂)) e a = cong (¬_ ∘ ¬_)
    (cong₂ _≡_
      (gen₁-helper-term x t₁ e a)
      (gen₁-helper-term x t₂ e a))
  gen₁-helper x (~ p) e a = cong ¬_ (gen₁-helper x p e a)
  gen₁-helper x (p₁ ∪ p₂) e a = cong₂ (λ s₁ s₂ → ¬ (¬ s₁ × ¬ s₂)) (gen₁-helper x p₁ e a) (gen₁-helper x p₂ e a)
  gen₁-helper x ([+] p) e a = {!!}
  gen₁-helper x ([-] p) e a = {!!}

  {-
    proofyx : ⊢ sub y x p    ⊢ p(x,x)
    
  -}

  -- SucNat is sound under the GG semantics.
  soundness* : {p : QH0} → ProofQH p → (e : Env zero) → ⟦ p ⟧* e
  soundness* (fromFK p elem proof) e       = {!!}
  soundness* (passage (at c pass) proof) e = fwd (_◂-⇄_ c (passage-sound pass) e) (soundness* proof e)
  soundness* (gen₁ {p} x proof) e          = λ a → subst id (gen₁-helper x p e a)
                                               (soundness* proof (adjustReal x a e))
  soundness* (gen₂ {p} x y proofyx) e      = {!!}
  soundness* (simp {p} p∪pProof) e         = raa* e p (λ ¬⟦p⟧* → (soundness* p∪pProof e) (¬⟦p⟧* , ¬⟦p⟧*))
  soundness* (mp {p} {q} pqProof pProof) e = raa* e q (λ ¬⟦q⟧* → soundness* pqProof e
                                               (¬¬-intro (soundness* pProof e) , ¬⟦q⟧*))
  soundness* (external t) e = arithSound* t e
