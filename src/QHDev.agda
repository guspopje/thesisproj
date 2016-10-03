import SecondKind

open import Data.Nat using (ℕ ; _+_ ; zero ; suc)
open import Data.Bool using (Bool ; true ; false)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_)
open import Common
open import Function using (id ; const)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂ ; subst ; subst₂ ; sym)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Sum

module QHDev (atomic : SecondKind.Atomic) (ts : SecondKind.QH-Atomic.TicketSystem atomic) where
  open import FirstKind renaming (_⊃_ to _⊃₁_ ; _&_ to _&₁_ ; _≣_ to _≣₁_ ;  _≣!_ to _≣!₁_ ; ≣-refl to ≣₁-refl ; ≣-sym to ≣₁-sym) hiding (interpret)
  open SecondKind
  open SecondKind.QH-Atomic atomic
  open Proofs ts


  module SimpleProperties where
    open Atomic atomic using (Atom ; X)
    -- Property: mapFS only produces elementary propositions.
    mapFS-elem : ∀{β} {C : Set β} → (f : C → Atom zero) → (p : FK C) → elementary (mapFS f p)
    mapFS-elem f (atom a) = tt
    mapFS-elem f (~ p) = mapFS-elem f p
    mapFS-elem f (p ∪ q) = (mapFS-elem f p , mapFS-elem f q)

    -- Raise only produces elementary propositions
    raise-elem : (p : FK (Atom zero)) → elementary (raise p)
    raise-elem = mapFS-elem id

    -- For elementary propositions of the second kind, (raise ∘ lower) p = p
    raise∘lower : (p : QH0) → (e : elementary p) → raise (lower p e) ≡ p
    raise∘lower (atom a) e = refl
    raise∘lower (~ p) e = cong {A = QH0} {B = QH0} ~_
      (raise∘lower p e)
    raise∘lower (p₁ ∪ p₂) e = cong₂ {A = QH0} {B = QH0} {C = QH0} _∪_
      (raise∘lower p₁ (proj₁ e))
      (raise∘lower p₂ (proj₂ e))
    raise∘lower ([+] p) ()
    raise∘lower ([-] p) ()

    -- For all propositions of the first kind, (lower ∘ raise) p = p
    lower∘raise : (p : FK (Atom zero)) → lower (raise p) (raise-elem p) ≡ p
    lower∘raise (atom a) = refl
    lower∘raise (~ p) = cong ~_ (lower∘raise p)
    lower∘raise (p₁ ∪ p₂) = cong₂ _∪_ (lower∘raise p₁) (lower∘raise p₂)


    -- Raising edition.
    fromFK' : {p : FK (Atom zero)} → ProofFK p → ProofQH (raise p)
    fromFK' {p} proof = (fromFK (raise p) (raise-elem p)) (subst ProofFK (sym (lower∘raise p)) proof)

    -- A trivial result of raise preserving structure.
    raise-⊃ : {p q : FK (Atom zero)} → ProofFK (p ⊃₁ q) → ProofQH ((raise p) ⊃ (raise q))
    raise-⊃ = fromFK'


    _∈_ : {n : ℕ} → X → QH n → Set
    _∈_ x = QHrec
      (const Set)
      (Atomic._∈_ atomic x)
      id
      _⊎_
      id
      id

    _∉_ : {n : ℕ} → X → QH n → Set
    x ∉ p = ¬ (x ∈ p)

    --Passage′ 
      
  open SimpleProperties public

  module Context-stuff where
    -- Compose two contexts
    infix 11 _◂◂_
    _◂◂_ : {m n k : ℕ} → Context k n → Context m k → Context m n
    c ◂◂ ∙ = c
    c ◂◂ (c' ~∙) = (c ◂◂ c') ~∙
    c ◂◂ (c' ⟨∙∪ p₂ ⟩) = (c ◂◂ c') ⟨∙∪ p₂ ⟩
    c ◂◂ (c' ⟨ p₁ ∪∙⟩) = (c ◂◂ c') ⟨ p₁ ∪∙⟩
    c ◂◂ (c' [+]∙) = (c ◂◂ c') [+]∙
    c ◂◂ (c' [-]∙) = (c ◂◂ c') [-]∙

    -- Show that composition behaves as required
    ◂◂-works : {m n k : ℕ} → (c₁ : Context k n) → (c₂ : Context m k) → (p : QH m) → ((c₁ ◂◂ c₂) ◂ p) ≡ (c₁ ◂ (c₂ ◂ p))
    ◂◂-works c ∙ p              = refl
    ◂◂-works c (c' ~∙) p        = ◂◂-works c c' (~ p)
    ◂◂-works c (c' ⟨∙∪ p₂ ⟩) p  = ◂◂-works c c' (p ∪ p₂)
    ◂◂-works c (c' ⟨ p₁ ∪∙⟩) p  = ◂◂-works c c' (p₁ ∪ p)
    ◂◂-works c (c' [+]∙) p      = ◂◂-works c c' ([+] p)
    ◂◂-works c (c' [-]∙) p      = ◂◂-works c c' ([-] p)

    -- How deep is the context, in terms of quantifiers?
    -- Will equal m - n, but that is not so useful at the moment.
    ◂-depth : {m n : ℕ} → Context m n → ℕ
    ◂-depth ∙ = zero
    ◂-depth (c ~∙) = ◂-depth c
    ◂-depth (c ⟨∙∪ _ ⟩) = ◂-depth c
    ◂-depth (c ⟨ _ ∪∙⟩) = ◂-depth c
    ◂-depth (c [+]∙) = suc (◂-depth c)
    ◂-depth (c [-]∙) = suc (◂-depth c)

    _◂-Somewhere_ : {m n : ℕ} {Φ₁ Φ₂ : QH m} {R : {l : ℕ} → QH l → QH l → Set} (c : Context m n) → Somewhere R Φ₁ Φ₂ → Somewhere R (c ◂ Φ₁) (c ◂ Φ₂)
    _◂-Somewhere_ {R = R} c (at {_} {Φ₁} {Φ₂} c' r) = subst₂ (Somewhere R) (◂◂-works c c' Φ₁) (◂◂-works c c' Φ₂) (at (c ◂◂ c') r)

    somewhere-sym : {n : ℕ} {R : {m : ℕ} → QH m → QH m → Set} → ({m : ℕ} → symmetric (R {m})) → symmetric (Somewhere {n} R)
    somewhere-sym rsym (at c x) = at c (rsym x)

    _◂-Somewhere⋆_ :  {m n : ℕ} {Φ₁ Φ₂ : QH m} {R : {l : ℕ} → QH l → QH l → Set} (c : Context m n) → (Somewhere R ⋆) Φ₁ Φ₂ → (Somewhere R ⋆) (c ◂ Φ₁) (c ◂ Φ₂)
    _◂-Somewhere⋆_ {R = R} c refl⋆ = refl⋆
    _◂-Somewhere⋆_ {R = R} c (trans⋆ s ss) = trans⋆ (c ◂-Somewhere s) (c ◂-Somewhere⋆ ss)

    SP-sym : {n : ℕ} → symmetric (SP {n})
    SP-sym = somewhere-sym vice-versa
    SP⋆-sym : {n : ℕ} → symmetric (SP⋆ {n})
    SP⋆-sym = symmetric⋆ SP-sym
  open Context-stuff public



  module Equiv where
    -- Summary: p₁ ≈ p₂ means p₁ and p₂ are "interchangeable" as far as a proposition's truth is concerned.
    -- More explicitly, for any context c, proofs of c ◂ p₁ and c ◂ p₂ may be derived from one another.
    infix 3 _≈_
    _≈_ : {n : ℕ} → QH n → QH n → Set₁
    _≈_ {n = n} p₁ p₂ = (c : Context n zero) → ⊢ (c ◂ p₁) ⇄ ⊢ (c ◂ p₂)

    -- It's an equivalence relation.

    ≈-refl : {n : ℕ} {p : QH n} → p ≈ p
    ≈-refl {p = p} c = id :⇄: id

    ≈-sym : {n : ℕ} {p q : QH n} → p ≈ q → q ≈ p
    ≈-sym {p = p} {q = q} eq c = ⇄-flip (eq c)

    ≈-trans : {n : ℕ} {p q r : QH n} → p ≈ q → q ≈ r → p ≈ r
    ≈-trans eq₁ eq₂ c = (eq₁ c) ⇄⇄ (eq₂ c)

    -- The rules of passage qualify.

    SP-≈ : {n : ℕ} {p₁ p₂ : QH n} → (SP p₁ p₂) → p₁ ≈ p₂
    SP-≈ (at {m} c pass) c' = passage {m} (c' ◂-Somewhere (at c pass)) :⇄: passage {m} (c' ◂-Somewhere (at c (vice-versa pass)))

    SP⋆-≈ : {n : ℕ} {Φ₁ Φ₂ : QH n} → SP⋆ Φ₁ Φ₂ → Φ₁ ≈ Φ₂
    SP⋆-≈ (refl⋆) = ≈-refl
    SP⋆-≈ (trans⋆ sp sps) = ≈-trans (SP-≈ sp) (SP⋆-≈ sps)

    -- It also respects a number of operations.

    _◂-≈_ : {n m : ℕ} {p₁ p₂ : QH m} (c : Context m n) → p₁ ≈ p₂ → (c ◂ p₁) ≈ (c ◂ p₂)
    _◂-≈_ {p₁ = p₁} {p₂ = p₂} c eq c' = subst₂ (λ x₁ x₂ → ⊢ x₁ ⇄ ⊢ x₂) (◂◂-works c' c p₁) (◂◂-works c' c p₂) (eq (c' ◂◂ c))

    ≈-~ : {n : ℕ} {p₁ p₂ : QH n} → p₁ ≈ p₂ → ~ p₁ ≈ ~ p₂
    ≈-~ eq = (∙ ~∙) ◂-≈ eq

    ≈-[+] : {n : ℕ} {p₁ p₂ : QH (suc n)} → p₁ ≈ p₂ → [+] p₁ ≈ [+] p₂
    ≈-[+] eq = (∙ [+]∙) ◂-≈ eq

    ≈-[-] : {n : ℕ} {p₁ p₂ : QH (suc n)} → p₁ ≈ p₂ → [-] p₁ ≈ [-] p₂
    ≈-[-] eq = (∙ [-]∙) ◂-≈ eq
  open Equiv public


  module ξ-stuff where
    ξ-elem : {n : ℕ} → (i : ℕ) → (p : QH n) → elementary p → elementary (ξ i p)
    ξ-elem i (atom a) _ = tt
    ξ-elem i (~ p) e = ξ-elem i p e
    ξ-elem i (p₁ ∪ p₂) e = Data.Product.map (ξ-elem i p₁) (ξ-elem i p₂) e
    ξ-elem _ ([+] p) ()
    ξ-elem _ ([-] p) ()

    -- I can't believe this worked out of the box.
    ξ-comm : {n : ℕ} → (k i : ℕ) → (p : QH n) → ξ k (ξ (k + i) p) ≡ ξ (suc (k + i)) (ξ k p)
    ξ-comm k i (atom a) = cong atom (Atomic.ξ-comm atomic k i a)
    ξ-comm k i (~ p) = cong ~_ (ξ-comm k i p)
    ξ-comm k i (p₁ ∪ p₂) = cong₂ _∪_ (ξ-comm k i p₁) (ξ-comm k i p₂)
    ξ-comm k i ([+] p) = cong [+]_ (ξ-comm (suc k) i p)
    ξ-comm k i ([-] p) = cong [-]_ (ξ-comm (suc k) i p)

    ξ-◂ : {m n : ℕ} → ℕ → Context m n → Context (suc m) (suc n)
    ξ-◂ i ∙ = ∙
    ξ-◂ i (c ~∙) = (ξ-◂ i c) ~∙
    ξ-◂ i (c ⟨∙∪ p ⟩) = (ξ-◂ i c) ⟨∙∪ (ξ ((◂-depth c) + i) p) ⟩
    ξ-◂ i (c ⟨ p ∪∙⟩) = (ξ-◂ i c) ⟨ (ξ ((◂-depth c) + i) p) ∪∙⟩
    ξ-◂ i (c [+]∙) = (ξ-◂ i c) [+]∙
    ξ-◂ i (c [-]∙) = (ξ-◂ i c) [-]∙

    ξ-◂-works : {m n : ℕ} (i : ℕ) (c : Context m n) → (Φ : QH m) → (ξ-◂ i c) ◂ (ξ ((◂-depth c) + i) Φ) ≡ ξ i (c ◂ Φ)
    ξ-◂-works i ∙ Φ = refl
    ξ-◂-works i (c ~∙) Φ = (ξ-◂-works i c (~ Φ))
    ξ-◂-works i (c ⟨∙∪ p ⟩) Φ = ξ-◂-works i c (Φ ∪ p)
    ξ-◂-works i (c ⟨ p ∪∙⟩) Φ = ξ-◂-works i c (p ∪ Φ)
    ξ-◂-works i (c [+]∙) Φ = ξ-◂-works i c ([+] Φ)
    ξ-◂-works i (c [-]∙) Φ = ξ-◂-works i c ([-] Φ)

    
    -- ξ and Passage get along.
    ξ-passage : {n : ℕ} {Φ₁ Φ₂ : QH n} → (i : ℕ) → Passage Φ₁ Φ₂ → Passage (ξ i Φ₁) (ξ i Φ₂)
    ξ-passage i pass₁ = pass₁
    ξ-passage i pass₂ = pass₂
    ξ-passage i (pass₃ {n} {Φ} {p}) = subst (λ x → Passage ([+] ξ (suc i) Φ ∪ ξ i p) ([+] (ξ (suc i) Φ ∪ x))) (ξ-comm zero i p) (pass₃ {suc n} {ξ (suc i) Φ} {ξ i p})
    ξ-passage i (pass₄ {n} {Φ} {p}) = subst (λ x → Passage (ξ i p ∪ [+] ξ (suc i) Φ) ([+] (x ∪ ξ (suc i) Φ))) (ξ-comm zero i p) (pass₄ {suc n} {ξ (suc i) Φ} {ξ i p})
    ξ-passage i (pass₅ {n} {Φ} {p}) = subst (λ x → Passage ([-] ξ (suc i) Φ ∪ ξ i p) ([-] (ξ (suc i) Φ ∪ x))) (ξ-comm zero i p) (pass₅ {suc n} {ξ (suc i) Φ} {ξ i p})
    ξ-passage i (pass₆ {n} {Φ} {p}) = subst (λ x → Passage (ξ i p ∪ [-] ξ (suc i) Φ) ([-] (x ∪ ξ (suc i) Φ))) (ξ-comm zero i p) (pass₆ {suc n} {ξ (suc i) Φ} {ξ i p})
    ξ-passage i (vice-versa pass) = vice-versa (ξ-passage i pass)

    -- ξ and Somewhere Passage get along.
    -- Hur funkar det: ξ the context (via ξ-◂), ξ the parts related by passage (via ξ-passage), then show that this is equivalent to ξ on the whole thing.
    ξ-somewhere-passage : {n : ℕ} {Φ₁ Φ₂ : QH n} → (i : ℕ) → Somewhere Passage Φ₁ Φ₂ → Somewhere Passage (ξ i Φ₁) (ξ i Φ₂)
    ξ-somewhere-passage i (at {_} {Φ₁'} {Φ₂'} c pass) = subst₂ (Somewhere Passage) (ξ-◂-works i c Φ₁') (ξ-◂-works i c Φ₂') (at (ξ-◂ i c) (ξ-passage (◂-depth c + i) pass))
    
  open ξ-stuff public



  module PrenexMod where

    data Prenex : {n : ℕ} → QH n → Set₁ where
      M : {n : ℕ} → (p : QH n) → elementary p → Prenex p
      [+]_ : {n : ℕ} → {p : QH (suc n)} → Prenex p → Prenex ([+] p)
      [-]_ : {n : ℕ} → {p : QH (suc n)} → Prenex p → Prenex ([-] p)
      via-pass : {n : ℕ} {p q : QH n} → Somewhere {n} Passage p q → Prenex q → Prenex p

    interpret-prenex : {n : ℕ} {p : QH n} → Prenex p → QH n
    interpret-prenex (M p _) = p
    interpret-prenex ([+] pre) = [+] (interpret-prenex pre)
    interpret-prenex ([-] pre) = [-] (interpret-prenex pre)
    interpret-prenex (via-pass _ pre) = interpret-prenex pre

    prenex-passages : {n : ℕ} {p : QH n} (pre : Prenex p) → SP⋆ (interpret-prenex pre) p
    prenex-passages (M p _) = refl⋆
    prenex-passages ([+] pre) = (∙ [+]∙) ◂-Somewhere⋆ (prenex-passages pre)
    prenex-passages ([-] pre) = (∙ [-]∙) ◂-Somewhere⋆ (prenex-passages pre)
    prenex-passages (via-pass sp pre) = trans⋆′ (prenex-passages pre) (SP-sym sp)

    prenex-correct : {n : ℕ} {p : QH n} (pre : Prenex p) → (interpret-prenex pre) ≈ p
    prenex-correct pre = SP⋆-≈ (prenex-passages pre)
    
{-
    -- The old, "direct" way
    prenex-correct : {n : ℕ} {p : QH n} (pre : Prenex p) → (interpret-prenex pre) ≈ p
    prenex-correct (M p _) = ≈-refl
    prenex-correct ([+] pre) = ≈-[+] (prenex-correct pre)
    prenex-correct ([-] pre) = ≈-[-] (prenex-correct pre)
    prenex-correct (via-pass sp pre) = ≈-trans (prenex-correct pre) (≈-sym (SP-≈ sp))
-}    

    negate-prenex : {n : ℕ} → {p : QH n} → Prenex p → Prenex (~ p)
    negate-prenex (M p e) = M (~ p) e
    negate-prenex ([+] pre) = via-pass (at ∙ pass₁) ([-] negate-prenex pre)
    negate-prenex ([-] pre) = via-pass (at ∙ pass₂) ([+] negate-prenex pre)
    negate-prenex (via-pass sp pre) = via-pass ((∙ ~∙) ◂-Somewhere sp) (negate-prenex pre)

    ξ-prenex : {n : ℕ} → {p : QH n} → (i : ℕ) → Prenex p → Prenex (ξ i p)
    ξ-prenex i (M p e) = M (ξ i p) (ξ-elem i p e)
    ξ-prenex i ([+] pre) = [+] (ξ-prenex (suc i) pre)
    ξ-prenex i ([-] pre) = [-] (ξ-prenex (suc i) pre)
    ξ-prenex i (via-pass sp pre) = via-pass (ξ-somewhere-passage i sp) (ξ-prenex i pre)

    or-right : {n : ℕ} → {p₂ : QH n} → (p₁ : QH n) → elementary p₁ → Prenex p₂ → Prenex (p₁ ∪ p₂)
    or-right p₁ e₁ (M p₂ e₂) = M (p₁ ∪ p₂) (e₁ , e₂)
    or-right p₁ e₁ ([+] pre₂) = via-pass (at ∙ pass₄) ([+] (or-right (ξ₀ p₁) (ξ-elem zero p₁ e₁) pre₂))
    or-right p₁ e₁ ([-] pre₂) = via-pass (at ∙ pass₆) ([-] (or-right (ξ₀ p₁) (ξ-elem zero p₁ e₁) pre₂))
    or-right p₁ e₁ (via-pass sp pre₂) = via-pass ((∙ ⟨ _ ∪∙⟩) ◂-Somewhere sp) (or-right p₁ e₁ pre₂)

    or-prenex : {n : ℕ} → {p₁ p₂ : QH n} → Prenex p₁ → Prenex p₂ → Prenex (p₁ ∪ p₂)
    or-prenex (M p₁ e₁)       pre₂ = or-right p₁ e₁ pre₂
    or-prenex ([+] pre₁)      pre₂ = via-pass (at ∙ pass₃) ([+] (or-prenex pre₁ (ξ-prenex zero pre₂)))
    or-prenex ([-] pre₁)      pre₂ = via-pass (at ∙ pass₅) ([-] (or-prenex pre₁ (ξ-prenex zero pre₂)))
    or-prenex (via-pass sp pre₁) pre₂ = via-pass ((∙ ⟨∙∪ _ ⟩) ◂-Somewhere sp) (or-prenex pre₁ pre₂)
    
    prenex : {n : ℕ} → (p : QH n) → Prenex p
    prenex (atom a) = M (atom a) tt
    prenex (~ p) = negate-prenex (prenex p)
    prenex (p₁ ∪ p₂) = or-prenex (prenex p₁) (prenex p₂)
    prenex ([+] p) = [+] (prenex p)
    prenex ([-] p) = [-] (prenex p)

  open PrenexMod public 

{-
  If pf is an identity of the first kind, we can prove ⊢ interpret pf args as long as all args are elementary.

Purpose of thm 4.1?

Via fromFK we can prove that replacing the atoms of a true FK with *elementary* QH0 is ok.
Want to substitute it with arbitrary QH0 (well, prenex form).
If no more than one positive and one negative instance of each, we can stuff in a [+ x ] or [- x ].

Wait, why can't I just bubble out all quantifiers? ξ?
-}
  module Theorem4-1 where
    open Atomic atomic using (Atom ; X)
    open import Data.Fin hiding (raise)
    open import Data.Fin.Properties using (_≟_)
    open import Data.Vec
    open import Data.Empty
    open import Data.Sum
    open import Relation.Nullary
    open import Relation.Nullary.Decidable
    open import Relation.Nullary.Sum

    data Atom41 (n : ℕ) : Set where
      elem : (p : QH0) → elementary p → Atom41 n
      arg : Fin n → Atom41 n

    PF41 : ℕ → Set
    PF41 n = FK (Atom41 n)

    -- At least one positive occurrence.
    _∈₊_ : {n : ℕ} (i : Fin n) → PF41 n → Set

    -- At least one negative occurrence.
    _∈₋_ : {n : ℕ} (i : Fin n) → PF41 n → Set
    
    i ∈₊ (atom (elem _ _)) = ⊥
    i ∈₊ (atom (arg j)) = i ≡ j
    i ∈₊ (~ p) = i ∈₋ p
    i ∈₊ (p₁ ∪ p₂) = (i ∈₊ p₁) ⊎ (i ∈₊ p₂)
    
    i ∈₋ (atom _) = ⊥
    i ∈₋ (~ p) = i ∈₊ p
    i ∈₋ (p₁ ∪ p₂) = (i ∈₋ p₁) ⊎ (i ∈₋ p₂)

    -- At least one positive occurrence.
    _∈₊?_ : {n : ℕ} (i : Fin n) → (pf : PF41 n) → Dec (i ∈₊ pf)

    -- At least one negative occurrence.
    _∈₋?_ : {n : ℕ} (i : Fin n) → (pf : PF41 n) → Dec (i ∈₋ pf)
    
    i ∈₊? (atom (elem _ _)) = no (λ ())
    i ∈₊? (atom (arg j)) = i ≟ j
    i ∈₊? (~ p) = i ∈₋? p
    i ∈₊? (p₁ ∪ p₂) = (i ∈₊? p₁) ⊎-dec (i ∈₊? p₂)
    
    i ∈₋? (atom _) = no (λ ())
    i ∈₋? (~ p) = i ∈₊? p
    i ∈₋? (p₁ ∪ p₂) = (i ∈₋? p₁) ⊎-dec (i ∈₋? p₂)

    data Friendly {n : ℕ} (i : Fin n) : PF41 n → Set where
      fratom : (a : Atom41 n) → Friendly i (atom a)
      frneg : {p : _} → Friendly i p → Friendly i (~ p)
      fror : {p₁ p₂ : _} → Friendly i p₁ → Friendly i p₂ →
        ¬ (i ∈₊ p₁ × i ∈₊ p₂) →
        ¬ (i ∈₋ p₁ × i ∈₋ p₂) →
        Friendly i (p₁ ∪ p₂)

    data [?]-order : Set where
      [+-] : [?]-order
      [-+] : [?]-order

    swap : [?]-order → [?]-order
    swap [+-] = [-+]
    swap [-+] = [+-]
{-
    [?] : {n : ℕ} → [?]-order → (t t' : X) → (pf : PF41 (suc n)) → Bool → Bool → QH0 → QH0
    [?] [+-] t t' pf true  true  q = [+ t ] [- t' ] q
    [?] [-+] t t' pf true  true  q = [- t ] [+ t' ] q
    [?] _    t t' pf true  false q = [+ t ] q
    [?] _    t t' pf false true  q = [- t' ] q
    [?] _    t t' pf false false q = q
-}

    [?] : {n : ℕ} → [?]-order → (t t' : X) → (pf : PF41 (suc n)) → QH0 → QH0
    [?] ord t t' pf q with ord | ⌊ zero ∈₊? pf ⌋ | ⌊ zero ∈₋? pf ⌋
    ... | [+-] | true | true = [+ t ] [- t' ] q
    ... | [-+] | true | true = [- t' ] [+ t ] q
    ... | _ | true  | false = [+ t ] q
    ... | _ | false | true  = [- t' ] q
    ... | _ | false | false = q


--    [?] ord ~ pf = ~ [?] (swap ord) 
    [?]~ : {n : ℕ} → (ord : [?]-order) → (t t' : X) → (pf : PF41 (suc n)) → (q : QH0) → ~ ([?] (swap ord) t' t pf q) ≈ [?] ord t t' (~ pf) (~ q)
    [?]~ ord t t' pf q with ord | ⌊ zero ∈₊? pf ⌋ | ⌊ zero ∈₋? pf ⌋
    ... | [+-] | true  | true  = ≈-trans (SP-≈ (at ∙ pass₂)) ((SP-≈ (at (∙ [+]∙) pass₁)))
    ... | [-+] | true  | true  = ≈-trans (SP-≈ (at ∙ pass₁)) ((SP-≈ (at (∙ [-]∙) pass₂)))
    ... | [+-] | true  | false = SP-≈ (at ∙ pass₁)
    ... | [-+] | true  | false = SP-≈ (at ∙ pass₁)
    ... | [+-] | false | true  = SP-≈ (at ∙ pass₂)
    ... | [-+] | false | true  = SP-≈ (at ∙ pass₂)
    ... | [+-] | false | false = ≈-refl
    ... | [-+] | false | false = ≈-refl

{-
    [?]₊ : {n : ℕ} → (t t' : X) → (pf : PF41 (suc n)) → Dec (zero ∈₊ pf) → Dec (zero ∈₋ pf) → QH0 → QH0
    [?]₊ t t' pf (yes _) (yes _) q = [+ t ] [- t' ] q
    [?]₊ t t' pf (yes _) (no _)  q = [+ t ] q
    [?]₊ t t' pf (no _)  (yes _) q = [- t' ] q
    [?]₊ t t' pf (no _)  (no _)  q = q

    [?]₋ : {n : ℕ} → (t t' : X) → (pf : PF41 (suc n)) → Dec (zero ∈₊ pf) → Dec (zero ∈₋ pf) → QH0 → QH0
    [?]₋ t t' pf (yes _) (yes _) q = [- t ] [+ t' ] q
    [?]₋ t t' pf (yes _) (no _)  q = [- t ] q
    [?]₋ t t' pf (no _)  (yes _) q = [+ t' ] q
    [?]₋ t t' pf (no _)  (no _)  q = q
-}
{-
    ~[?]₊ : {n : ℕ} → (t t' : X) → (pf : PF41 (suc n)) →
      (0∈₊ : Dec (zero ∈₊ pf)) → (0∈₋ : Dec (zero ∈₋ pf)) →
      (q : QH0) →
      ~ ([?]₋ t t' 0∈₊ 0∈₋ q) ≈ ([?]₊ t t' 0∈₋ 0∈₊ (~ q))

    ~[?]₊ : {n : ℕ} → (t t' : X) → (pf : PF41 (suc n)) →
      (0∈₊ : Dec (zero ∈₊ pf)) → (0∈₋ : Dec (zero ∈₋ pf)) →
      (q : QH0) →
      ~ ([?]₊ t t' 0∈₊ 0∈₋ q) ≈ 
-}

    apply : {n : ℕ} → PF41 n → Vec QH0 n → QH0
    apply (atom (arg i)) as = lookup i as
    apply (atom (elem q _)) _ = q
    apply (~ pf) as = ~ apply pf as
    apply (pf₁ ∪ pf₂) as = (apply pf₁ as) ∪ (apply pf₂ as)

    bubble[+] : {n : ℕ} → (order : [?]-order) → (pf : PF41 (suc n)) → (a : QH0) → (as : Vec QH0 n) →
      (t t' : X) → t ∉ (apply pf (a ∷ as)) → t' ∉ (apply pf (a ∷ as)) →
      Friendly zero pf →
      (apply pf (([+ t ] a) ∷ as)) ≈ ([?] order t t' pf (apply pf (a ∷ as)))
    bubble[+] {n = zero} [+-] (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble[+] {n = zero} [-+] (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble[+] {n = zero} _(atom (arg (suc ()))) a as t t' _ _ _
    bubble[+] {n = suc n} [+-] (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble[+] {n = suc n} [-+] (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble[+] {n = suc n} [+-] (atom (arg (suc i))) a as t t' _ _ _ = ≈-refl
    bubble[+] {n = suc n} [-+] (atom (arg (suc i))) a as t t' _ _ _ = ≈-refl
    bubble[+] [+-] (atom (elem q _)) a as t t' _ _ _ = ≈-refl
    bubble[+] [-+] (atom (elem q _)) a as t t' _ _ _ = ≈-refl
    bubble[+] [+-] (~ pf) a as t t' t∉ t'∉ (frneg f) = {!!}
    bubble[+] [-+] (~ pf) a as t t' t∉ t'∉ (frneg f) = {!!}
    bubble[+] [+-] (pf₁ ∪ pf₂) a as t t' t∉ t'∉ (fror f₁ f₂ nand₊ nand₋) = {!!}
    bubble[+] [-+] (pf₁ ∪ pf₂) a as t t' t∉ t'∉ (fror f₁ f₂ nand₊ nand₋) = {!!}
    
{-
  have   (≈-~ (bubble[+] [-+] pf a as t t' t∉ t'∉ f))
       : ~ (apply pf (([+ t ] a) ∷ as)) ≈ ~ ([?] [-+] t t' pf (apply pf (a ∷ as)))

  want : (apply (~ pf) (([+ t ] a) ∷ as)) ≈ [?] [+-] t t' (~ pf) (apply (~ pf) (a ∷ as))
       = ~ (apply pf (([+ t ] a) ∷ as)) ≈ [?] [+-] t t' (~ pf) (~ (apply pf (a ∷ as)))
-}
{-
    bubble₋ : {n : ℕ} → (pf : PF41 (suc n)) → (a : QH0) → (as : Vec QH0 n) →
      (t t' : X) → t ∉ (apply pf (a ∷ as)) → t' ∉ (apply pf (a ∷ as)) →
      Friendly zero pf →
      (apply pf (([- t ] a) ∷ as)) ≈ ([?]₋ t t' pf (zero ∈₊? pf) (zero ∈₋? pf) (apply pf (a ∷ as)))


   

    bubble₋ {n = zero} (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble₋ {n = zero} (atom (arg (suc ()))) a as t t' _ _ _
    bubble₋ {n = suc n} (atom (arg zero)) a as t t' _ _ _ = ≈-refl
    bubble₋ {n = suc n} (atom (arg (suc i))) a as t t' _ _ _ = ≈-refl
    bubble₋ (atom (elem q _)) a as t t' _ _ _ = ≈-refl
    bubble₋ (~ pf) a as t t' t∉ t'∉ (frneg f) = {!!}
    bubble₋ (pf₁ ∪ pf₂) a as t t' t∉ t'∉ (fror f₁ f₂ nand₊ nand₋) = {!!}
-}    
    {-
    add-[+] : {n : ℕ} → (pf : PF41 (suc n)) → ⊢ interpret pf (a ∷ as) → ⊢ interpret pf (([+ x ] a) ∷ as)
    add-[+] = ?
    
    add-[-] : {n : ℕ} → (pf : PF41 (suc n)) → ⊢ interpret pf (a ∷ as) → ⊢ interpret pf (([- x ] a) ∷ as)
    add-[-] = ?
    -}
  {-
    -- elim₀ : 

    
    --elim₀ : {n : ℕ} → (pf : PF41 (suc n)) → 
-}
  open Theorem4-1 public
