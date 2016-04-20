module Common where

  open import Agda.Primitive
  open import Data.Bool
  open import Data.Unit
  open import Data.Empty
  open import Data.Nat
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Nullary.Negation
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  -- A property preserved by a unary operator.
  pres₁ : {A : Set} → (A → Set) → (A → A) → Set
  pres₁ {A} P f = {x : A} → P x → P (f x)

  -- A property preserved by a binary operator.
  pres₂ : {A : Set} → (A → Set) → (A → A → A) → Set
  pres₂ {A} P f = {x y : A} → P x → P y → P (f x y)

  module DecVec {α α' : Level} {ds : DecSetoid α α'} where

    open import Data.Vec hiding (_∈_)
    module DS = DecSetoid ds
    open DS

    _[_/_] : {n : ℕ} → Vec Carrier n → Carrier → Carrier → Vec Carrier n
    _[_/_] v y x = Data.Vec.map (λ z → if ⌊ (DS._≟_ z x) ⌋ then y else z) v

    _∈_ : {n : ℕ} → Carrier → Vec Carrier n → Set
    x ∈ [] = ⊥
    x ∈ (y ∷ ys) with DS._≟_ x y
    ... | yes _ = ⊤
    ... | no _ = x ∈ ys

    _∈?_ : {n : ℕ} → (x : Carrier) → (ys : Vec Carrier n) → Dec (x ∈ ys)
    x ∈? [] = no (λ ())
    x ∈? (y ∷ ys) with DS._≟_ x y
    ... | yes _ = yes tt
    ... | no _ = x ∈? ys

    _∉_ : {n : ℕ} → Carrier → Vec Carrier n → Set
    x ∉ ys = ¬ (x ∈ ys)

    _∉?_ : {n : ℕ} → (x : Carrier) → (ys : Vec Carrier n) → Dec (x ∉ ys)
    x ∉? ys = ¬? (x ∈? ys)

    --sub-∉ : {n : ℕ} → (x z : Carrier) → (ys : Vec Carrier n) → x ∉ ys → (ys [ z / x ]) ≡ ys
    --sub-∉ = {!!}


    
  {-
    _[_/_] : {α α' : Level} {ds : DecSetoid α α'} {n : ℕ} → Vec (Carrier ds) n → Carrier ds → Carrier ds → Vec (Carrier ds) n
    _[_/_] {ds = ds} v y x = Data.Vec.map (λ z → if ⌊ (DecSetoid._≟_ ds z x) ⌋ then y else z) v

    _∈_ : {α α' : Level} {ds : DecSetoid α α'} {n : ℕ} → Carrier ds → Vec (Carrier ds) n → Set
    x ∈ [] = ⊥
    _∈_ {ds = ds} x (y ∷ ys) with DecSetoid._≟_ ds x y
    ... | yes _ = ⊤
    ... | no _ = _∈_ {ds = ds} x ys


    _∈?_ : {α α' : Level} {ds : DecSetoid α α'} {n : ℕ} → (x : Carrier ds) → (ys : Vec (Carrier ds) n) → Dec (_∈_ {ds = ds} x ys)
    x ∈? [] = no (λ ())
    _∈?_ {ds = ds} x (y ∷ ys) with DecSetoid._≟_ ds x y
    ... | yes _ = yes tt
    ... | no _ = _∈?_ {ds = ds} x ys

    _∉_ : {α α' : Level} {ds : DecSetoid α α'} {n : ℕ} → Carrier ds → Vec (Carrier ds) n → Set
    _∉_ {ds = ds} x ys = ¬ (_∈_ {ds = ds} x ys)

    _∉?_ : {α α' : Level} {ds : DecSetoid α α'} {n : ℕ} → (x : Carrier ds) → (ys : Vec (Carrier ds) n) → Dec (_∉_ {ds = ds} x ys)
    _∉?_ {ds = ds} x ys = ¬? (x ∈? ys)
  -}
