module Common where

  open import Agda.Primitive
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties using (≤-step)
  open import Data.Nat.Properties.Simple using (+-comm)
  open import Data.Fin hiding (_≤_ ; _+_)
  open import Data.Vec using (Vec ; _∷_ ; [])
  open import Function using (_∘_) public
  open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂) public
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′) public
  open import Data.Empty using (⊥ ; ⊥-elim) public
  open import Data.Unit using (⊤ ; tt) public
  open import Relation.Nullary public
  open import Relation.Nullary.Negation public
  open import Relation.Nullary.Decidable hiding (map) public
  open import Relation.Nullary.Sum public
  open import Relation.Binary.PropositionalEquality hiding ([_]) public

  relaxFin : {n : ℕ} → Fin n → Fin (suc n)
  relaxFin zero = zero
  relaxFin (suc m) = suc (relaxFin m)

  toℕ-relaxFin : {n : ℕ} → (i : Fin n) → toℕ (relaxFin i) ≡ toℕ i
  toℕ-relaxFin zero = refl
  toℕ-relaxFin (suc m) = cong suc (toℕ-relaxFin m)

  ≤-relax : {n : ℕ} → {i : ℕ} → {a : Fin n}
    → i ≤ toℕ a
    → i ≤ toℕ (relaxFin a)
  ≤-relax {i = i} {a = a} = subst (λ x → i ≤ x) (sym (toℕ-relaxFin a))

  ≰-relax : {n : ℕ} → {i : ℕ} → {a : Fin n}
    → i ≰ toℕ a
    → i ≰ toℕ (relaxFin a)
  ≰-relax {i = i} {a = a} = subst (λ x → i ≰ x) (sym (toℕ-relaxFin a))

  a+b≤c⇒b≤c : (a b c : ℕ) → a + b ≤ c → b ≤ c
  a+b≤c⇒b≤c zero zero zero _ = z≤n
  a+b≤c⇒b≤c zero (suc b) zero ()
  a+b≤c⇒b≤c (suc a) b zero ()
  a+b≤c⇒b≤c zero b (suc c) le = le
  a+b≤c⇒b≤c (suc a) b (suc c) (s≤s le) = ≤-step (a+b≤c⇒b≤c a b c le)

  a+b≤c⇒a≤c : (a b c : ℕ) → a + b ≤ c → a ≤ c
  a+b≤c⇒a≤c a b c le = a+b≤c⇒b≤c b a c (subst (λ x → x ≤ c) (+-comm a b) le)

  ¬¬-intro : ∀{α} {P : Set α} → P → ¬ ¬ P
  ¬¬-intro p ¬p = ¬p p

  ¬₃ : ∀{α} {P : Set α} → ¬ ¬ ¬ P → ¬ P
  ¬₃ ¬¬¬p = ¬¬¬p ∘ ¬¬-intro

  ¬¬× : ∀{α} {A B : Set α}
    → ¬ ¬ (A × B)
    → (¬ ¬ A) × (¬ ¬ B)
  ¬¬× p = (λ ¬a → p (¬a ∘ proj₁)) , (λ ¬b → p (¬b ∘ proj₂))

  -- insert (suc i) case broken into cases to appease the case-coverage checker.
  {-
  insert : ∀{α} {n : ℕ} {A : Set α} → Fin (suc n) → A → Vec A n → Vec A (suc n)
  insert zero a₀ as = a₀ ∷ as
  insert (suc zero) a₀ (a ∷ as) = a ∷ (insert zero a₀ as)
  insert (suc (suc i)) a₀ (a ∷ as) = a ∷ (insert (suc i) a₀ as)
  -}
{-

  relaxFin-toℕ : {n : ℕ} → (m : Fin n) → (toℕ m ≡ toℕ (relaxFin m))
  relaxFin-toℕ zero = refl
  relaxFin-toℕ (suc m) = cong suc (relaxFin-toℕ m)

  flop : ∀{α} {T T' : Set α} → T ≡ T' → T → T'
  flop refl = id

  ¬2 : ∀{α} {P : Set α} → P → ¬ ¬ P
  ¬2 p ¬p = ¬p p
  
  
  ¬¬→ : ∀{α β} {A : Set α} {B : Set β} → (A → B) → (¬ ¬ A) → (¬ ¬ B)
  ¬¬→ f ¬¬a = λ ¬b → ¬¬a (λ a → ¬b (f a))
  
--  ¬¬sym : ∀{α} {A : Set α} (x y : A) → ¬ ¬ (x ≡ y) → ¬ ¬ (y ≡ x)
--  ¬¬sym
  
  
-}


-- Transitive-reflexive closure
  data _⋆ {α β : Level} {A : Set α} (R : A → A → Set β) : A → A → Set (α ⊔ β) where
    refl⋆ : {a : A} → (R ⋆) a a
    trans⋆ : {a₀ a₁ a₂ : A} → R a₀ a₁ → (R ⋆) a₁ a₂ → (R ⋆) a₀ a₂

  -- snoc
  trans⋆′ : {α β : Level} {A : Set α} {R : A → A → Set β} {a₀ a₁ a₂ : A}
    → (R ⋆) a₀ a₁ → R a₁ a₂ → (R ⋆) a₀ a₂
  trans⋆′ refl⋆ r = trans⋆ r refl⋆
  trans⋆′ (trans⋆ r rs) r' = trans⋆ r (trans⋆′ rs r')

-- Symmetric relationships
  symmetric : {α β : Level} {A : Set α} (R : A → A → Set β) → Set _
  symmetric {A = A} R = {a₁ a₂ : A} → R a₁ a₂ → R a₂ a₁

  symmetric⋆ : {α β : Level} {A : Set α} {R : A → A → Set β} → symmetric R → symmetric (R ⋆)
  symmetric⋆ symm refl⋆ = refl⋆
  symmetric⋆ symm (trans⋆ r rs) = trans⋆′ (symmetric⋆ symm rs) (symm r)


  infix 4 _⇄_
  infix 5 _:⇄:_
  record _⇄_ {α β : Level} (From : Set α) (To : Set β) : Set (α ⊔ β) where
    constructor _:⇄:_
    field
      fwd : From → To
      bck : To → From
  open _⇄_ public
  
  infixr 9 _⇄⇄_
  _⇄⇄_ : ∀{α β γ} {A : Set α} {B : Set β} {C : Set γ}
    → A ⇄ B → B ⇄ C → A ⇄ C
  f ⇄⇄ g = fwd g ∘ fwd f :⇄: bck f ∘ bck g

  ¬⇄ : ∀{α β} {A : Set α} {B : Set β} → A ⇄ B → (¬ A) ⇄ (¬ B)
  ¬⇄ f = contraposition (bck f) :⇄: contraposition (fwd f)

  ⇄-flip : ∀{α β} {A : Set α} {B : Set β} → A ⇄ B → B ⇄ A
  ⇄-flip (f :⇄: b) = (b :⇄: f)

  _∘⇄∘_ : ∀{α β γ} {A : Set α} {B : Set β} {C : Set γ} → (C → A → B) → (C → B → A) → C → (A ⇄ B)
  (f ∘⇄∘ g) x = (f x) :⇄: (g x)

  infixr 2 _⇄×⇄_
  _⇄×⇄_ : ∀{α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
    → A ⇄ B
    → C ⇄ D
    → (A × C) ⇄ (B × D)
  f ⇄×⇄ g = (Data.Product.map (fwd f) (fwd g)) :⇄: (Data.Product.map (bck f) (bck g))

  -- Π : ∀{α β} (A : Set α) (B : A → Set β) → Set (α ⊔ β)
  -- Π A B = (a : A) → (B a)
  
  -- Π⇄ : ∀{α β} {A : Set α} {B₁ B₂ : A → Set β} → Π A (λ x → B₁ x ⇄ B₂ x) → Π A B₁ ⇄ Π A B₂
  -- Π⇄ h = (λ f → λ x → fwd (h x) (f x)) :⇄: (λ f → λ x → bck (h x) (f x))

  Π⇄ : ∀{α β} {A : Set α} {B₁ B₂ : A → Set β}
    → ((x : A) → B₁ x ⇄ B₂ x)
    → ((x : A) → B₁ x) ⇄ ((x : A) → B₂ x)
  Π⇄ h = (λ f → λ x → fwd (h x) (f x)) :⇄: (λ f → λ x → bck (h x) (f x))

{-
  Π≡ : ∀{α β} {A : Set α} {B₁ B₂ : A → Set β}
    → ((x : A) → B₁ x ≡ B₂ x)
    → ((x : A) → B₁ x) ≡ ((x : A) → B₂ x)
  Π≡ {A = A} eq = {!!}
-}

  {-
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
  -}

  module Functions where

    Injective : ∀{α β} {X : Set α} {Y : Set β} → (X → Y) → Set (α ⊔ β)
    Injective {X = X} {Y = Y} f = {x₁ x₂ : X} → (f x₁ ≡ f x₂) → (x₁ ≡ x₂)
    
    Surjective : ∀{α β} {X : Set α} {Y : Set β} → (X → Y) → Set (α ⊔ β)
    Surjective {X = X} {Y = Y} f = (y : Y) → Σ X (λ x → f x ≡ y)

    --pre : {X Y : Set} → (f : X → Y) → Surjective f → Y → X
    --pre f sur = proj₁ ∘ sur

    --pre-lemma : {X Y : Set} → (f : X → Y) → (s : Surjective f) → (y : Y) → f (pre s y) ≡ y
    --pre-lemma f sur y = proj₂ sur y

    -- bijection
    record _↔_ {α β : Level} (X : Set α) (Y : Set β) : Set (α ⊔ β) where
      field
        f : X → Y
        inj : Injective f
        sur : Surjective f

    -- injection
    record _↣_ {α β : Level} (X : Set α) (Y : Set β) : Set (α ⊔ β) where
      field
        f : X → Y
        inj : Injective f

    {-
    inverse : {X Y : Set} → X ↔ Y → Y ↔ X
    inverse bi = record
      { f = pre (_↔_.sur bi)
      ; inj = λ y₁ y₂ proof → {!!}
      ; sur = {!!}
      }
    -}

  open Functions public
{-
proof:
(proj₁ ∘ _↔_.sur bi) y₁ ≡
(proj₁ ∘ _↔_.sur bi) y₂

aka

pre (_↔_.sur bi) y₁ ≡ pre (_↔_.sur bi) y₂
-}
