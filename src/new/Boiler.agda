module Boiler where

  -- Begin boilerplate code (most in stdlib) --

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  data Vec (A : Set) : ℕ → Set where
    [] : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

  data ⊥ : Set where

  ¬_ : Set → Set
  ¬ x = x → ⊥

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  contradiction : {A B : Set} → A → ¬ A → B
  contradiction a ¬a = ⊥-elim (¬a a)

  contraposition : {A B : Set} → (A → B) → ¬ B → ¬ A
  contraposition f ¬b a = ¬b (f a)

  ¬¬-intro : {A : Set} → A → ¬ ¬ A
  ¬¬-intro a = λ ¬a → ¬a a

  id : {A : Set} → A → A
  id x = x

  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  g ∘ f = λ x → g (f x)
  infixr 10 _∘_

  module Sum where
    data _⊎_ (A : Set) (B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

    [_,_]′ : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B) → C
    [ f , g ]′ (inj₁ a) = f a
    [ f , g ]′ (inj₂ b) = g b

    map : {A B C D : Set} → (A → C) → (B → D) → (A ⊎ B) → (C ⊎ D)
    map f _ (inj₁ a) = inj₁ (f a)
    map _ g (inj₂ b) = inj₂ (g b)

  module Product where
    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,_
      field
        proj₁ : A
        proj₂ : B proj₁
    open Σ public

    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)

    map : {A C : Set} {B : A → Set} {D : C → Set} (f : A → C) (g : {a : A} → B a → D (f a)) → Σ A B → Σ C D
    map f g (a , b) = (f a , g b)


  --module List where

  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  [_] : {A : Set} → A → List A
  [ a ] = a ∷ []

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  concat : {A : Set} → List (List A) → List A
  concat [] = []
  concat (x ∷ xs) = x ++ (concat xs)

  open Sum public hiding (map)
  open Product public hiding (map)
  --open List public





  data Dec (A : Set) : Set where
    yes : A → Dec A
    no  : ¬ A → Dec A

  ¬? : {A : Set} → Dec A → Dec (¬ A)
  ¬? (yes a) = no (λ f → f a)
  ¬? (no ¬a) = yes ¬a

  _⊎?_ : {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
  (yes a) ⊎? _ = yes (inj₁ a)
  (no ¬a) ⊎? (yes b) = yes (inj₂ b)
  (no ¬a) ⊎? (no ¬b) = no [ ¬a , ¬b ]′

  _×?_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
  (yes a) ×? (yes b) = yes (a , b)
  (yes a) ×? (no ¬b) = no (¬b ∘ proj₂)
  (no ¬a) ×? _ = no (¬a ∘ proj₁)

  _⇒?_ : {A B : Set} → Dec A → Dec B → Dec (A → B)
  _       ⇒? (yes b) = yes (λ _ → b)
  (yes a) ⇒? (no ¬b) = no (λ f → ¬b (f a))
  (no ¬a) ⇒? (no ¬b) = yes (λ a → contradiction a ¬a)



  -- End of boilerplate code --
