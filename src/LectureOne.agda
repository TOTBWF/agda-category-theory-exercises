module LectureOne where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function

-- These are the exercises for my first "pseudolecture" on category theory.
-- We are going to be using agda for the exercises, as I find it provides
-- really nice feedback on whether or not you are on the right track.
-- However, I will not be giving an introduction to agda, as Philip Wadler
-- has done a much better job than I could ever hope to!
-- The first few parts of Section 1 of 'Programming Language Foundations in Agda'
-- form an excellent introduction to the language. It can be found at:
-- https://plfa.github.io/#part-1-logical-foundations

record Monoid (A : Set) : Set₁ where
  field
    _∙_ : A → A → A
    ε : A

  infixr 5 _∙_

  field
    -- Now, onto the monoid laws!
    assoc : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    identityˡ : ∀ {x} → ε ∙ x ≡ x
    identityʳ : ∀ {x} → x ∙ ε ≡ x

-- Exercise 1 (*): Prove that '0' is the right-identity to +
+-monoid : Monoid ℕ
+-monoid = record
  { _∙_ = _+_
  ; ε = 0
  ; assoc = λ {x y z} → assoc x y z
  ; identityˡ = λ {x} → identityˡ x
  ; identityʳ = λ {x} → identityʳ x
  }
  where
    assoc : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
    assoc zero y z = refl
    assoc (suc x) y z =  cong suc (assoc x y z)

    identityˡ : ∀ (x : ℕ) → 0 + x ≡ x
    identityˡ x = refl

    -- HINT: 'cong' lets us take a proof that 'x ≡ y', and show that 'f x ≡ f y'
    identityʳ : ∀ (x : ℕ) → x + 0 ≡ x
    identityʳ x = {!!}

-- Exercise 2 (**): Prove that lists form a monoid under '++' and '[]'
++-monoid : (A : Set) → Monoid (List A)
++-monoid A = record
  { _∙_ = _++_
  ; ε = []
  ; assoc = λ {x y z} → assoc x y z
  ; identityˡ = λ {x} → identityˡ x
  ; identityʳ = λ {x} → identityʳ x
  }
  where
    assoc : ∀ (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    assoc xs yz zs = {!!}

    identityˡ : ∀ (xs : List A) → [] ++ xs ≡ xs
    identityˡ xs = {!!}

    identityʳ : ∀ (xs : List A) → xs ++ [] ≡ xs
    identityʳ xs = {!!}

-- Note: So far, we have been using Agda's "propositional equality", which states that
-- two things are equal when they are /literally/ the same term. This works great for things
-- like ℕ, List, Bool, etc, but is a bit too strong when dealing with functions.
--
-- There are ways around this, and we will get to them later, but for now, let's simply
-- postulate that two functions are equal if we can show that they return the same value
-- for every possible input.
postulate fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → (f x ≡ g x)) → f ≡ g

-- Functions form a monoid under composition
∘-monoid : (A : Set) → Monoid (A → A)
∘-monoid A = record
  { _∙_ = λ f g → f ∘ g
  ; ε = id
  ; assoc = λ {f g h} → fun-ext λ x → refl
  ; identityˡ = λ {f} → fun-ext λ x → refl
  ; identityʳ = λ {f}  → fun-ext λ x → refl
  }

record MonoidHomomorphism {A B : Set} (M : Monoid A) (N : Monoid B) : Set₁ where
  private
    module M = Monoid M
    module N = Monoid N
    open M using () renaming (_∙_ to _∙₁_; ε to ε₁)
    open N using () renaming (_∙_ to _∙₂_; ε to ε₂)
  field
    ⟦_⟧ : A → B
    ⟦⟧-cong : ∀ {x y} → x ≡ y → ⟦ x ⟧ ≡ ⟦ y ⟧
    ∙-homo : ∀ {x y} → ⟦ x ∙₁ y ⟧ ≡ (⟦ x ⟧ ∙₂ ⟦ y ⟧)
    ε-homo : ⟦ ε₁ ⟧ ≡ ε₂

open MonoidHomomorphism using (⟦_⟧)

-- Exercise 3 (*): Show that length is a homomorphism
length-homo : (A : Set) → MonoidHomomorphism (++-monoid A) +-monoid
length-homo A = record
  { ⟦_⟧ = length
  ; ⟦⟧-cong = λ eq → cong length eq
  ; ∙-homo = λ {xs ys} → ∙-homo xs ys
  ; ε-homo = ε-homo
  }
  where

    ∙-homo : ∀ (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
    ∙-homo xs ys = {!!}

    ε-homo : length {A = A} [] ≡ 0
    ε-homo = {!!}


-- Exercise 4 (***): Show that we have a homomorphisms from
-- any monoid on 'A' to the monoid of functions 'A → A'
-- HINT: use 'fun-ext'
cayley : ∀ {A} (M : Monoid A) → MonoidHomomorphism M (∘-monoid A)
cayley M = record
  { ⟦_⟧ = λ x → x ∙_
  ; ⟦⟧-cong = λ {x y} x≈y → fun-ext λ z → cong₂ _∙_ x≈y refl
  ; ∙-homo = λ {x y} → fun-ext λ z → assoc
  ; ε-homo = fun-ext (λ _ → identityˡ)
  }
  where
    open Monoid M

-- Exercise 5 (***): Show that the homomorphism we have
-- just defined is *injective*. As a reminder, means that it never maps
-- two elements of the domain to the same element in the codomain.
-- HINT: use 'cong-app' and 'trans'
cayley-inj : ∀ {A : Set} {x y : A} (M : Monoid A) → ⟦ cayley M ⟧ x ≡ ⟦ cayley M ⟧ y → x ≡ y
cayley-inj M eq = {!!}
  where open Monoid M
