module BigLEM where

{-
  We wish to investigate the possible sizes of function spaces `A → B`
  in the absence of extensionality principles.

  Concretely: given an inhabited type `B`, when can we have an injection
  from some type `C` to the function space `A → B`?

  In what follows we show that at least not all axioms of the form
    `biglem : (A B : Set) → (¬ B) ⊎ (C ↪ (A → B))`
  are consistent, where `C : Set`.

  In particular, ((⊤ → ⊤) → Bool) is already "too big" to be C.
  This is a Cantor diagonalization argument, using the fact that biglem
  implies LEM in an essential way. In particular, it doesn't seem to say
  anything about axioms of the form
    `big : (A B : Set) → B → C ↪ (A → B)`.
  Can you?
-}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

import Agda.Primitive

{-
  We define injections mostly so we can use ↪ as the syntax.
  In `Function.Bundle` the type `A ↪ B` stands for split monos instead.
-} 
record _↪_ {ℓ₁ ℓ₂ : _} (A : Set ℓ₁) (B : Set ℓ₂) : Set (Agda.Primitive._⊔_ ℓ₁ ℓ₂) where
  field
    app : A → B
    inj : ∀ x → ∀ y → app x ≡ app y → x ≡ y
open _↪_


{-
  We start with a classical version of Cantor's theorem, showing that
  there is no injection from 2^K to K. NB the usual version which
  proves that there is no surjection from K to 2^K goes through
  constructively, but this direction requires LEM. Why? Well, think
  about how in some constructive theories we have sets K that only
  have two decidable subsets, namely ∅ and K itself. So 2^K need not
  be very large at all.
-}
module Cantor
  (lem : ∀ (B : Set) → B ⊎ (B → ⊥))
  where

  _holds : Set → Bool
  K holds with lem K
  ... | inj₁ [K] = true
  ... | inj₂ [¬K] = false

  holds-t : ∀ (K : Set) → K → K holds ≡ true
  holds-t K [K] with lem K
  ... | inj₁ _ = refl
  ... | inj₂ [¬K] = ⊥-elim ([¬K] [K])

  holds-f : ∀ (K : Set) → (K → ⊥) → K holds ≡ false
  holds-f K [¬K] with lem K
  ... | inj₁ [K] = ⊥-elim ([¬K] [K]) 
  ... | inj₂ _ = refl

  cantor-inj : ∀ (K : Set) → ((K → Bool) ↪ K) → ⊥
  cantor-inj K assm = [¬R[fRh]] [R[fRh]] where
    f : (K → Bool) → K
    f = app assm
    R : K → Set
    R k = ∃ λ (P : K → Bool) → f P ≡ k × P k ≡ false
    Rh : K → Bool
    Rh k = R k holds
    [¬R[fRh]] : R (f Rh) → ⊥
    [¬R[fRh]] (P , fst , snd) = [f≠t] [f=t] where
      [P=Rh] : P ≡ Rh
      [P=Rh] = inj assm P Rh fst
      [P[fRh]=Rh[fRh]] : P (f Rh) ≡ Rh (f Rh)
      [P[fRh]=Rh[fRh]] = cong (λ z → z (f Rh)) [P=Rh]
      [Rh[fRh]=t] : Rh (f Rh) ≡ true
      [Rh[fRh]=t] = holds-t (R (f Rh)) (P , fst , snd)
      [P[fRh]=t] : P (f Rh) ≡ true
      [P[fRh]=t] = trans [P[fRh]=Rh[fRh]] [Rh[fRh]=t]
      [P[fRh]=f] : P (f Rh) ≡ false
      [P[fRh]=f] = snd
      [f=t] : false ≡ true
      [f=t] = trans (sym [P[fRh]=f]) [P[fRh]=t]
      [f≠t] : false ≡ true → ⊥
      [f≠t] ()
    [R[fRh]] : R (f Rh)
    [R[fRh]] = Rh , refl , holds-f (R (f Rh)) [¬R[fRh]]

{-
  The main result: if we set C to `(⊤ → ⊤) → Bool` in a biglem axiom,
  we can prove LEM, and then use Cantor's theorem to get a contradiction.
-}

module _
  (biglem : (A B : Set) → (B → ⊥) ⊎ (((⊤ → ⊤) → Bool) ↪ (A → B)))
  where

  lem : ∀ (B : Set) → B ⊎ (B → ⊥)
  lem B with biglem ⊤ B
  ... | inj₁ [¬B] = inj₂ [¬B]
  ... | inj₂ bb = inj₁ (app bb (λ _ → false) tt)

  open Cantor lem

  bad-injection : ((⊤ → ⊤) → Bool) ↪ (⊤ → ⊤)
  bad-injection with biglem ⊤ ⊤
  ... | inj₁ x = ⊥-elim (x tt)
  ... | inj₂ y = y

  contradiction : ⊥
  contradiction = cantor-inj (⊤ → ⊤) bad-injection
