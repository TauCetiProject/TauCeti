/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Canonical maps from principal localizations to localizations at primes

For a prime ideal `P` of a commutative semiring `R` and an element `f ∉ P`, every power of `f`
lies outside `P`, so the localization `Localization.Away f` maps canonically to
`Localization.AtPrime P`.

## Main definitions

* `Ideal.localizationAwayToAtPrime P f hf`: the canonical ring homomorphism
  `Localization.Away f →+* Localization.AtPrime P` for `f ∉ P`.

## Main results

* `Ideal.localizationAwayToAtPrime_algebraMap`: `P.localizationAwayToAtPrime f hf` sends the
  image of `r : R` in `Localization.Away f` to its image in `Localization.AtPrime P`.
* `Ideal.localizationAwayToAtPrime_comp_algebraMap`: composition with
  `algebraMap R (Localization.Away f)` is `algebraMap R (Localization.AtPrime P)`.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- For a prime ideal `P` of `R` and `f ∉ P`, the canonical ring homomorphism
`Localization.Away f →+* Localization.AtPrime P` extending `algebraMap R (Localization.AtPrime P)`.
-/
noncomputable def localizationAwayToAtPrime (P : Ideal R) [P.IsPrime] (f : R) (hf : f ∉ P) :
    Localization.Away f →+* Localization.AtPrime P :=
  IsLocalization.map (T := P.primeCompl) _ (RingHom.id R) (Submonoid.powers_le.mpr hf)

/-- On elements of `R`, `Ideal.localizationAwayToAtPrime` agrees with `algebraMap`. -/
@[simp]
theorem localizationAwayToAtPrime_algebraMap (P : Ideal R) [P.IsPrime] (f : R) (hf : f ∉ P)
    (r : R) :
    P.localizationAwayToAtPrime f hf (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.AtPrime P) r :=
  IsLocalization.map_eq _ r

/-- Composing `Ideal.localizationAwayToAtPrime` with `algebraMap R (Localization.Away f)` yields
`algebraMap R (Localization.AtPrime P)`. -/
@[simp]
theorem localizationAwayToAtPrime_comp_algebraMap (P : Ideal R) [P.IsPrime] (f : R)
    (hf : f ∉ P) :
    (P.localizationAwayToAtPrime f hf).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.AtPrime P) :=
  RingHom.ext (P.localizationAwayToAtPrime_algebraMap f hf)

end Ideal
