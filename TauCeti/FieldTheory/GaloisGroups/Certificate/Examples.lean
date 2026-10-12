/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check

import Mathlib.Tactic.ComputeDegree
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees

/-!
# Examples of quintic Galois-group certificate evidence

This module gives a symmetric-route certificate for `X⁵ - X - 1`, from its factorizations modulo
`5` and `2`, and reads the label `5T5` off it.

## Main results

* `TauCeti.QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one`: `X⁵ - X - 1` has a
  symmetric-route certificate.
* `TauCeti.hasGaloisLabel_X_pow_five_sub_X_sub_one`: `X⁵ - X - 1` has label `5T5`.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-- `X⁵ - X - 1` has a symmetric-route certificate: it is irreducible modulo `5`, and has factor
degrees `(2,3)` modulo `2`. Both primes are good, since neither divides its discriminant. -/
theorem QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one :
    (QuinticCertificate.symmetric 5 2).check (X ^ 5 - X - 1) = true := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := monic_X_pow_five_sub_X_sub_one
  have hirr := (factorDegrees_eq_singleton_iff.mp factorDegrees_X_pow_five_sub_X_sub_one_five).1
  have hgood5 : IsGoodPrime (X ^ 5 - X - 1) 5 := (isGoodPrime_iff _ 5).mpr <|
    (hf.separable_map_zmod_iff_not_dvd_discr 5).mp (PerfectField.separable_of_irreducible hirr)
  have hgood2 : IsGoodPrime (X ^ 5 - X - 1) 2 :=
    (isGoodPrime_iff _ 2).mpr not_two_dvd_discr_X_pow_five_sub_X_sub_one
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_symmetric_iff]
  refine ⟨HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_sub_one_five,
    HasFactorDegrees.mk hgood2 ?_⟩
  rw [factorDegrees_X_pow_five_sub_X_sub_one_two]
  decide

/-- **`X⁵ - X - 1` has label `5T5`.** Its symmetric-route certificate checks. -/
theorem hasGaloisLabel_X_pow_five_sub_X_sub_one :
    HasGaloisLabel ((X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have h := QuinticCertificate.check_sound monic_X_pow_five_sub_X_sub_one
    QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one
  rwa [QuinticCertificate.label_symmetric] at h

end TauCeti
