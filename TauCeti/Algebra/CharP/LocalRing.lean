/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Invertible integers and the residue characteristic of a local ring

A natural number is invertible in a commutative local ring exactly when the characteristic of the
residue field does not divide it, since an element of a local ring is a unit exactly when its
residue is nonzero. A local domain of positive characteristic has a residue field of the same
characteristic, since that characteristic is prime and the residue field is nonzero.

## Main results

* `IsLocalRing.isUnit_natCast_iff_not_dvd`: `n` is a unit of a local ring `R` exactly when
  the residue characteristic of `R` does not divide `n`.
* `IsLocalRing.ringChar_residueField_of_ringChar_ne_zero`: a local domain of positive
  characteristic has a residue field of the same characteristic.
-/

public section

namespace TauCeti

/-- A natural number is invertible in a commutative local ring exactly when the residue
characteristic does not divide it. -/
@[simp]
theorem _root_.IsLocalRing.isUnit_natCast_iff_not_dvd {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} :
    IsUnit (n : R) ↔ ¬ ringChar (IsLocalRing.ResidueField R) ∣ n := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, ne_eq, ← ringChar.spec]

/-- A local domain of positive characteristic has a residue field of the same characteristic. -/
theorem _root_.IsLocalRing.ringChar_residueField_of_ringChar_ne_zero {R : Type*} [CommRing R]
    [IsDomain R] [IsLocalRing R] (h : ringChar R ≠ 0) :
    ringChar (IsLocalRing.ResidueField R) = ringChar R :=
  have := CharP.of_ringHom_of_ne_zero (IsLocalRing.residue R) (ringChar R) h
  ringChar.eq _ _

end TauCeti
