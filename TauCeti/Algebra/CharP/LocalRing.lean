/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced

/-!
# Invertible integers and the residue characteristic of a local ring

A natural number is invertible in a commutative local ring exactly when the characteristic of the
residue field does not divide it, since an element of a local ring is a unit exactly when its
residue is nonzero. A local ring of prime characteristic has a residue field of the same
characteristic, since the residue characteristic divides it and is not `1`. This applies in
particular to a local domain of positive characteristic. When the residue field has exponential
characteristic `p`, elements with equal `p^k`-th powers have equal residues modulo the maximal
ideal because iterated Frobenius on the residue field is injective.

## Main results

* `IsLocalRing.isUnit_natCast_iff_not_dvd`: `n` is a unit of a local ring `R` exactly when
  the residue characteristic of `R` does not divide `n`.
* `IsLocalRing.ringChar_residueField_of_prime_ringChar`: a local ring of prime characteristic
  has a residue field of the same characteristic.
* `IsLocalRing.residue_eq_of_pow_eq`: in a local ring of residue exponential characteristic `p`,
  elements with equal `p^k`-th powers have equal residues.
* `IsLocalRing.residue_units_eq_of_exists_pow_eq`: in a local ring of residue exponential
  characteristic `p`, units with equal `p^k`-th powers for some `k` have equal residues.
-/

public section

namespace IsLocalRing

/-- A natural number is invertible in a commutative local ring exactly when the residue
characteristic does not divide it. -/
@[simp]
theorem isUnit_natCast_iff_not_dvd {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} :
    IsUnit (n : R) ↔ ¬ ringChar (IsLocalRing.ResidueField R) ∣ n := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, ne_eq, ← ringChar.spec]

/-- A local ring of prime characteristic has a residue field of the same characteristic. -/
theorem ringChar_residueField_of_prime_ringChar {R : Type*} [CommRing R]
    [IsLocalRing R] (h : (ringChar R).Prime) :
    ringChar (IsLocalRing.ResidueField R) = ringChar R :=
  ((Nat.dvd_prime h).1 (CharP.dvd_of_ringHom (IsLocalRing.residue R) _ _)).resolve_left
    CharP.ringChar_ne_one

/-- In a local ring whose residue field has exponential characteristic `p`, elements with equal
`p ^ k`-th powers have equal residues modulo the maximal ideal. -/
theorem residue_eq_of_pow_eq {R : Type*} [CommRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar (IsLocalRing.ResidueField R) p] {k : ℕ} {x y : R}
    (h : x ^ p ^ k = y ^ p ^ k) :
    IsLocalRing.residue R x = IsLocalRing.residue R y := by
  refine iterateFrobenius_inj (IsLocalRing.ResidueField R) p k ?_
  simpa only [iterateFrobenius_def, ← map_pow] using congrArg (IsLocalRing.residue R) h

/-- In a local ring whose residue field has exponential characteristic `p`, units with equal
`p ^ k`-th powers for some `k` have equal residues modulo the maximal ideal. -/
theorem residue_units_eq_of_exists_pow_eq {R : Type*} [CommRing R] [IsLocalRing R]
    (p : ℕ) [ExpChar (IsLocalRing.ResidueField R) p] {u v : Rˣ}
    (h : ∃ k : ℕ, u ^ p ^ k = v ^ p ^ k) :
    IsLocalRing.residue R u = IsLocalRing.residue R v :=
  let ⟨_, hk⟩ := h
  residue_eq_of_pow_eq p (by simpa using congrArg Units.val hk)

end IsLocalRing
