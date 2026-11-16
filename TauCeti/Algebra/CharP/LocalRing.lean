/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Basic
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Invertible integers and the residue characteristic of a local ring

A natural number is invertible in a commutative local ring exactly when the characteristic of the
residue field does not divide it, since an element of a local ring is a unit exactly when its
residue is nonzero. A local ring of prime characteristic has a residue field of the same
characteristic, since the residue characteristic divides it and is not `1`. Conversely, if a prime
`p` maps into the maximal ideal of a local domain as a nonzero element, every prime `q ≠ p` is a
unit and hence nonzero, so the ring has characteristic zero.

## Main results

* `IsLocalRing.isUnit_natCast_iff_not_dvd`: `n` is a unit of a local ring `R` exactly when
  the residue characteristic of `R` does not divide `n`.
* `IsLocalRing.ringChar_residueField_of_prime_ringChar`: a local ring of prime characteristic
  has a residue field of the same characteristic.
* `IsLocalRing.charZero_of_mem_maximalIdeal_of_ne_zero`: a local domain in which a prime `p`
  maps to a nonzero element of the maximal ideal has characteristic zero.
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

/-- If a prime natural number `p` maps into the maximal ideal of a local domain `R` as a nonzero
element, then `R` has characteristic zero: every prime `q ≠ p` is coprime to `p` and hence a unit
in `R`, while `(p : R) ≠ 0` by hypothesis. -/
theorem charZero_of_mem_maximalIdeal_of_ne_zero {R : Type*} [CommRing R] [NoZeroDivisors R]
    [IsLocalRing R] {p : ℕ} (hp : p.Prime) (hp_mem : (p : R) ∈ maximalIdeal R)
    (hp_ne : (p : R) ≠ 0) : CharZero R :=
  (_root_.CharZero.charZero_iff_forall_prime_ne_zero R).mpr fun q hq ↦
    (eq_or_ne q p).elim (· ▸ hp_ne) fun hne ↦ (((Nat.coprime_primes hq hp).mpr hne).isUnit_natCast
      (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hp_mem))).ne_zero

end IsLocalRing
