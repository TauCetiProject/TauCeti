/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.Algebra.Group.Units.UnitOrOne
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder

import TauCeti.Data.ZMod.Units

/-!
# Integer labels in the cyclotomic tower

We work in the unit group modulo the cyclotomic order, which labels the infinite places of
an imaginary quadratic cyclotomic tower. An integer acts through its residue if it is prime
to the order and through the identity otherwise. Reducing the label of `-n` to the base modulus
tests exactly the residue class used in the short prime sum.

## References

The conventions for integer labels and their reduction follow `New.Parameters.placeOfInt`
and `New.Parameters.placeClass_placeOfInt_eq_neg_one_iff` in
`grh/src/New/Reduction/Data/FieldsAndPlaces.lean` of https://github.com/lsernau/grh-lean at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- The unit label of an integer at cyclotomic level `q₁ s`, with identity label for nonunits. -/
noncomputable def placeOfInt (s : ℕ) (a : ℤ) : (ZMod (P.q₁ s))ˣ :=
  Units.unitOrOne (a : ZMod (P.q₁ s))

/-- Express the label as the canonical unit-or-identity label of the residue. -/
theorem placeOfInt_def (s : ℕ) (a : ℤ) :
    P.placeOfInt s a = Units.unitOrOne (a : ZMod (P.q₁ s)) := (rfl)

/-- The same integers are invertible at the base and at every level of the tower. -/
theorem isUnit_intCast_q₁_iff (s : ℕ) (a : ℤ) :
    IsUnit (a : ZMod (P.q₁ s)) ↔ IsUnit (a : ZMod P.q₀) := by
  simp only [Int.isUnit_intCast_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast,
    ← Nat.coprime_iff_gcd_eq_one]
  refine ⟨fun h ↦ h.coprime_dvd_right (P.q₀_dvd_q₁ s), fun h ↦ ?_⟩
  exact Nat.coprime_of_dvd fun p hp ha hq ↦
    (hp.coprime_iff_not_dvd.mp (h.coprime_dvd_left ha)) (P.dvd_q₀_of_dvd_q₁ hp hq)

/-- For an integer invertible modulo `q₀`, the underlying residue of its label is its cast. -/
@[simp] theorem val_placeOfInt_of_isUnit (s : ℕ) {a : ℤ} (ha : IsUnit (a : ZMod P.q₀)) :
    (P.placeOfInt s a : ZMod (P.q₁ s)) = a := by
  rw [placeOfInt_def, Units.val_unitOrOne_of_isUnit ((P.isUnit_intCast_q₁_iff s a).mpr ha)]

/-- An integer not invertible modulo `q₀` has identity label. -/
@[simp] theorem placeOfInt_of_not_isUnit (s : ℕ) {a : ℤ} (ha : ¬ IsUnit (a : ZMod P.q₀)) :
    P.placeOfInt s a = 1 := by
  rw [placeOfInt_def, Units.unitOrOne_of_not_isUnit (mt (P.isUnit_intCast_q₁_iff s a).mp ha)]

/-- The label of an integer power is the corresponding power of the label. -/
@[simp] theorem placeOfInt_pow (s : ℕ) (a : ℤ) (k : ℕ) :
    P.placeOfInt s (a ^ k) = P.placeOfInt s a ^ k := by
  simp [placeOfInt_def]

/-- On integers invertible at the base, reduction to any divisor of `q₁` gives the residue. -/
@[simp] theorem val_unitsMap_placeOfInt_of_isUnit {s m : ℕ} (hm : m ∣ P.q₁ s) {a : ℤ}
    (ha : IsUnit (a : ZMod P.q₀)) : (ZMod.unitsMap hm (P.placeOfInt s a) : ZMod m) = a := by
  rw [ZMod.unitsMap_val, P.val_placeOfInt_of_isUnit s ha, ZMod.cast_intCast hm]

/-- Reduction to the base commutes with the unit-or-identity convention. -/
@[simp] theorem unitsMap_placeOfInt (s : ℕ) (a : ℤ) :
    ZMod.unitsMap (P.q₀_dvd_q₁ s) (P.placeOfInt s a) = Units.unitOrOne (a : ZMod P.q₀) := by
  rw [ZMod.unitsMap_def, placeOfInt_def, Units.map_unitOrOne]
  · simp
  · simpa using (P.isUnit_intCast_q₁_iff s a).mpr

/-- A label is in the `-1` fiber over the base exactly for integers congruent to `-1`. -/
theorem unitsMap_placeOfInt_eq_neg_one_iff (s : ℕ) (a : ℤ) :
    ZMod.unitsMap (P.q₀_dvd_q₁ s) (P.placeOfInt s a) = -1 ↔ a ≡ -1 [ZMOD P.q₀] := by
  let : Fact (2 < P.q₀) := ⟨by have := P.le_q₀; omega⟩
  have h : (-1 : (ZMod P.q₀)ˣ) ≠ 1 := fun he ↦
    ZMod.neg_one_ne_one (by simpa using congrArg Units.val he)
  rw [P.unitsMap_placeOfInt, Units.unitOrOne_eq_iff_of_ne_one h]
  simpa only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] using
    ZMod.intCast_eq_intCast_iff a (-1) P.q₀

/-- Restricting the unrestricted weight to the `-1` fiber of the label of `-n` gives precisely
`λ_q₀(n)`, the weight of the base progression `n ≡ 1 (mod q₀)`. -/
theorem primeWeight_eq_ite_unitsMap_placeOfInt (s n : ℕ) :
    primeWeight P.d P.q₀ n =
      if ZMod.unitsMap (P.q₀_dvd_q₁ s) (P.placeOfInt s (-(n : ℤ))) = -1 then
        primeWeight P.d 1 n else 0 := by
  have h := (P.unitsMap_placeOfInt_eq_neg_one_iff s (-(n : ℤ))).trans
    (Int.neg_modEq_neg.trans (ZMod.intCast_eq_intCast_iff n 1 P.q₀).symm)
  simp only [Int.cast_natCast, Int.cast_one] at h
  simp only [h, primeWeight_def, Subsingleton.elim (n : ZMod 1) 1, ↓reduceIte]

end TauCeti.OneSidedBound.Parameters
