/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The sign of a basis relative to an orientation

The relative sign takes values in the integer units and compensates the sign of a change of
basis. Empty index types are included, so both zero-dimensional orientations retain their sign.
-/

public section
noncomputable section

namespace Orientation

section CommRing

variable {R E ι : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι]

/-- The sign of a basis relative to a model orientation, including empty index types. -/
def signBasis (o : Orientation R E ι) (b : Module.Basis ι R E) : ℤˣ := by
  classical
  exact if o = b.orientation then 1 else -1

/-- A basis giving the chosen orientation has positive relative sign. -/
@[simp]
theorem signBasis_orientation (b : Module.Basis ι R E) : signBasis b.orientation b = 1 := by
  simp [signBasis]

/-- Reversing the orientation reverses the relative basis sign. -/
@[simp]
theorem signBasis_neg (o : Orientation R E ι) (b : Module.Basis ι R E) :
    signBasis (-o) b = -signBasis o b := by
  rcases b.orientation_eq_or_eq_neg o with h | h
  · subst o
    simp [signBasis, (Module.Ray.ne_neg_self b.orientation).symm]
  · subst o
    rw [neg_neg b.orientation]
    simp [signBasis, (Module.Ray.ne_neg_self b.orientation).symm]

/-- Reversing the basis orientation reverses its relative sign. -/
theorem signBasis_eq_neg_of_orientation_eq_neg (o : Orientation R E ι)
    (b b' : Module.Basis ι R E) (h : b'.orientation = -b.orientation) :
    signBasis o b' = -signBasis o b := by
  rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
    subst o <;> simp [signBasis, h, Module.Ray.ne_neg_self b.orientation,
      (Module.Ray.ne_neg_self b.orientation).symm]

/-- The basis signs compensate the change-of-basis determinant to give a positive product. -/
theorem signBasis_mul_det_mul_pos (o : Orientation R E ι)
    (b b' : Module.Basis ι R E) :
    0 < (signBasis o b : R) * b.det b' * (signBasis o b' : R) := by
  have hsign : (signBasis o b : R) * (signBasis o b : R) = 1 := by
    exact_mod_cast Int.isUnit_mul_self (signBasis o b).isUnit
  rcases lt_or_gt_of_ne (b.isUnit_det b').ne_zero with hneg | hpos
  · have h := (b.orientation_ne_iff_eq_neg b'.orientation).mp fun h ↦
      (not_lt_of_gt hneg) ((b.orientation_eq_iff_det_pos b').mp h.symm)
    rw [signBasis_eq_neg_of_orientation_eq_neg o b b' h, Units.val_neg, Int.cast_neg,
      mul_neg, mul_right_comm (signBasis o b : R) (b.det b') _, hsign, one_mul]
    exact neg_pos.mpr hneg
  · have h : b.orientation = b'.orientation := (b.orientation_eq_iff_det_pos b').mpr hpos
    have hs : signBasis o b' = signBasis o b := by simp only [signBasis]; rw [h]
    rw [hs, mul_right_comm (signBasis o b : R) (b.det b') _, hsign, one_mul]
    exact hpos

end CommRing

section Field

variable {R E ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι]

/-- The relative basis sign compensates exactly for the signed determinant ratio. -/
theorem signBasis_mul_det_div_abs (o : Orientation R E ι) (b b' : Module.Basis ι R E) :
    (signBasis o b' : R) * (b.det b' / |b.det b'|) = (signBasis o b : R) := by
  have hp := signBasis_mul_det_mul_pos o b b'
  have hu (u : ℤˣ) : |(u : R)| = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  have ha : |b.det b'| = (signBasis o b : R) * b.det b' * (signBasis o b' : R) := by
    rw [← abs_of_pos hp, abs_mul, abs_mul, hu, hu, one_mul, mul_one]
  have hs : (signBasis o b : R) * (signBasis o b : R) = 1 := by
    exact_mod_cast Int.isUnit_mul_self (signBasis o b).isUnit
  rw [ha]
  field_simp [hp.ne']
  simpa only [pow_two, div_self (b.isUnit_det b').ne_zero] using hs.symm

end Field

end Orientation
