/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation
public import Mathlib.Basic.Real.Basic

/-!
# The sign of a basis relative to an orientation

The relative sign takes values in the integer units and compensates the sign of a change of
basis. Empty index types are included, so both zero-dimensional orientations retain their sign.
-/

public section

noncomputable section

namespace Orientation

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

/-- The sign of a basis relative to a model orientation, including empty index types. -/
def signBasis (o : Orientation ℝ E ι) (b : Module.Basis ι ℝ E) : ℤˣ := by
  classical
  exact if o = b.orientation then 1 else -1

/-- A basis giving the chosen orientation has positive relative sign. -/
@[simp]
theorem signBasis_orientation (b : Module.Basis ι ℝ E) : signBasis b.orientation b = 1 := by
  simp [signBasis]

/-- Reversing the orientation reverses the relative basis sign. -/
@[simp]
theorem signBasis_neg (o : Orientation ℝ E ι) (b : Module.Basis ι ℝ E) :
    signBasis (-o) b = -signBasis o b := by
  rcases b.orientation_eq_or_eq_neg o with h | h
  · subst o
    simp [signBasis, (Module.Ray.ne_neg_self b.orientation).symm]
  · subst o
    rw [neg_neg b.orientation]
    simp [signBasis, (Module.Ray.ne_neg_self b.orientation).symm]

/-- Reversing the basis orientation reverses its relative sign. -/
theorem signBasis_eq_neg_of_orientation_eq_neg (o : Orientation ℝ E ι)
    (b b' : Module.Basis ι ℝ E) (h : b'.orientation = -b.orientation) :
    signBasis o b' = -signBasis o b := by
  rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
    subst o <;> simp [signBasis, h, Module.Ray.ne_neg_self b.orientation,
      (Module.Ray.ne_neg_self b.orientation).symm]

/-- The relative basis sign compensates exactly for the signed determinant ratio. -/
theorem signBasis_mul_det_div_abs (o : Orientation ℝ E ι) (b b' : Module.Basis ι ℝ E) :
    (signBasis o b' : ℝ) * (b.det b' / |b.det b'|) = (signBasis o b : ℝ) := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hne : b'.orientation ≠ b.orientation := by
      intro h
      have hp := (b.orientation_eq_iff_det_pos b').mp h.symm
      exact (not_lt_of_gt hneg) hp
    have h := (b.orientation_ne_iff_eq_neg b'.orientation).mp hne
    rw [signBasis_eq_neg_of_orientation_eq_neg o b b' h, abs_of_neg hneg]
    have hf : b.det b' / -b.det b' = -1 := by field_simp
    rw [hf]
    simp
  · have h : b.orientation = b'.orientation := (b.orientation_eq_iff_det_pos b').mpr hpos
    have hs : signBasis o b' = signBasis o b := by simp only [signBasis]; rw [h]
    rw [hs, abs_of_pos hpos, div_self hd, mul_one]

/-- The basis signs compensate the change-of-basis determinant to give a positive product. -/
theorem signBasis_mul_det_mul_pos (o : Orientation ℝ E ι)
    (b b' : Module.Basis ι ℝ E) :
    0 < (signBasis o b : ℝ) * b.det b' * (signBasis o b' : ℝ) := by
  have h := signBasis_mul_det_div_abs o b b'
  have hsign : (signBasis o b' : ℝ) * (signBasis o b' : ℝ) = 1 := by
    exact_mod_cast Int.isUnit_mul_self (signBasis o b').isUnit
  have hd : 0 < |b.det b'| := abs_pos.mpr (b.isUnit_det b').ne_zero
  have he : (signBasis o b : ℝ) * b.det b' * (signBasis o b' : ℝ) = |b.det b'| := by
    rw [← h]
    calc
      (signBasis o b' : ℝ) * (b.det b' / |b.det b'|) * b.det b' *
          (signBasis o b' : ℝ) =
        ((signBasis o b' : ℝ) * (signBasis o b' : ℝ)) *
          ((b.det b') ^ 2 / |b.det b'|) := by ring
      _ = |b.det b'| := by rw [hsign, one_mul, ← sq_abs]; field_simp
  rw [he]
  exact hd

end Orientation
