/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.TopDegree

/-!
# Basis-independent signed top-form integrals

An arbitrary basis determines a coefficient and normalized Haar measure. Its sign relative to
an actual model orientation compensates for a reversing basis change. This includes empty bases:
the negative orientation in dimension zero has no positively oriented basis, but its signed
integral is still defined using any basis. No new orientation carrier is introduced.
-/

public section

noncomputable section

open MeasureTheory

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

end Orientation

namespace Module.Basis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

/-- The actual signed coefficient integral is independent of an arbitrary basis. The model
orientation is fixed; the relative basis sign handles both determinant signs and dimension zero. -/
theorem integral_signed_apply_eq (o : Orientation ℝ E ι) (b b' : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (Orientation.signBasis o b : ℝ) * (∫ x, ω x b ∂b.addHaar) =
      (Orientation.signBasis o b' : ℝ) * (∫ x, ω x b' ∂b'.addHaar) := by
  rw [integral_apply_basis_change b b' ω, ← mul_assoc,
    Orientation.signBasis_mul_det_div_abs]

omit [DecidableEq ι] in
/-- Top-form coefficient integrability is independent of the basis and its Haar normalization. -/
theorem integrable_apply_basis_iff (b b' : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    Integrable (fun x ↦ ω x b') b'.addHaar ↔ Integrable (fun x ↦ ω x b) b.addHaar := by
  classical
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [addHaar_eq_smul_of_basis b b', integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  simp_rw [ContinuousAlternatingMap.apply_eq_det_mul (b := b) (v := b')]
  exact integrable_const_mul_iff (b.isUnit_det b') _

omit [FiniteDimensional ℝ E] in
/-- Multiplication by the relative orientation sign preserves genuine integrability. -/
theorem integrable_signed_apply_iff (o : Orientation ℝ E ι) (b : Basis ι ℝ E)
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    Integrable (fun x ↦ (Orientation.signBasis o b : ℝ) * ω x b) b.addHaar ↔
      Integrable (fun x ↦ ω x b) b.addHaar := by
  apply integrable_const_mul_iff
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast (Orientation.signBasis o b).ne_zero

end Module.Basis
