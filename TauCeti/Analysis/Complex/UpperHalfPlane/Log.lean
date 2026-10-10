/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The logarithm maps the upper half-plane onto a strip

The principal logarithm is a holomorphic bijection from the open upper half-plane
onto the horizontal strip with imaginary part between `0` and `π`. Its inverse is
complex exponentiation. This supplies the logarithmic coordinate for parallel-sided
conformal ends.
-/

public section

open Complex Function Set UpperHalfPlane

namespace TauCeti

/-- The principal logarithm maps the upper half-plane bijectively onto the open
horizontal strip of height `π`. -/
theorem bijOn_log_upperHalfPlaneSet :
    BijOn Complex.log upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} := by
  have hmaps : MapsTo Complex.log upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} := by
    intro z hz
    rw [mem_ofPred_eq, Complex.log_im]
    refine ⟨lt_of_le_of_ne (arg_nonneg_iff.mpr hz.le) ?_, arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩
    intro h
    exact hz.ne' (arg_eq_zero_iff.mp h.symm).2
  refine ⟨hmaps, fun z hz v hv h => ?_, fun w hw => ?_⟩
  · have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    simpa only [exp_log hz0, exp_log hv0] using congrArg Complex.exp h
  · refine ⟨Complex.exp w, ?_, Complex.log_exp (by linarith [Real.pi_pos, hw.1]) hw.2.le⟩
    simpa only [upperHalfPlaneSet, mem_ofPred_eq, Complex.exp_im] using
      mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2)

/-- For `p < q`, the real fractional-linear transformation sending `p` to infinity
and `q` to zero preserves the upper half-plane bijectively. -/
theorem bijOn_sub_div_sub_upperHalfPlaneSet {p q : ℝ} (hpq : p < q) :
    BijOn (fun z : ℂ => (z - (q : ℂ)) / (z - (p : ℂ)))
      upperHalfPlaneSet upperHalfPlaneSet := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, -q; 1, -p] (by simpa [Matrix.det_fin_two, sub_eq_add_neg, add_comm] using
      (sub_pos.mpr hpq).ne')
  have hg : 0 < g.det.val := by
    simpa [g, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using sub_pos.mpr hpq
  have hsemi : Semiconj ((↑) : ℍ → ℂ) (fun z => g • z)
      (fun z : ℂ => (z - (q : ℂ)) / (z - (p : ℂ))) := by
    intro z
    rw [UpperHalfPlane.coe_smul_of_det_pos hg]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, g,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, sub_eq_add_neg]
  simpa only [UpperHalfPlane.range_coe] using
    hsemi.bijOn_range (MulAction.toPerm g).bijective UpperHalfPlane.coe_injective

end TauCeti
