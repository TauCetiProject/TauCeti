/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# The logarithm maps the upper half-plane onto a strip

The principal logarithm is a holomorphic bijection from the open upper half-plane
onto the horizontal strip with imaginary part between `0` and `π`. Its inverse is
complex exponentiation. This supplies the logarithmic coordinate for parallel-sided
conformal ends.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

/-- The principal logarithm maps the upper half-plane bijectively onto the open
horizontal strip of height `π`. -/
theorem bijOn_log_upperHalfPlaneSet :
    BijOn Complex.log upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} := by
  refine InvOn.bijOn ⟨fun z hz => exp_log (ne_of_apply_ne Complex.im hz.ne'),
    fun w hw => log_exp ((neg_neg_of_pos Real.pi_pos).trans hw.1) hw.2.le⟩
    (fun z hz => ?_) fun w hw => ?_
  · rw [mem_ofPred_eq, log_im]
    exact ⟨(arg_nonneg_iff.mpr hz.le).lt_of_ne fun h => hz.ne' (arg_eq_zero_iff.mp h.symm).2,
      arg_lt_pi_iff.mpr (.inr hz.ne')⟩
  · simpa only [upperHalfPlaneSet, mem_ofPred_eq, exp_im] using
      mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2)

end TauCeti
