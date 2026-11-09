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
  refine ⟨hmaps, expOpenPartialHomeomorph.symm.injOn.mono
    (fun z hz => UpperHalfPlane.mem_slitPlane ⟨z, hz⟩), fun w hw => ?_⟩
  refine ⟨Complex.exp w, ?_, expOpenPartialHomeomorph.left_inv
    ⟨by linarith [Real.pi_pos, hw.1], hw.2⟩⟩
  simpa only [upperHalfPlaneSet, mem_ofPred_eq, Complex.exp_im] using
    mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2)

end TauCeti
