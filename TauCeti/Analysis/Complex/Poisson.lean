/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson

/-!
# Similarity invariance of the complex Poisson kernel

The Poisson kernel is unchanged when its center is translated to the origin and its arguments
are scaled by the inverse of a nonzero real number.
-/

public section

noncomputable section

namespace TauCeti

open Complex

/-- Translating the center of the Poisson kernel to zero and rescaling by a nonzero real number
does not change its value. -/
theorem poissonKernel_inv_smul_sub {c a z : ℂ} {R : ℝ} (hR : R ≠ 0) :
    poissonKernel 0 (R⁻¹ • (a - c)) (R⁻¹ • (z - c)) = poissonKernel c a z := by
  simp only [poissonKernel_def, sub_zero, sub_sub_sub_cancel_right, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_inv]
  field_simp

end TauCeti

end
