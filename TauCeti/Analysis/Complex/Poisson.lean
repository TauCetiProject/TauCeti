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
are multiplied by the inverse of a nonzero complex number. This normalized-coordinate identity
transports formulas between centered unit disks and translated, rescaled disks, including the
Green-kernel boundary derivative formula.
-/

public section

noncomputable section

namespace TauCeti

open Complex

/-- Translating the center of the Poisson kernel to zero and multiplying by a nonzero complex number
does not change its value. -/
theorem poissonKernel_inv_mul_sub {c a z q : ℂ} (hq : q ≠ 0) :
    poissonKernel 0 (q⁻¹ * (a - c)) (q⁻¹ * (z - c)) = poissonKernel c a z := by
  simp only [poissonKernel_def, sub_zero, sub_sub_sub_cancel_right, ← mul_sub, norm_mul,
    norm_inv]
  field_simp

end TauCeti

end
