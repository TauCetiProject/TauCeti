/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of the complex logarithm

The derivative of a logarithm with a scaled argument is the reciprocal of the point on its
slit domain.
-/

public section

namespace Complex

/-- The derivative of the logarithm of `z / c` is `z⁻¹` on the resulting slit domain. -/
theorem hasDerivAt_log_div_const (z : ℂ) {c : ℂ} (hz : z / c ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ log (w / c)) z⁻¹ z := by
  obtain ⟨hz0, hc⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  have h : HasDerivAt (fun w : ℂ ↦ w / c) (1 / c) z :=
    (hasDerivAt_id z).div_const c
  convert h.clog hz using 1
  field_simp [hc, hz0]

end Complex
