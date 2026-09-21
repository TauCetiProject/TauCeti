/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Principal complex powers on a sector

The principal `β`-th root followed by the principal `β`-th power recovers a complex number
whose argument has absolute value at most `β * π / 2`, for `0 < β`. This branch identity
is used to straighten a polygonal corner before applying Schwarz reflection.
-/

public section

open Complex

namespace TauCeti

/-- On a sector of half-angle `β * π / 2`, the principal `β`-th root followed by the
principal `β`-th power is the identity, including at zero. -/
theorem cpow_inv_cpow_of_sector {w : ℂ} {β : ℝ} (hβ : 0 < β)
    (hw : |w.arg| ≤ β * Real.pi / 2) :
    (w ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = w := by
  have hb : |w.arg * β⁻¹| ≤ Real.pi / 2 := by
    rw [← div_eq_mul_inv, abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
    nlinarith [hw]
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  rw [← Complex.cpow_mul]
  · simp [hβ.ne']
  · simp only [mul_im, log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    linarith [Real.pi_pos]
  · simp only [mul_im, log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    linarith [Real.pi_pos]

end TauCeti
