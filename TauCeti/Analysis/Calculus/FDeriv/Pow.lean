/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The real derivative of a complex power

The real derivative of `w ↦ wⁿ` on `ℂ` is multiplication by `n zⁿ⁻¹`, so its operator norm is at
most `n ‖z‖ⁿ⁻¹` (`TauCeti.norm_fderiv_pow_le`).
-/

public section

namespace TauCeti

/-- The real derivative of `w ↦ wⁿ` has norm at most `n ‖z‖ⁿ⁻¹`. -/
theorem norm_fderiv_pow_le (n : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w : ℂ ↦ w ^ n) z‖ ≤ n * ‖z‖ ^ (n - 1) := by
  rw [((hasDerivAt_pow n z).hasFDerivAt.restrictScalars ℝ).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  simp [mul_comm]

end TauCeti
