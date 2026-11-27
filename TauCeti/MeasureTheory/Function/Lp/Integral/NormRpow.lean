/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The `γ`-th power of the norm of an `L^γ` class as an integral

For `0 < γ < ∞` the norm of a class `f ∈ L^γ(μ)` is `(∫ ‖f‖ ^ γ) ^ (1 / γ)`, so its `γ`-th power
is the Bochner integral `∫ ‖f‖ ^ γ` (`MeasureTheory.Lp.norm_rpow_eq_integral_norm_rpow`). This
is the form in which bounds on `Lᵖ` norms are passed to averages of `‖f‖ ^ γ`.
-/

public section

namespace MeasureTheory.Lp

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- For `0 < γ`, the `γ`-th power of the norm of `f ∈ L^γ` is the integral of `‖f‖ ^ γ`. -/
theorem norm_rpow_eq_integral_norm_rpow {γ : ℝ} (hγ : 0 < γ) (f : Lp E (ENNReal.ofReal γ) μ) :
    ‖f‖ ^ γ = ∫ x, ‖f x‖ ^ γ ∂μ := by
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ γ ∂μ := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by simpa using hγ)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hγ.le, ENNReal.toReal_ofReal
    (Real.rpow_nonneg hI _), Real.rpow_inv_rpow hI hγ.ne']

end MeasureTheory.Lp
