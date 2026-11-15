/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Exponential moments from bounded support

If a measure is concentrated, up to a null set, on a closed ball `‖x‖ ≤ R` centred at the origin,
then the exponential weight `exp (a * ‖x‖)` is essentially bounded by `exp (|a| * R)`, so
multiplying an integrable function by it preserves integrability, for every rate `a : ℝ`.

## Main results

* `MeasureTheory.Integrable.exp_norm_smul_of_ae_norm_le`: the statement for a seminormed group
  domain and a scalar weight in any `RCLike` field.
* `MeasureTheory.Integrable.exp_abs_smul_of_ae_abs_le`: the real-line form, with `|x|` in place
  of `‖x‖`. For instance, it applies to measures supported on `[-1, 1]` such as the Chebyshev
  measure.
-/

public section

namespace MeasureTheory

variable {α 𝕜 β : Type*} [SeminormedAddGroup α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [RCLike 𝕜] [NormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
variable {μ : Measure α} {g : α → β}

/-- Multiplication by `exp (a * ‖x‖)` preserves integrability on a measure that is essentially
supported in the closed ball of radius `R` centred at the origin. -/
theorem Integrable.exp_norm_smul_of_ae_norm_le (hg : Integrable g μ) (a R : ℝ)
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    Integrable (fun x : α => (Real.exp (a * ‖x‖) : 𝕜) • g x) μ := by
  refine hg.bdd_smul (Real.exp (|a| * R)) (by fun_prop) ?_
  filter_upwards [hR] with x hx
  rw [RCLike.norm_ofReal, Real.abs_exp, Real.exp_le_exp]
  exact (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg x)).trans (by gcongr)

/-- Real-line version of `Integrable.exp_norm_smul_of_ae_norm_le`, stated with `|x|`. -/
theorem Integrable.exp_abs_smul_of_ae_abs_le {μ : Measure ℝ} {g : ℝ → β}
    (hg : Integrable g μ) (a R : ℝ) (hR : ∀ᵐ x ∂μ, |x| ≤ R) :
    Integrable (fun x : ℝ => (Real.exp (a * |x|) : 𝕜) • g x) μ := by
  simpa only [Real.norm_eq_abs] using
    hg.exp_norm_smul_of_ae_norm_le (𝕜 := 𝕜) a R (by simpa only [Real.norm_eq_abs] using hR)

end MeasureTheory
