/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Jensen's inequality for powers of set averages

For `γ ≥ 1` the power `t ↦ t^γ` is convex on `[0, ∞)`, so the `γ`-th power of the average of
`‖f‖` over a set is at most the average of `‖f‖^γ`:

`(⨍_s ‖f‖)^γ ≤ ⨍_s ‖f‖^γ`.

This compares a mean oscillation in `L¹` with one in `L^γ`, as in Krylov's sharp function method,
and an `L¹` average with an `L^γ` average.

## Main results

* `TauCeti.rpow_setAverage_norm_le_setAverage_norm_rpow`: `(⨍_s ‖f‖)^γ ≤ ⨍_s ‖f‖^γ`.
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  {f : X → F} {s : Set X}

/-- **Jensen's inequality for powers of set averages.** For `γ ≥ 1` and `‖f‖^γ` integrable on
`s`, `(⨍_s ‖f‖)^γ ≤ ⨍_s ‖f‖^γ`. No finiteness of `μ s` is needed: on a set of measure `0` or `∞`
both averages vanish. -/
theorem rpow_setAverage_norm_le_setAverage_norm_rpow {γ : ℝ} (hγ : 1 ≤ γ)
    (hi : IntegrableOn (fun x => ‖f x‖ ^ γ) s μ) :
    (⨍ x in s, ‖f x‖ ∂μ) ^ γ ≤ ⨍ x in s, ‖f x‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hR : 0 ≤ ⨍ x in s, ‖f x‖ ^ γ ∂μ := average_nonneg fun x => by positivity
  -- Where the average of `‖f‖` vanishes, the left side is `0`.
  have hzero : ⨍ x in s, ‖f x‖ ∂μ = 0 → (⨍ x in s, ‖f x‖ ∂μ) ^ γ ≤ ⨍ x in s, ‖f x‖ ^ γ ∂μ :=
    fun h => by rwa [h, Real.zero_rpow hγ0.ne']
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · exact hzero (by simp [setAverage_eq, Measure.real, h0])
  rcases eq_or_ne (μ s) ⊤ with htop | htop
  · exact hzero (by simp [setAverage_eq, Measure.real, htop])
  by_cases hf : IntegrableOn (fun x => ‖f x‖) s μ
  · exact ConvexOn.map_set_average_le (convexOn_rpow hγ)
      (fun t _ => (Real.continuousAt_rpow_const t γ (Or.inr hγ0.le)).continuousWithinAt)
      isClosed_Ici h0 htop (ae_of_all _ fun x => norm_nonneg (f x)) hf hi
  · exact hzero (by rw [setAverage_eq, integral_undef hf, smul_zero])

end TauCeti
