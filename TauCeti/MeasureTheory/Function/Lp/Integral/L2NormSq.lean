/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The squared norm of a real `L²` class as an integral

The squared norm of a class `f ∈ L²(μ)` of real functions is `∫ G²` for any almost everywhere
representative `G` of `f` (`MeasureTheory.L2.norm_sq_eq_integral_sq_of_ae_eq`). On an interval
`(a, b)` of the real line it is the interval integral `∫_a^b G²`
(`MeasureTheory.L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq`).
-/

public section

open Set

namespace MeasureTheory.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The squared norm of a real `L²` class with an almost everywhere representative `G` is
`∫ G²`. -/
theorem norm_sq_eq_integral_sq_of_ae_eq {f : Lp ℝ 2 μ} {G : α → ℝ} (h : f =ᵐ[μ] G) :
    ‖f‖ ^ 2 = ∫ x, G x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  exact integral_congr_ae (h.mono fun x hx ↦ by simp [hx, sq])

/-- The squared norm of a class of `L²(a, b)` with an almost everywhere representative `G` is
`∫_a^b G²`. -/
theorem norm_sq_eq_intervalIntegral_sq_of_ae_eq {a b : ℝ} (hab : a ≤ b)
    {f : Lp ℝ 2 (volume.restrict (Ioo a b))} {G : ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (Ioo a b)] G) : ‖f‖ ^ 2 = ∫ t in a..b, G t ^ 2 := by
  rw [norm_sq_eq_integral_sq_of_ae_eq h, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]

end MeasureTheory.L2
