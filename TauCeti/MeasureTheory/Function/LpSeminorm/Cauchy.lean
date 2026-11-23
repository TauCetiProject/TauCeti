/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Convergence in `Lᵖ` gives the `Lᵖ` Cauchy property

If `f j → g` in `Lᵖ(μ)` along a filter `l`, then `‖f i - f j‖_{Lᵖ(μ)} → 0` as `(i, j)` tends to
`l ×ˢ l` (`MeasureTheory.tendsto_eLpNorm_sub_prod_of_tendsto_eLpNorm_sub`). This holds for every
exponent `p` and without measurability assumptions, through the quasi-triangle inequality
`MeasureTheory.eLpNorm_sub_le'`.
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Type*} [NormedAddCommGroup F]
  {p : ℝ≥0∞}

/-- **Convergence in `Lᵖ` gives the `Lᵖ` Cauchy property.** If `f j → g` in `Lᵖ(μ)` along `l`,
then `‖f i - f j‖_{Lᵖ(μ)} → 0` as `(i, j)` tends to `l ×ˢ l`. -/
theorem tendsto_eLpNorm_sub_prod_of_tendsto_eLpNorm_sub {ι : Type*} {l : Filter ι}
    {f : ι → X → F} {g : X → F} (h : Tendsto (fun j => eLpNorm (f j - g) p μ) l (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm (f ij.1 - f ij.2) p μ) (l ×ˢ l) (𝓝 0) := by
  have hlim := ENNReal.Tendsto.const_mul ((h.comp tendsto_fst).add (h.comp tendsto_snd))
    (.inr (ENNReal.LpAddConst_lt_top p).ne)
  rw [add_zero, mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun ij => ?_
  rw [← sub_sub_sub_cancel_right (f ij.1) (f ij.2) g]
  exact eLpNorm_sub_le' p

end MeasureTheory
