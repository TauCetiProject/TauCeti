/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Pointwise bounds for infinite sums in `Lᵖ`

If a countable family `u` in `Lᵖ` has sum `v` in the `Lᵖ` norm, then `‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ`
at almost every point. Unlike `MeasureTheory.Lp.hasSum_coeFn_tsum`, this needs no summability
of the norms `‖u i‖`: it only uses that some sequence of finite partial sums converges to `v`
almost everywhere. A typical use is a sum of functions with disjoint supports in `L²`, whose norms
are square-summable but need not be summable.

## Main declarations

* `MeasureTheory.Lp.ae_enorm_le_tsum_enorm_of_hasSum`: the pointwise bound.
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

namespace Lp

variable {α E κ : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If a countable family `u` in `Lᵖ` has sum `v`, then at almost every point the extended norm
of `v` is at most the sum of the extended norms of the `u i`. -/
theorem ae_enorm_le_tsum_enorm_of_hasSum [Countable κ] {u : κ → Lp E p μ} {v : Lp E p μ}
    (h : HasSum u v) : ∀ᵐ x ∂μ, ‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ := by
  obtain ⟨S, -, hS⟩ := (tendstoInMeasure_of_tendsto_Lp h).exists_seq_tendsto_ae'
  have hsum : ∀ᵐ x ∂μ, ∀ n, (⇑(∑ i ∈ S n, u i) : α → E) x = ∑ i ∈ S n, u i x :=
    ae_all_iff.2 fun n => coeFn_fun_finsetSum (S n) u
  filter_upwards [hS, hsum] with x hx hxsum
  refine le_of_tendsto' (continuous_enorm.tendsto _ |>.comp hx) fun n => ?_
  simp only [Function.comp_apply, hxsum n]
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)

end Lp

end MeasureTheory
