/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The logarithm is Lipschitz away from zero

For `a > 0` the logarithm is `a⁻¹`-Lipschitz on `[a, ∞)`
(`Real.lipschitzOnWith_log_Ici`): for `a ≤ y ≤ x`,
`log x - log y = log (x / y) ≤ x / y - 1 = (x - y) / y ≤ (x - y) / a`.
The constant is the supremum of the derivative `1 / t` over `[a, ∞)`, so it is optimal.

Consequently the logarithm of a `K`-Lipschitz function bounded below by `a > 0` is
`a⁻¹ K`-Lipschitz (`LipschitzWith.log`), and `t ↦ log (max 1 t)` is `1`-Lipschitz
(`Real.lipschitzWith_log_max_one`).
-/

public section

namespace Real

open Set

/-- **The logarithm is `a⁻¹`-Lipschitz on `[a, ∞)`** for `a > 0`. -/
theorem lipschitzOnWith_log_Ici {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith (Real.toNNReal a⁻¹) log (Ici a) := by
  refine LipschitzOnWith.of_le_add_mul' a⁻¹ fun x hx y hy => ?_
  have hx0 : 0 < x := ha.trans_le hx
  have hy0 : 0 < y := ha.trans_le hy
  -- `log x - log y = log (x / y) ≤ x / y - 1 = (x - y) / y`.
  have hlog : log x - log y ≤ (x - y) / y := by
    rw [← log_div hx0.ne' hy0.ne', sub_div, div_self hy0.ne']
    exact log_le_sub_one_of_pos (div_pos hx0 hy0)
  have hdiv : (x - y) / y ≤ a⁻¹ * dist x y := by
    rcases le_total x y with hxy | hxy
    · exact (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hxy) hy0.le).trans
        (by positivity)
    · rw [dist_eq, abs_of_nonneg (sub_nonneg.2 hxy), inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (sub_nonneg.2 hxy) ha hy
  linarith

end Real

/-- **The logarithm of a `K`-Lipschitz function bounded below by `a > 0` is `a⁻¹ K`-Lipschitz.** -/
theorem LipschitzWith.log {α : Type*} [PseudoEMetricSpace α] {K : NNReal} {g : α → ℝ} {a : ℝ}
    (hg : LipschitzWith K g) (ha : 0 < a) (hga : ∀ x, a ≤ g x) :
    LipschitzWith (Real.toNNReal a⁻¹ * K) fun x => Real.log (g x) :=
  lipschitzOnWith_univ.1 <|
    (Real.lipschitzOnWith_log_Ici ha).comp hg.lipschitzOnWith fun x _ => hga x

namespace Real

/-- The function `t ↦ log (max 1 t)` is `1`-Lipschitz. -/
theorem lipschitzWith_log_max_one : LipschitzWith 1 fun t : ℝ => log (max 1 t) := by
  simpa using (LipschitzWith.id.const_max 1).log one_pos fun t => le_max_left 1 t

end Real
