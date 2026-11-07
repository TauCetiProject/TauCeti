/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local integrability of `log ‖x‖`

On a finite-dimensional real normed space with an additive Haar measure, the function
`x ↦ log ‖x‖` is locally integrable. Its only singularity is at the origin, where it is dominated
by `‖x‖ ^ (-1 / 2)`, which is locally integrable in every positive dimension. In the plane this is
the local integrability of the logarithmic fundamental solution of the Laplacian.

## Main declarations

* `TauCeti.locallyIntegrable_log_norm`: `x ↦ log ‖x‖` is locally integrable.
-/

public section

namespace TauCeti

open MeasureTheory

/-- On a finite-dimensional real normed space with an additive Haar measure, `x ↦ log ‖x‖` is
locally integrable. -/
theorem locallyIntegrable_log_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun x : E ↦ Real.log ‖x‖) μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simpa [norm_of_subsingleton] using locallyIntegrable_const (μ := μ) (0 : ℝ)
  -- Dominate `|log ‖x‖|` by `2 ‖x‖ ^ (-1 / 2) + ‖x‖`.
  have hpow : LocallyIntegrable (fun x : E ↦ 2 * ‖x‖ ^ (-(1 / 2 : ℝ))) μ :=
    locallyIntegrable_of_norm_le_rpow (C := 2) (α := 1 / 2) Module.finrank_pos
      (by linarith [(Nat.one_le_cast (α := ℝ)).2 (Module.finrank_pos (R := ℝ) (M := E))])
      (.of_forall fun x ↦ by rw [Real.norm_of_nonneg (by positivity)])
      (by fun_prop : Measurable _).aestronglyMeasurable
  refine (hpow.add continuous_norm.locallyIntegrable).mono
    (by fun_prop : Measurable fun x : E ↦ Real.log ‖x‖).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, Pi.add_apply, Real.norm_of_nonneg (by positivity), abs_le]
  -- `-2 ‖x‖ ^ (-1 / 2) ≤ log ‖x‖ ≤ ‖x‖`.
  have hlow := Real.neg_rpow_div_le_log (norm_nonneg x) (ε := 1 / 2) (by norm_num)
  constructor <;> linarith [Real.log_le_self (norm_nonneg x), norm_nonneg x,
    Real.rpow_nonneg (norm_nonneg x) (-(1 / 2))]

end TauCeti
