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
  · have h : (fun x : E ↦ Real.log ‖x‖) = fun _ ↦ 0 := by
      funext x
      rw [Subsingleton.elim x 0, norm_zero, Real.log_zero]
    rw [h]
    exact locallyIntegrable_const 0
  -- Dominate `|log ‖x‖|` by `2 ‖x‖ ^ (-1 / 2) + ‖x‖`.
  have hpow : LocallyIntegrable (fun x : E ↦ 2 * ‖x‖ ^ (-(1 / 2 : ℝ))) μ := by
    refine locallyIntegrable_of_norm_le_rpow Module.finrank_pos (C := 2) (α := 1 / 2) ?_
      (Filter.Eventually.of_forall fun x ↦ ?_)
      ((measurable_norm.pow_const _).const_mul 2).aestronglyMeasurable
    · have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
      linarith
    · rw [Real.norm_of_nonneg (by positivity)]
  refine (hpow.add continuous_norm.locallyIntegrable).mono
    (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
  -- `-2 ‖x‖ ^ (-1 / 2) ≤ log ‖x‖ ≤ ‖x‖`.
  have hlow := Real.neg_rpow_div_le_log (norm_nonneg x) (ε := 1 / 2) (by norm_num)
  have hup := Real.log_le_rpow_div (norm_nonneg x) (ε := 1) one_pos
  rw [Real.rpow_one, div_one] at hup
  have hpow : 0 ≤ ‖x‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg x) _
  rw [abs_le]
  constructor <;> linarith [norm_nonneg x]

end TauCeti
