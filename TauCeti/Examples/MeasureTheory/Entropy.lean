/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Integral.Entropy.Product

/-!
# Regression examples for functional entropy

The log-sum inequality applies to equal densities without a separate `x log x` integrability
assumption. Product subadditivity applies to zero total mass and needs no marginal hypotheses
for probability factors.
-/

open MeasureTheory MeasureTheory.Measure

example {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (∫ x, f x ∂μ) * Real.log ((∫ x, f x ∂μ) / (∫ x, f x ∂μ)) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (f x) ∂μ := by
  apply integral_log_sum_le μ hf hf (by filter_upwards with x hx; exact hx) hfi hfi
  simpa only [sub_self] using (integrable_fun_zero α ℝ μ)

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    entropy (μ.prod ν) (fun _ ↦ 0) ≤
      (∫ _ : α, entropy ν (fun _ ↦ 0) ∂μ) + ∫ _ : β, entropy μ (fun _ ↦ 0) ∂ν := by
  apply entropy_prod_le μ ν (fun _ ↦ 0)
  · filter_upwards with _
    simp
  · exact integrable_fun_zero (α × β) ℝ (μ.prod ν)
  · simp
