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
for finite factors.
-/

open MeasureTheory MeasureTheory.Measure

example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ ↦ c) = 0 := by
  simp

example {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (g : α → ℝ) : entropy (dirac a) g = 0 := by
  simp

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ) :
    entropy (ν.prod μ) (g ∘ Prod.swap) = entropy (μ.prod ν) g :=
  entropy_prod_swap μ ν g

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

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] :
    entropy (μ.prod (0 : Measure β)) (fun _ ↦ 0) ≤
      (∫ _ : α, entropy (0 : Measure β) (fun _ ↦ 0) ∂μ) +
        ∫ _ : β, entropy μ (fun _ ↦ 0) ∂(0 : Measure β) := by
  apply entropy_prod_le μ (0 : Measure β) (fun _ ↦ 0)
  · filter_upwards with _
    simp
  · exact integrable_fun_zero (α × β) ℝ (μ.prod 0)
  · simp

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (a : α) (b : β) :
    entropy ((dirac a).prod (dirac b + dirac b)) (fun _ ↦ 1) ≤
      (∫ _ : α, entropy (dirac b + dirac b) (fun _ ↦ 1) ∂(dirac a)) +
        ∫ _ : β, entropy (dirac a) (fun _ ↦ 1) ∂(dirac b + dirac b) := by
  apply entropy_prod_le (dirac a) (dirac b + dirac b) (fun _ ↦ 1)
  · filter_upwards with _
    norm_num
  · exact integrable_const 1
  · simp

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α × β → ℝ) (hg : 0 ≤ᵐ[μ.prod ν] g)
    (hgi : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν :=
  entropy_prod_le μ ν g hg hgi hlog
