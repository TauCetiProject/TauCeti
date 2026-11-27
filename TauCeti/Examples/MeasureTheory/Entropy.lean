/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Integral.Entropy.Product
import TauCeti.InformationTheory.KullbackLeibler.Convex

/-!
# Regression examples for functional entropy

The log-sum inequality applies to equal a.e. nonnegative integrable densities without a separate
`x log x` integrability assumption. Product subadditivity applies to zero total mass and needs no
marginal hypotheses for finite factors.
-/

open scoped ENNReal
open MeasureTheory MeasureTheory.Measure

example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ ↦ c) = 0 := by
  simp

example {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (g : α → ℝ) : entropy (dirac a) g = 0 := by
  simp

example {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (c : ℝ≥0∞) (g : α → ℝ) :
    entropy (c • dirac a) g = -(c.toReal * g a) * Real.log c.toReal := by
  simp [entropy_smul_measure]

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ) :
    entropy (ν.prod μ) (g ∘ Prod.swap) = entropy (μ.prod ν) g := by
  rw [← measurePreserving_swap.map_eq]
  have hswap : MeasurableEmbedding (Prod.swap : α × β → β × α) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [entropy_map hswap]
  simp [Function.comp_def]

example {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (∫ x, f x ∂μ) * Real.log ((∫ x, f x ∂μ) / (∫ x, f x ∂μ)) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (f x) ∂μ := by
  apply integral_log_sum_le μ hf hf (by filter_upwards with x hx; exact hx) hfi hfi
  simpa only [sub_self] using (integrable_fun_zero α ℝ μ)

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α × β → ℝ) (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ entropy ν (fun y ↦ g (x, y))) μ ∧
      Integrable (fun y ↦ entropy μ (fun x ↦ g (x, y))) ν :=
  ⟨integrable_entropy_prod_left μ ν g hlog (integrable_marginal_mul_log_left μ ν hg hlog),
    integrable_entropy_prod_right μ ν g hlog (integrable_marginal_mul_log_right μ ν hg hlog)⟩

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α × β → ℝ) (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) :=
  entropy_prod_eq μ ν g hg hlog (integrable_marginal_mul_log_left μ ν hg hlog)

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
