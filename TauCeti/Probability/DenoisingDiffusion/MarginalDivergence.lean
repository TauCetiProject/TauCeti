/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Probability.DenoisingDiffusion.ForwardChain

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import TauCeti.InformationTheory.KullbackLeibler.ChainRule
import TauCeti.InformationTheory.KullbackLeibler.Gaussian

/-!
# Divergence of forward Gaussian noising marginals

A forward marginal is a mixture of isotropic Gaussian laws. The divergence of this mixture
from the standard Gaussian is bounded by the average of the divergences of its components.
Applying the Gaussian divergence formula gives a bound in terms of the initial second moment
and the cumulative signal level. For an initial law with finite second moment, the forward
marginals converge in Kullback–Leibler divergence to the standard Gaussian as the cumulative
signal tends to zero.

The bound uses `InformationTheory.klDiv_map_le` on the joint law of the input and noised output,
`TauCeti.klDiv_compProd_right` to average the conditional divergences, and
`TauCeti.klDiv_multivariateGaussian_smul_one` to evaluate them.

## References

* J. Ho, A. Jain and P. Abbeel, *Denoising diffusion probabilistic models*, NeurIPS 2020,
  equation (4) for the Gaussian components of the forward marginal.
-/

public section

open Filter InformationTheory MeasureTheory ProbabilityTheory
open scoped Real Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The divergence from the standard Gaussian after noising a fixed input with signal level
`a ∈ [0, 1)`. The two contributions are the rescaled input energy and the variance mismatch. -/
theorem klDiv_noiseKernel_stdGaussian {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (x : EuclideanSpace ℝ ι) :
    klDiv (noiseKernel a x) (stdGaussian (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal ((a * ‖x‖ ^ 2 - Fintype.card ι * a -
        Fintype.card ι * Real.log (1 - a)) / 2) := by
  classical
  have h := klDiv_multivariateGaussian_smul_one (√a • x) 0 (sub_pos.2 ha₁) zero_lt_one
  rw [one_smul] at h
  rw [noiseKernel_apply, ← multivariateGaussian_zero_one, h]
  simp only [div_one, mul_one, sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt ha₀]
  congr 1
  ring

/-- The divergence from the standard Gaussian of a noised probability law, bounded in terms of
an upper bound `M` on the initial second moment. -/
theorem klDiv_noiseKernel_comp_le (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a M : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hM : ∫ x, ‖x‖ ^ 2 ∂μ ≤ M)
    (hint : Integrable (fun x ↦ ‖x‖ ^ 2) μ) :
    klDiv (noiseKernel a ∘ₘ μ) (stdGaussian (EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal ((a * M - Fintype.card ι * a - Fintype.card ι * Real.log (1 - a)) / 2) := by
  let ν := stdGaussian (EuclideanSpace ℝ ι)
  have hν : (μ ⊗ₘ Kernel.const _ ν).map Prod.snd = ν := by
    simp [Measure.compProd_const]
  have hdata := klDiv_map_le (μ ⊗ₘ noiseKernel a) (μ ⊗ₘ Kernel.const _ ν) measurable_snd
  rw [hν, ← Measure.snd, Measure.snd_compProd, klDiv_compProd_right] at hdata
  simp only [Kernel.const_apply, ν, klDiv_noiseKernel_stdGaussian ha₀ ha₁] at hdata
  refine hdata.trans ?_
  set d := (Fintype.card ι : ℝ)
  let c := d * (-a - Real.log (1 - a))
  have hsplit (u : ℝ) : u - d * a - d * Real.log (1 - a) = u + c := by
    dsimp only [c]
    ring
  simp_rw [hsplit]
  have hpos : 0 ≤ -a - Real.log (1 - a) := by
    linarith [Real.log_le_sub_one_of_pos (sub_pos.2 ha₁)]
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) hpos
  have hscaled : Integrable (fun x ↦ a * ‖x‖ ^ 2) μ := hint.const_mul a
  have hf : Integrable (fun x ↦ (a * ‖x‖ ^ 2 + c) / 2) μ :=
    (hscaled.add (integrable_const c)).div_const 2
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun x ↦ by
      exact div_nonneg (add_nonneg (mul_nonneg ha₀ (sq_nonneg ‖x‖)) hc) (by norm_num)),
    integral_div, integral_add hscaled (integrable_const c), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  exact ENNReal.ofReal_le_ofReal (by gcongr)

variable {β : ℕ → ℝ}

/-- The divergence of the time-`t` marginal from the standard Gaussian is bounded in terms of
the initial second moment and the cumulative signal level, provided the latter is below one. -/
theorem klDiv_forwardMarginal_le (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hβ : ∀ s, 1 ≤ s → β s ≤ 1) {M : ℝ} (hM : ∫ x, ‖x‖ ^ 2 ∂μ ≤ M)
    (hint : Integrable (fun x ↦ ‖x‖ ^ 2) μ) {t : ℕ} (ht : alphaBar β t < 1) :
    klDiv (forwardMarginal μ β t) (stdGaussian (EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal ((alphaBar β t * M - Fintype.card ι * alphaBar β t -
        Fintype.card ι * Real.log (1 - alphaBar β t)) / 2) := by
  rw [forwardMarginal_def]
  exact klDiv_noiseKernel_comp_le μ (alphaBar_nonneg hβ t) ht hM hint

/-- For a probability law with finite second moment, the forward marginal divergences from
the standard Gaussian tend to zero when the cumulative signal tends to zero. -/
theorem tendsto_klDiv_forwardMarginal (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hβ : ∀ s, 1 ≤ s → β s ≤ 1) (hint : Integrable (fun x ↦ ‖x‖ ^ 2) μ)
    (hα : Tendsto (alphaBar β) atTop (𝓝 0)) :
    Tendsto (fun t ↦ klDiv (forwardMarginal μ β t) (stdGaussian (EuclideanSpace ℝ ι)))
      atTop (𝓝 0) := by
  let M := ∫ x, ‖x‖ ^ 2 ∂μ
  let B (a : ℝ) := ENNReal.ofReal
    ((a * M - Fintype.card ι * a - Fintype.card ι * Real.log (1 - a)) / 2)
  have hlog : ContinuousAt (fun a : ℝ ↦ Real.log (1 - a)) 0 :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp (by fun_prop)
  have hB : ContinuousAt B 0 := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    fun_prop
  have hlim : Tendsto (fun t ↦ B (alphaBar β t)) atTop (𝓝 0) := by
    simpa [B, Function.comp_def] using hB.tendsto.comp hα
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hα.eventually_lt_const zero_lt_one] with t ht
  exact klDiv_forwardMarginal_le μ hβ le_rfl hint ht

end TauCeti.Probability
