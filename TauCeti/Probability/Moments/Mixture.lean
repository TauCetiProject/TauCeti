/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Integral.Bind
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Means and covariances of probability mixtures

A mixture's expectation is the expectation of its component means. Its covariance is the
expected component covariance plus the covariance of the component means; taking the same
observable twice gives the law of total variance.

The mixing measure is a probability measure and the components need be probability measures
only almost everywhere. Finite second moments of the mixture imply the required integrability
of component means and covariances. The covariance formula applies to any pair of real
observables, including coordinates of a vector-valued law.

The integration steps use Mathlib's kernel-composition theory through
`TauCeti.MeasureTheory.Integral.Bind`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {K : α → Measure β}
  {X Y : β → ℝ}

/-- Component means of a square-integrable real observable are square-integrable under the
mixing law, even when the components are probability measures only almost everywhere. -/
theorem memLp_integral_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    MemLp (fun a ↦ ∫ x, X x ∂K a) 2 μ := by
  have hmean := hX.aestronglyMeasurable.integral_kernel_comp
    (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())
  simp only [Kernel.coe_mk, Kernel.const_apply] at hmean
  apply (memLp_two_iff_integrable_sq hmean).mpr
  obtain ⟨hae, hsecond⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  simp only [Real.norm_eq_abs, sq_abs] at hsecond
  refine hsecond.mono' (hmean.pow 2) ?_
  filter_upwards [hprob, hae] with a hpa hXa
  have hvar := variance_nonneg X (K a)
  rw [variance_eq_sub hXa] at hvar
  simpa only [Real.norm_of_nonneg (sq_nonneg _), Pi.pow_apply] using sub_nonneg.mp hvar

/-- The component covariances of two square-integrable observables are integrable under the
mixing law. -/
theorem integrable_covariance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    Integrable (fun a ↦ covariance X Y (K a)) μ := by
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans := (memLp_integral_bind hK hprob hX).integrable_mul
    (memLp_integral_bind hK hprob hY)
  simp only [Pi.mul_apply] at hprod hmeans
  refine (hprod.sub hmeans).congr ?_
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
  filter_upwards [hprob, hXae, hYae] with a hpa hXa hYa
  exact (covariance_eq_sub hXa hYa).symm

variable [IsProbabilityMeasure μ]

/-- **Law of total covariance**: a probability mixture's covariance is the sum of the expected
component covariance and the covariance of component means. -/
theorem covariance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    covariance X Y (μ.bind K) =
      (∫ a, covariance X Y (K a) ∂μ) +
        covariance (fun a ↦ ∫ x, X x ∂K a) (fun a ↦ ∫ x, Y x ∂K a) μ := by
  have : IsProbabilityMeasure (μ.bind K) := isProbabilityMeasure_bind hK.aemeasurable hprob
  have hmX := memLp_integral_bind hK hprob hX
  have hmY := memLp_integral_bind hK hprob hY
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans : Integrable (fun a ↦ (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) μ :=
    hmX.integrable_mul hmY
  have hcov : (fun a ↦ covariance X Y (K a)) =ᵐ[μ]
      (fun a ↦ (∫ x, X x * Y x ∂K a) - (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) := by
    obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
    obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
    filter_upwards [hprob, hXae, hYae] with a hpa hXa hYa
    exact covariance_eq_sub hXa hYa
  rw [covariance_eq_sub hX hY, covariance_eq_sub hmX hmY,
    integral_congr_ae hcov]
  simp only [Pi.mul_apply] at hprod hmeans ⊢
  have hXY : (∫ x, X x * Y x ∂μ.bind K) = ∫ a, ∫ x, X x * Y x ∂K a ∂μ :=
    Measure.integral_bind hK.aemeasurable (hX.integrable_mul hY)
  rw [integral_sub hprod hmeans, hXY,
    Measure.integral_bind hK.aemeasurable (hX.integrable one_le_two),
    Measure.integral_bind hK.aemeasurable (hY.integrable one_le_two)]
  ring

/-- **Law of total variance**: a probability mixture's variance is its expected component
variance plus the variance of the component means. -/
theorem variance_bind (hK : Measurable K)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    variance X (μ.bind K) = (∫ a, variance X (K a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂K a) μ := by
  have hae := hX.aestronglyMeasurable.comp (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())
  simp only [Kernel.coe_mk, Kernel.const_apply] at hae
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable, covariance_bind hK hprob hX hX,
    covariance_self (memLp_integral_bind hK hprob hX).aestronglyMeasurable.aemeasurable]
  congr 1
  exact integral_congr_ae (hae.mono fun a ha ↦ covariance_self ha.aemeasurable)

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} [IsProbabilityMeasure μ] {X Y : β → ℝ}

/-- The law of total covariance for the composition of a probability measure and a Markov
kernel. -/
theorem covariance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) (hY : MemLp Y 2 (κ ∘ₘ μ)) :
    covariance X Y (κ ∘ₘ μ) = (∫ a, covariance X Y (κ a) ∂μ) +
      covariance (fun a ↦ ∫ x, X x ∂κ a) (fun a ↦ ∫ x, Y x ∂κ a) μ := by
  exact TauCeti.Probability.covariance_bind κ.measurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX hY

/-- The law of total variance for the composition of a probability measure and a Markov
kernel. -/
theorem variance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) :
    variance X (κ ∘ₘ μ) = (∫ a, variance X (κ a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂κ a) μ := by
  exact TauCeti.Probability.variance_bind κ.measurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX

end ProbabilityTheory.Kernel
