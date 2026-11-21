/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Convergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Random logarithmic potentials

Convergence in probability at Lebesgue-almost every observation point implies convergence
in probability of every bounded continuous spectral statistic. The analogous almost-sure
statement gives almost-sure weak convergence of the random probability measures.

The passage from observation-point convergence in probability to the deterministic continuity
theorem uses convergence in measure on a product and subsequence extraction. A finite measure
equivalent to Lebesgue measure provides a common subsequence for the entire plane.
These are the probabilistic forms of T. Tao, *Topics in Random Matrix Theory*, Theorem 2.8.3.
-/

public section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

/-- Evaluation of the logarithmic potential is jointly measurable in the measure and the point. -/
@[fun_prop]
theorem measurable_logarithmicPotential :
    Measurable fun p : ProbabilityMeasure ℂ × ℂ ↦ (p.1 : Measure ℂ).logarithmicPotential p.2 := by
  let κ : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ × ℂ) ℂ :=
    ⟨fun p ↦ p.1, measurable_subtypeVal.comp measurable_fst⟩
  have hκ (p : ProbabilityMeasure ℂ × ℂ) : κ p = p.1 := (rfl)
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun p ↦ hκ p ▸ inferInstance⟩
  have h : Measurable fun q : (ProbabilityMeasure ℂ × ℂ) × ℂ ↦ Real.log ‖q.1.2 - q.2‖ := by
    fun_prop
  simpa only [Measure.logarithmicPotential_def, hκ] using
    (h.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}

private theorem ae_tendsto_of_ae_prod_tendsto_logarithmicPotential
    {ν : Measure ℂ} [SFinite ν] (hν : volume ≪ ν)
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ p ∂P.prod ν, Tendsto (fun n ↦ (X n p.1 : Measure ℂ).logarithmicPotential p.2)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential p.2))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 μ) := by
  filter_upwards [hm, Measure.ae_ae_of_ae_prod h] with ω hω hconv
  exact tendsto_of_ae_tendsto_logarithmicPotential hω hμ (hν.ae_le hconv)

private theorem ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_of_measurable [SFinite P]
    (hX : ∀ n, Measurable (X n))
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential z))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 μ) := by
  have hs : MeasurableSet {p : Ω × ℂ |
      Tendsto (fun n ↦ (X n p.1 : Measure ℂ).logarithmicPotential p.2)
        atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential p.2))} :=
    measurableSet_tendsto_fun
      (fun n ↦ measurable_logarithmicPotential.comp (((hX n).comp measurable_fst).prodMk
        measurable_snd))
      ((μ : Measure ℂ).measurable_logarithmicPotential.comp measurable_snd)
  exact ae_tendsto_of_ae_prod_tendsto_logarithmicPotential
    Measure.AbsolutelyContinuous.rfl hm hμ
    ((Measure.ae_prod_iff_ae_ae hs).2 ((Measure.ae_ae_comm hs).2 h))

private theorem tendstoInMeasure_integral_of_ae_tendstoInMeasure_logarithmicPotential_of_measurable
    [IsFiniteMeasure P]
    (hX : ∀ n, Measurable (X n))
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (fun _ ↦ (μ : Measure ℂ).logarithmicPotential z))
    (f : ℂ →ᵇ ℝ) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂(X n ω : Measure ℂ))
      atTop (fun _ ↦ ∫ z, f z ∂(μ : Measure ℂ)) := by
  let ν := (volume : Measure ℂ).toFinite
  let u (n : ℕ) (p : ℂ × Ω) := (X n p.2 : Measure ℂ).logarithmicPotential p.1
  let v (p : ℂ × Ω) := (μ : Measure ℂ).logarithmicPotential p.1
  have hu (n : ℕ) : Measurable (u n) :=
    measurable_logarithmicPotential.comp (((hX n).comp measurable_snd).prodMk measurable_fst)
  have hv : Measurable v := (μ : Measure ℂ).measurable_logarithmicPotential.comp measurable_fst
  have hprod : TendstoInMeasure (ν.prod P) u atTop v :=
    tendstoInMeasure_prod_of_ae_tendstoInMeasure
      (Eventually.of_forall fun n ↦ (hu n).edist hv) ((toFinite_absolutelyContinuous _).ae_le h)
  let F (σ : ProbabilityMeasure ℂ) := ∫ z, f z ∂(σ : Measure ℂ)
  have hF : Continuous F := continuous_integral_boundedContinuousFunction f
  let κ : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ) ℂ :=
    ⟨fun σ ↦ σ, measurable_subtypeVal⟩
  have hmeas : Measurable F :=
    (f.continuous.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n ↦ (hmeas.comp (hX n)).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ms, hms, hconv⟩ := (hprod.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  have hswap : ∀ᵐ p ∂P.prod ν,
      Tendsto (fun n ↦ (X (ns (ms n)) p.1 : Measure ℂ).logarithmicPotential p.2)
        atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential p.2)) :=
    (Measure.measurePreserving_swap (μ := P) (ν := ν)).quasiMeasurePreserving.ae hconv
  have ht := ae_tendsto_of_ae_prod_tendsto_logarithmicPotential
    (absolutelyContinuous_toFinite (volume : Measure ℂ))
    (hm.mono fun ω hω n ↦ hω (ns (ms n))) hμ hswap
  exact ht.mono fun ω hω ↦ hF.continuousAt.tendsto.comp hω

/-- Almost-sure convergence of the potentials at Lebesgue-almost every point implies almost-sure
weak convergence of the random measures. The logarithmic moments may be random and need
only be finite almost surely. -/
theorem ae_tendsto_of_ae_ae_tendsto_logarithmicPotential [SFinite P]
    (hX : ∀ n, AEMeasurable (X n) P)
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential z))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 μ) := by
  let Y (n : ℕ) := (hX n).mk (X n)
  have hXY : ∀ᵐ ω ∂P, ∀ n, X n ω = Y n ω := ae_all_iff.2 fun n ↦ (hX n).ae_eq_mk
  have hmY : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (Y n ω : Measure ℂ) := by
    filter_upwards [hm, hXY] with ω hω he
    simpa only [← he] using hω
  have hY : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Y n ω) atTop (𝓝 μ) := by
    apply ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_of_measurable
      (fun n ↦ (hX n).measurable_mk) hmY hμ
    filter_upwards [h] with z hz
    filter_upwards [hz, hXY] with ω hω he
    simpa only [he] using hω
  filter_upwards [hY, hXY] with ω hω he
  simpa only [← he] using hω

/-- Pointwise convergence in probability of the potentials for almost every observation point
implies convergence in probability of every bounded continuous test integral. -/
theorem tendstoInMeasure_integral_of_ae_tendstoInMeasure_logarithmicPotential [IsFiniteMeasure P]
    (hX : ∀ n, AEMeasurable (X n) P)
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (fun _ ↦ (μ : Measure ℂ).logarithmicPotential z))
    (f : ℂ →ᵇ ℝ) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂(X n ω : Measure ℂ))
      atTop (fun _ ↦ ∫ z, f z ∂(μ : Measure ℂ)) := by
  let Y (n : ℕ) := (hX n).mk (X n)
  have hXY : ∀ n, X n =ᵐ[P] Y n := fun n ↦ (hX n).ae_eq_mk
  have hmY : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (Y n ω : Measure ℂ) := by
    filter_upwards [hm, ae_all_iff.2 hXY] with ω hω he
    simpa only [← he] using hω
  have hY : ∀ᵐ z ∂volume, TendstoInMeasure P
      (fun n ω ↦ (Y n ω : Measure ℂ).logarithmicPotential z) atTop
      (fun _ ↦ (μ : Measure ℂ).logarithmicPotential z) := by
    filter_upwards [h] with z hz
    exact TendstoInMeasure.congr_left (fun n ↦ (hXY n).mono fun ω he ↦
      congrArg (fun σ : ProbabilityMeasure ℂ ↦ (σ : Measure ℂ).logarithmicPotential z) he) hz
  have ht := tendstoInMeasure_integral_of_ae_tendstoInMeasure_logarithmicPotential_of_measurable
    (fun n ↦ (hX n).measurable_mk) hmY hμ hY f
  exact TendstoInMeasure.congr_left (fun n ↦ (hXY n).symm.mono fun ω he ↦
    congrArg (fun σ : ProbabilityMeasure ℂ ↦ ∫ z, f z ∂(σ : Measure ℂ)) he) ht

end ProbabilityMeasure
end MeasureTheory
