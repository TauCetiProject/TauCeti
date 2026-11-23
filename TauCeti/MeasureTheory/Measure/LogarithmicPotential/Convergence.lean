/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Basic

import Mathlib.Probability.ConditionalProbability
import TauCeti.MeasureTheory.Measure.Portmanteau
import TauCeti.MeasureTheory.Function.UniformIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Lp
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# Weak convergence from logarithmic potentials

Almost-everywhere convergence of the logarithmic potentials of probability measures
on the complex plane implies weak convergence to the probability measure with the limiting
potential. Each measure may have its own finite logarithmic moment. To obtain a uniform
local bound without any uniform moment condition, take differences between potentials
evaluated at two points. The differences are unchanged by normalizing the potentials,
and testing against a Laplacian removes the constant.

This is the logarithmic-potential continuity theorem of T. Tao, *Topics in Random Matrix
Theory*, Theorem 2.8.3, expressed for probability measures.
-/

public section

open Filter InnerProductSpace MeasureTheory Metric Set Topology
open scoped ENNReal Laplacian

namespace MeasureTheory

namespace ProbabilityMeasure

open Measure

private theorem eLpNorm_normalizedPotential_sub_le {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {μ : ProbabilityMeasure ℂ} {C : ℝ≥0∞}
    (h : eLpNorm (μ : Measure ℂ).normalizedLogarithmicPotential 2 ν ≤ C) :
    eLpNorm (fun p : ℂ × ℂ ↦ (μ : Measure ℂ).normalizedLogarithmicPotential p.1 -
      (μ : Measure ℂ).normalizedLogarithmicPotential p.2) 2 (ν.prod ν) ≤ C + C := by
  let u := (μ : Measure ℂ).normalizedLogarithmicPotential
  have hm : Measurable u := (μ : Measure ℂ).measurable_normalizedLogarithmicPotential
  have hfst := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    hm.aestronglyMeasurable (measurePreserving_fst (μ := ν) (ν := ν))
  have hsnd := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    hm.aestronglyMeasurable (measurePreserving_snd (μ := ν) (ν := ν))
  calc
    _ ≤ eLpNorm (u ∘ Prod.fst) 2 (ν.prod ν) + eLpNorm (u ∘ Prod.snd) 2 (ν.prod ν) :=
      eLpNorm_sub_le (by norm_num)
    _ ≤ _ := by rw [hfst, hsnd]; exact add_le_add h h

private theorem tendsto_eLpNorm_normalizedPotential_sub {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ σ : ProbabilityMeasure ℂ,
      eLpNorm (σ : Measure ℂ).normalizedLogarithmicPotential 2 ν ≤ C)
    (hν : ν ≪ (volume : Measure ℂ))
    {c : ℕ → ℝ} {d : ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop
        (𝓝 ((μ : Measure ℂ).normalizedLogarithmicPotential z + d))) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℂ × ℂ ↦
        ((μs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (μs n : Measure ℂ).normalizedLogarithmicPotential p.2) -
        ((μ : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (μ : Measure ℂ).normalizedLogarithmicPotential p.2)) 1 (ν.prod ν)) atTop (𝓝 0) := by
  let u (σ : ProbabilityMeasure ℂ) (p : ℂ × ℂ) :=
    (σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
    (σ : Measure ℂ).normalizedLogarithmicPotential p.2
  have hLp (σ : ProbabilityMeasure ℂ) : MemLp (u σ) 2 (ν.prod ν) :=
    memLp_iff.mpr ((eLpNorm_normalizedPotential_sub_le (hbound σ)).trans_lt (by finiteness))
  refine tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n ↦ (hLp (μs n)).aestronglyMeasurable) ((hLp μ).mono_exponent (by norm_num)) ?_ ?_
  · exact unifIntegrable_of_eLpNorm_le (by norm_num : (1 : ℝ≥0∞) < 2)
      (ENNReal.add_ne_top.2 ⟨hC, hC⟩) (fun n ↦ eLpNorm_normalizedPotential_sub_le (hbound (μs n)))
  · have hν' := hν.ae_le h
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hν',
      measurePreserving_snd.quasiMeasurePreserving.ae hν'] with p h1 h2
    simpa only [add_sub_add_right_eq_sub, u] using h1.sub h2

private theorem integral_laplacian_mul_normalizedPotential_sub_cond
    {s : Set ℂ} {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hsub : tsupport (Δ f) ⊆ s) (hs : volume s ≠ 0) (hfin : volume s ≠ ∞)
    (σ : ProbabilityMeasure ℂ) {B : ℝ} (hB : ∀ z, ‖Δ f z‖ ≤ B)
    (hu : Integrable (σ : Measure ℂ).normalizedLogarithmicPotential
      (ProbabilityTheory.cond volume s)) :
    let ν := ProbabilityTheory.cond volume s
    ∫ p : ℂ × ℂ, Δ f p.1 * ((σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
      (σ : Measure ℂ).normalizedLogarithmicPotential p.2) ∂ν.prod ν =
      (((volume s)⁻¹).toReal * (2 * Real.pi)) * ∫ z, f z ∂(σ : Measure ℂ) := by
  let ν := ProbabilityTheory.cond volume s
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hs hfin
  have hrestrict (u : ℂ → ℝ) :
      ∫ z, Δ f z * u z ∂ν = ((volume s)⁻¹).toReal * ∫ z, Δ f z * u z := by
    have hν : ν = (volume s)⁻¹ • volume.restrict s := rfl
    rw [hν, integral_smul_measure, smul_eq_mul, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    have hz' : Δ f z = 0 :=
      Function.notMem_support.mp fun h ↦ hz (hsub (subset_tsupport _ h))
    simp only [hz', zero_mul]
  have hvzero : ∫ z, Δ f z ∂ν = 0 := by
    have hvanish := TauCeti.integral_laplacian_eq_zero_of_hasCompactSupport (μ := volume) hf hc
    simpa [hvanish] using hrestrict (fun _ ↦ 1)
  have hΔ : Integrable (Δ f) ν :=
    Integrable.of_bound hf.continuous_laplacian.aestronglyMeasurable B (ae_of_all _ hB)
  have hmul : Integrable (fun z ↦ Δ f z * (σ : Measure ℂ).normalizedLogarithmicPotential z) ν :=
    hu.bdd_mul hf.continuous_laplacian.aestronglyMeasurable (ae_of_all _ hB)
  dsimp only
  rw [integral_mul_sub_comp_prod_eq_sub hΔ hu hmul, hvzero, zero_mul, sub_zero,
    hrestrict, (σ : Measure ℂ).integral_laplacian_mul_normalizedLogarithmicPotential hf hc]
  ring

private theorem tendsto_integral_contDiff_of_ae_tendsto_normalizedLogarithmicPotential_add
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    {c : ℕ → ℝ} {d : ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop
        (𝓝 ((μ : Measure ℂ).normalizedLogarithmicPotential z + d)))
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Tendsto (fun n ↦ ∫ z, f z ∂(μs n : Measure ℂ)) atTop (𝓝 (∫ z, f z ∂(μ : Measure ℂ))) := by
  obtain ⟨R, hR⟩ := hc.laplacian.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let s := closedBall (0 : ℂ) (max 1 R)
  have hs : volume s ≠ 0 := (measure_closedBall_pos volume 0 (by positivity : 0 < max 1 R)).ne'
  have hfin : volume s ≠ ∞ := (isCompact_closedBall 0 (max 1 R)).measure_lt_top.ne
  let ν := ProbabilityTheory.cond volume s
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hs hfin
  have hν : ν = (volume s)⁻¹ • volume.restrict s := rfl
  have hνac : ν ≪ volume := ProbabilityTheory.cond_absolutelyContinuous
  obtain ⟨C, hC, hbound⟩ := Measure.exists_eLpNorm_normalizedLogarithmicPotential_le (max 1 R)
  have hC' : C * (volume s)⁻¹ ^ (1 / 2 : ℝ) ≠ ∞ := by finiteness
  have hLp (σ : ProbabilityMeasure ℂ) :
      eLpNorm (σ : Measure ℂ).normalizedLogarithmicPotential 2 ν ≤
        C * (volume s)⁻¹ ^ (1 / 2 : ℝ) := by
    rw [hν, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _
      (σ : Measure ℂ).measurable_normalizedLogarithmicPotential.aestronglyMeasurable]
    simpa [mul_comm] using mul_le_mul' (hbound (σ : Measure ℂ))
      (le_refl ((volume s)⁻¹ ^ (1 / 2 : ℝ)))
  have hpot := tendsto_eLpNorm_normalizedPotential_sub hC' hLp hνac h
  have hsub : tsupport (Δ f) ⊆ s := hR.trans (closedBall_subset_closedBall (le_max_right _ _))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (max 1 R)).exists_bound_of_continuousOn
    hf.continuous_laplacian.continuousOn
  have hB' (z : ℂ) : ‖Δ f z‖ ≤ max B 0 := by
    by_cases hz : z ∈ s
    · exact (hB z hz).trans (le_max_left _ _)
    · have hz' : Δ f z = 0 :=
        Function.notMem_support.mp fun h ↦ hz (hsub (subset_tsupport _ h))
      simp [hz']
  have hi (σ : ProbabilityMeasure ℂ) : Integrable (fun p : ℂ × ℂ ↦
      (σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (σ : Measure ℂ).normalizedLogarithmicPotential p.2) (ν.prod ν) :=
    (memLp_iff.mpr ((eLpNorm_normalizedPotential_sub_le (hLp σ)).trans_lt
      (by finiteness : _ < ∞))).integrable (by norm_num)
  have htest := tendsto_integral_mul_of_tendsto_eLpNorm (.of_forall fun n ↦ hi (μs n)) (hi μ)
    (hf.continuous_laplacian.measurable.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ fun p ↦ hB' p.1) hpot
  have hpair (σ : ProbabilityMeasure ℂ) :
      ∫ p : ℂ × ℂ, Δ f p.1 * ((σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (σ : Measure ℂ).normalizedLogarithmicPotential p.2) ∂ν.prod ν =
        (((volume s)⁻¹).toReal * (2 * Real.pi)) * ∫ z, f z ∂(σ : Measure ℂ) :=
    integral_laplacian_mul_normalizedPotential_sub_cond hf hc hsub hs hfin σ hB'
      ((memLp_iff.mpr ((hLp σ).trans_lt hC'.lt_top)).integrable (by norm_num))
  simp only [Function.comp_apply, hpair] at htest
  have hne : ((volume s)⁻¹).toReal * (2 * Real.pi) ≠ 0 := by
    rw [ENNReal.toReal_inv]
    positivity [ENNReal.toReal_pos hs hfin, Real.pi_pos]
  exact (tendsto_const_smul_iff₀ hne).1 htest

/-- Weak convergence follows from almost-everywhere convergence of the normalized potentials
up to additive constants. The constants can depend on the index. -/
theorem tendsto_of_ae_tendsto_normalizedLogarithmicPotential_add
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    {c : ℕ → ℝ} {d : ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop
        (𝓝 ((μ : Measure ℂ).normalizedLogarithmicPotential z + d))) :
    Tendsto μs atTop (𝓝 μ) :=
  tendsto_of_forall_tendsto_integral_contDiff_hasCompactSupport fun _ ↦
    fun hf ↦ tendsto_integral_contDiff_of_ae_tendsto_normalizedLogarithmicPotential_add h
      (hf.of_le (by norm_num))

/-- Logarithmic-potential continuity theorem on the plane. Almost-everywhere convergence
of the potentials implies weak convergence when the limiting potential is that of a
probability measure. Each measure has a finite logarithmic moment. -/
theorem tendsto_of_ae_tendsto_logarithmicPotential
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    (hm : ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μs n : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, Tendsto (fun n ↦ (μs n : Measure ℂ).logarithmicPotential z)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential z))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hseq := ae_all_iff.2 fun n ↦
    (μs n : Measure ℂ).logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add (hm n)
  have hlim := (μ : Measure ℂ).logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add hμ
  apply tendsto_of_ae_tendsto_normalizedLogarithmicPotential_add
    (c := fun n ↦ ∫ w, Real.posLog ‖w‖ ∂(μs n : Measure ℂ))
    (d := ∫ w, Real.posLog ‖w‖ ∂(μ : Measure ℂ))
  filter_upwards [hseq, hlim, h] with z hseqz hlimz hz
  simpa only [hseqz, hlimz] using hz

end ProbabilityMeasure
end MeasureTheory
