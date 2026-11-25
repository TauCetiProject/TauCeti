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

The same argument compares two sequences of probability measures (the replacement principle):
if the potentials of `μs n` and `νs n` become asymptotically equal at almost every point, then the
integrals of every continuous compactly supported function against `μs n` and `νs n` become
asymptotically equal, and a weak limit of `νs n` is a weak limit of `μs n`. No tightness or moment
bound is needed beyond the finite logarithmic moment of each measure.

## Main results

* `ProbabilityMeasure.tendsto_integral_sub_integral_of_ae_tendsto_logarithmicPotential_sub`: the
  replacement principle for vague convergence.
* `ProbabilityMeasure.tendsto_of_tendsto_of_ae_tendsto_logarithmicPotential_sub`: the replacement
  principle with a weak limit.
* `ProbabilityMeasure.tendsto_of_ae_tendsto_logarithmicPotential`: the logarithmic-potential
  continuity theorem.

## References

* T. Tao, *Topics in Random Matrix Theory*, Theorem 2.8.3, the continuity theorem.
* T. Tao, V. Vu, *Random matrices: universality of ESDs and the circular law*, with an appendix
  by M. Krishnapur, Ann. Probab. 38 (2010); arXiv:0807.4898, Theorem 2.1 and §3.6. Their
  replacement principle is
  stated for normalized log-determinants of random matrices and also assumes Frobenius bounds,
  which supply the uniform integrability of their argument. The alternate argument of §3.6, which
  they credit to Krishnapur, tests the difference of potentials against a Laplacian, as here;
  the two-point differences of normalized potentials make the Frobenius bounds unnecessary.
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
    {μs νs : ℕ → ProbabilityMeasure ℂ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ σ : ProbabilityMeasure ℂ,
      eLpNorm (σ : Measure ℂ).normalizedLogarithmicPotential 2 ν ≤ C)
    (hν : ν ≪ (volume : Measure ℂ)) {c : ℕ → ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z -
        (νs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℂ × ℂ ↦
        ((μs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (μs n : Measure ℂ).normalizedLogarithmicPotential p.2) -
        ((νs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (νs n : Measure ℂ).normalizedLogarithmicPotential p.2)) 1 (ν.prod ν)) atTop (𝓝 0) := by
  let u (σ : ProbabilityMeasure ℂ) (p : ℂ × ℂ) :=
    (σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
    (σ : Measure ℂ).normalizedLogarithmicPotential p.2
  have hLp (σ : ProbabilityMeasure ℂ) : MemLp (u σ) 2 (ν.prod ν) :=
    memLp_iff.mpr ((eLpNorm_normalizedPotential_sub_le (hbound σ)).trans_lt (by finiteness))
  have hlim := tendsto_Lp_finite_of_tendsto_ae (p := 1) (g := 0)
    (f := fun n (p : ℂ × ℂ) ↦ ((μs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
      (μs n : Measure ℂ).normalizedLogarithmicPotential p.2) -
      ((νs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (νs n : Measure ℂ).normalizedLogarithmicPotential p.2)) (by norm_num) (by norm_num)
    (fun n ↦ ((hLp (μs n)).sub (hLp (νs n))).aestronglyMeasurable) MemLp.zero ?_ ?_
  · simpa only [sub_zero] using hlim
  · refine unifIntegrable_of_eLpNorm_le (by norm_num : (1 : ℝ≥0∞) < 2)
      (C := (C + C) + (C + C)) (by finiteness) fun n ↦ (eLpNorm_sub_le (by norm_num)).trans ?_
    exact add_le_add (eLpNorm_normalizedPotential_sub_le (hbound (μs n)))
      (eLpNorm_normalizedPotential_sub_le (hbound (νs n)))
  · have hν' := hν.ae_le h
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hν',
      measurePreserving_snd.quasiMeasurePreserving.ae hν'] with p h1 h2
    have h12 := h1.sub h2
    rw [sub_zero] at h12
    exact h12.congr fun n ↦ by ring

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

/-- The normalized potentials of all probability measures are uniformly bounded in `L²` of the
uniform law on a closed ball of radius at least one. -/
private theorem exists_eLpNorm_normalizedPotential_cond_le (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ σ : ProbabilityMeasure ℂ,
      eLpNorm (σ : Measure ℂ).normalizedLogarithmicPotential 2
        (ProbabilityTheory.cond volume (closedBall (0 : ℂ) (max 1 R))) ≤ C := by
  let s := closedBall (0 : ℂ) (max 1 R)
  have hs : volume s ≠ 0 := (measure_closedBall_pos volume 0 (by positivity : 0 < max 1 R)).ne'
  have hν : ProbabilityTheory.cond volume s = (volume s)⁻¹ • volume.restrict s := rfl
  obtain ⟨C, hC, hbound⟩ := Measure.exists_eLpNorm_normalizedLogarithmicPotential_le (max 1 R)
  refine ⟨C * (volume s)⁻¹ ^ (1 / 2 : ℝ), by finiteness, fun σ ↦ ?_⟩
  rw [hν, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _
    (σ : Measure ℂ).measurable_normalizedLogarithmicPotential.aestronglyMeasurable]
  simpa [mul_comm] using mul_le_mul' (hbound (σ : Measure ℂ))
    (le_refl ((volume s)⁻¹ ^ (1 / 2 : ℝ)))

private theorem tendsto_integral_sub_integral_contDiff_of_ae_tendsto_normalizedPotential_sub_add
    {μs νs : ℕ → ProbabilityMeasure ℂ} {c : ℕ → ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z -
        (νs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Tendsto (fun n ↦ ∫ z, f z ∂(μs n : Measure ℂ) - ∫ z, f z ∂(νs n : Measure ℂ)) atTop
      (𝓝 0) := by
  -- Test against `Δ f` on the uniform law `ν` of a ball containing its support.
  obtain ⟨R, hR⟩ := hc.laplacian.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let s := closedBall (0 : ℂ) (max 1 R)
  have hs : volume s ≠ 0 := (measure_closedBall_pos volume 0 (by positivity : 0 < max 1 R)).ne'
  have hfin : volume s ≠ ∞ := (isCompact_closedBall 0 (max 1 R)).measure_lt_top.ne
  let ν := ProbabilityTheory.cond volume s
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hs hfin
  obtain ⟨C, hC, hLp⟩ := exists_eLpNorm_normalizedPotential_cond_le R
  have hpot := tendsto_eLpNorm_normalizedPotential_sub hC hLp
    ProbabilityTheory.cond_absolutelyContinuous h
  have hsub : tsupport (Δ f) ⊆ s := hR.trans (closedBall_subset_closedBall (le_max_right _ _))
  obtain ⟨B, hB⟩ := hf.continuous_laplacian.bounded_above_of_compact_support hc.laplacian
  have hi (σ : ProbabilityMeasure ℂ) : Integrable (fun p : ℂ × ℂ ↦
      (σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (σ : Measure ℂ).normalizedLogarithmicPotential p.2) (ν.prod ν) :=
    (memLp_iff.mpr ((eLpNorm_normalizedPotential_sub_le (hLp σ)).trans_lt
      (by finiteness : _ < ∞))).integrable (by norm_num)
  have hΔ : AEStronglyMeasurable (fun p : ℂ × ℂ ↦ Δ f p.1) (ν.prod ν) :=
    (hf.continuous_laplacian.measurable.comp measurable_fst).aestronglyMeasurable
  have htest := tendsto_integral_mul_of_tendsto_eLpNorm (v := 0)
    (u := fun n (p : ℂ × ℂ) ↦ ((μs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
      (μs n : Measure ℂ).normalizedLogarithmicPotential p.2) -
      ((νs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (νs n : Measure ℂ).normalizedLogarithmicPotential p.2))
    (.of_forall fun n ↦ (hi (μs n)).sub (hi (νs n))) (integrable_zero _ _ _) hΔ
    (ae_of_all _ fun p ↦ hB p.1) (by simpa only [sub_zero] using hpot)
  -- Testing the two-point differences against `Δ f` recovers the integrals of `f`.
  let K := ((volume s)⁻¹).toReal * (2 * Real.pi)
  have hpair (σ : ProbabilityMeasure ℂ) :
      ∫ p : ℂ × ℂ, Δ f p.1 * ((σ : Measure ℂ).normalizedLogarithmicPotential p.1 -
        (σ : Measure ℂ).normalizedLogarithmicPotential p.2) ∂ν.prod ν =
        K * ∫ z, f z ∂(σ : Measure ℂ) :=
    integral_laplacian_mul_normalizedPotential_sub_cond hf hc hsub hs hfin σ hB
      ((memLp_iff.mpr ((hLp σ).trans_lt hC.lt_top)).integrable (by norm_num))
  have hsplit (n : ℕ) : ∫ p : ℂ × ℂ, Δ f p.1 *
      (((μs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (μs n : Measure ℂ).normalizedLogarithmicPotential p.2) -
        ((νs n : Measure ℂ).normalizedLogarithmicPotential p.1 -
          (νs n : Measure ℂ).normalizedLogarithmicPotential p.2)) ∂ν.prod ν =
      K * (∫ z, f z ∂(μs n : Measure ℂ) - ∫ z, f z ∂(νs n : Measure ℂ)) := by
    rw [mul_sub, ← hpair (μs n), ← hpair (νs n), ← integral_sub
      ((hi (μs n)).bdd_mul hΔ (ae_of_all _ fun p ↦ hB p.1))
      ((hi (νs n)).bdd_mul hΔ (ae_of_all _ fun p ↦ hB p.1))]
    simp only [mul_sub]
  simp only [hsplit, Pi.zero_apply, mul_zero, integral_zero] at htest
  have hne : K ≠ 0 := by
    dsimp only [K]
    rw [ENNReal.toReal_inv]
    positivity [ENNReal.toReal_pos hs hfin, Real.pi_pos]
  exact (tendsto_const_smul_iff₀ hne).1 (by simpa only [smul_eq_mul, mul_zero] using htest)

/-- **Replacement principle**, normalized form. If, at almost every point, the normalized
potentials of `μs n` and `νs n` differ by additive constants up to an error tending to zero, then
`μs n - νs n` tends to zero vaguely: the integrals of every continuous compactly supported function
against `μs n` and `νs n` become asymptotically equal. No moment or tightness condition is
needed. -/
theorem tendsto_integral_sub_integral_of_ae_tendsto_normalizedLogarithmicPotential_sub_add
    {μs νs : ℕ → ProbabilityMeasure ℂ} {c : ℕ → ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z -
        (νs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n ↦ ∫ z, f z ∂(μs n : Measure ℂ) - ∫ z, f z ∂(νs n : Measure ℂ)) atTop
      (𝓝 0) :=
  tendsto_integral_sub_integral_of_forall_contDiff_hasCompactSupport (fun _ hg hgc ↦
    tendsto_integral_sub_integral_contDiff_of_ae_tendsto_normalizedPotential_sub_add h
      (hg.of_le (by norm_num)) hgc) hf hc

/-- **Replacement principle** for probability measures on the plane with finite logarithmic
moments. If the logarithmic potentials of `μs n` and `νs n` become asymptotically equal at almost
every point, then the integrals of every continuous compactly supported function against `μs n`
and `νs n` become asymptotically equal.

This is the conclusion of the replacement principle of Tao and Vu, with the potentials in place of
normalized log-determinants. -/
theorem tendsto_integral_sub_integral_of_ae_tendsto_logarithmicPotential_sub
    {μs νs : ℕ → ProbabilityMeasure ℂ}
    (hμ : ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μs n : Measure ℂ))
    (hν : ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (νs n : Measure ℂ))
    (h : ∀ᵐ z ∂volume, Tendsto (fun n ↦ (μs n : Measure ℂ).logarithmicPotential z -
      (νs n : Measure ℂ).logarithmicPotential z) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n ↦ ∫ z, f z ∂(μs n : Measure ℂ) - ∫ z, f z ∂(νs n : Measure ℂ)) atTop
      (𝓝 0) := by
  have hμ' := ae_all_iff.2 fun n ↦
    (μs n : Measure ℂ).logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add (hμ n)
  have hν' := ae_all_iff.2 fun n ↦
    (νs n : Measure ℂ).logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add (hν n)
  refine tendsto_integral_sub_integral_of_ae_tendsto_normalizedLogarithmicPotential_sub_add
    (c := fun n ↦ ∫ w, Real.posLog ‖w‖ ∂(μs n : Measure ℂ) -
      ∫ w, Real.posLog ‖w‖ ∂(νs n : Measure ℂ)) ?_ hf hc
  filter_upwards [hμ', hν', h] with z hμz hνz hz
  refine hz.congr fun n ↦ ?_
  rw [hμz n, hνz n]
  ring

/-- **Replacement principle** with a limit. If `νs n` converges weakly to a probability measure
`μ` and the logarithmic potentials of `μs n` and `νs n` become asymptotically equal at almost every
point, then `μs n` also converges weakly to `μ`. -/
theorem tendsto_of_tendsto_of_ae_tendsto_logarithmicPotential_sub
    {μs νs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    (hμ : ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μs n : Measure ℂ))
    (hν : ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (νs n : Measure ℂ))
    (hlim : Tendsto νs atTop (𝓝 μ))
    (h : ∀ᵐ z ∂volume, Tendsto (fun n ↦ (μs n : Measure ℂ).logarithmicPotential z -
      (νs n : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_forall_tendsto_integral_contDiff_hasCompactSupport fun f hf hc ↦ ?_
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hνf := tendsto_iff_forall_integral_tendsto.1 hlim
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous B hB)
  simpa using (tendsto_integral_sub_integral_of_ae_tendsto_logarithmicPotential_sub hμ hν h
    hf.continuous hc).add hνf

/-- Weak convergence follows from almost-everywhere convergence of the normalized potentials
up to additive constants. The constants can depend on the index. -/
theorem tendsto_of_ae_tendsto_normalizedLogarithmicPotential_add
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}
    {c : ℕ → ℝ} {d : ℝ}
    (h : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ (μs n : Measure ℂ).normalizedLogarithmicPotential z + c n) atTop
        (𝓝 ((μ : Measure ℂ).normalizedLogarithmicPotential z + d))) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_forall_tendsto_integral_contDiff_hasCompactSupport fun f hf hc ↦ ?_
  refine tendsto_sub_nhds_zero_iff.1
    (tendsto_integral_sub_integral_contDiff_of_ae_tendsto_normalizedPotential_sub_add
      (νs := fun _ ↦ μ) (c := fun n ↦ c n - d) ?_ (hf.of_le (by norm_num)) hc)
  filter_upwards [h] with z hz
  have hz' := hz.sub_const ((μ : Measure ℂ).normalizedLogarithmicPotential z + d)
  rw [sub_self] at hz'
  exact hz'.congr fun n ↦ by ring

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
