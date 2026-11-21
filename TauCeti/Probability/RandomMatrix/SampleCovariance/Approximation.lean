/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.Concentration

import TauCeti.Analysis.Matrix.SpectralMeasure.CovariancePerturbation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Separable
import TauCeti.Probability.Moments.BoundedApproximation
import TauCeti.Probability.RandomMatrix.Frobenius
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Bounded-entry reduction for sample covariance limits

The expected covariance spectral measures are stable under perturbations that are small
in mean squared error per entry. Testing with bounded Lipschitz functions of the square
roots of the covariance eigenvalues permits a second-moment assumption on the data.

A bounded, centered and standardized approximation of any centered unit-variance
entry law therefore transfers convergence of the expected covariance measures. Together
with concentration, this reduces almost sure weak convergence in the finite-variance
regime to weak convergence in expectation for bounded entries.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2, Theorem 2.5.
* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Springer, 2010, §3.3 and Appendix A.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Matrix.Norms.Frobenius BoundedContinuousFunction

namespace TauCeti.Probability

section Perturbation

variable {Ω Ω' p n 𝕜 : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n]
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
  {X Y : Ω → Matrix p n 𝕜} {Z : Ω' → 𝕜}

private theorem integrable_integral_comp_sqrt_covariance (hX : AEMeasurable X P)
    (f : ℝ →ᵇ ℝ) :
    Integrable (fun ω ↦ ∫ x, f (Real.sqrt x) ∂((X ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)) P := by
  let g := f.compContinuous ⟨Real.sqrt, Real.continuous_sqrt⟩
  have hmeas := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).measurable
    |>.comp_aemeasurable (Matrix.measurable_spectralMeasure_sampleCovariance.comp_aemeasurable hX)
  refine (integrable_const ‖g‖).mono' hmeas.aestronglyMeasurable (.of_forall fun ω ↦ ?_)
  exact g.norm_integral_le_norm _

/-- The expected covariance measures of two coupled matrices with a common entrywise error
law differ on a Lipschitz square-root statistic by at most its Lipschitz constant times the
root mean square error of that law. Independence is unnecessary and empty samples are allowed. -/
theorem norm_integral_comp_sqrt_expectedCovarianceSpectralMeasure_sub_le
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hZ : MemLp Z 2 Q)
    (hid : ∀ i j, IdentDistrib (fun ω ↦ X ω i j - Y ω i j) Z P Q)
    {f : ℝ →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖(∫ x, f (Real.sqrt x) ∂(expectedCovarianceSpectralMeasure hX : Measure ℝ)) -
      ∫ x, f (Real.sqrt x) ∂(expectedCovarianceSpectralMeasure hY : Measure ℝ)‖ ≤
      (K : ℝ) * Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂Q) := by
  let Δ (ω : Ω) := X ω - Y ω
  have hΔ : MemLp (fun ω ↦ ‖Δ ω‖) 2 P := by
    have hm : AEMeasurable (fun ω ↦ ‖Δ ω‖) P := by
      simp only [Δ, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.rpow_two, Matrix.sub_apply]
      exact Real.continuous_sqrt.measurable.comp_aemeasurable
        (Finset.aemeasurable_fun_sum _ fun i _ ↦ Finset.aemeasurable_fun_sum _ fun j _ ↦
          (((hX.eval i).eval j).sub ((hY.eval i).eval j)).norm.pow_const 2)
    refine (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 ?_
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
      integrable_frobenius_norm_sq (X := Δ) (fun i j ↦ (hid i j).memLp_iff.2 hZ)
  let fX (ω : Ω) := ∫ x, f (Real.sqrt x) ∂((X ω).sampleCovariance.spectralMeasure
    (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)
  let fY (ω : Ω) := ∫ x, f (Real.sqrt x) ∂((Y ω).sampleCovariance.spectralMeasure
    (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)
  let g := f.compContinuous ⟨Real.sqrt, Real.continuous_sqrt⟩
  have hmix {W : Ω → Matrix p n 𝕜} (hW : AEMeasurable W P) :
      (∫ x, f (Real.sqrt x) ∂(expectedCovarianceSpectralMeasure hW : Measure ℝ)) =
        ∫ ω, ∫ x, f (Real.sqrt x) ∂((W ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) ∂P := by
    simpa only [g, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using
      integral_expectedCovarianceSpectralMeasure hW (g.integrable _)
  rw [hmix hX, hmix hY, ← integral_sub (integrable_integral_comp_sqrt_covariance hX f)
    (integrable_integral_comp_sqrt_covariance hY f)]
  have hdiff (ω : Ω) :
      ‖fX ω - fY ω‖ ≤ ((K : ℝ) / Real.sqrt (Fintype.card p * Fintype.card n)) * ‖Δ ω‖ := by
    rw [div_mul_eq_mul_div]
    exact Matrix.norm_integral_comp_sqrt_spectralMeasure_sampleCovariance_sub_le (X ω) (Y ω) hf
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hnorm := Lp.norm_integral_le_of_ae_norm_le_mul
    (hΔ.toLp _) (g := fun ω ↦ fX ω - fY ω)
    (hΔ.coeFn_toLp.mono fun ω hω ↦ by
      simpa only [hω, Real.norm_of_nonneg (norm_nonneg (Δ ω))] using hdiff ω)
  have hs : ‖hΔ.toLp _‖ = Real.sqrt (Fintype.card p * Fintype.card n) *
      Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂Q) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (Fintype.card p * Fintype.card n : ℝ)),
      ← Real.sqrt_sq (norm_nonneg (hΔ.toLp _)), hΔ.norm_toLp_sq]
    simp only [Real.norm_of_nonneg (norm_nonneg _)]
    rw [integral_frobenius_norm_sq_of_identDistrib (X := Δ) hid]
  rw [hs, measure_univ, ENNReal.one_rpow, ENNReal.toReal_one, mul_one] at hnorm
  calc
    _ ≤ (K : ℝ) / Real.sqrt (Fintype.card p * Fintype.card n) *
        (Real.sqrt (Fintype.card p * Fintype.card n) * Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂Q)) := by
      simpa only [fX, fY] using hnorm
    _ ≤ _ := by
      by_cases h : Real.sqrt (Fintype.card p * Fintype.card n : ℝ) = 0
      · rw [h, div_zero, zero_mul]
        positivity
      · rw [← mul_assoc, div_mul_cancel₀ _ h]

end Perturbation

section WeakLimit

variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
  {P : (m : ℕ) → Measure (Ω m)} [∀ m, IsProbabilityMeasure (P m)]
  {p n : ℕ → Type*} [∀ m, Fintype (p m)] [∀ m, DecidableEq (p m)]
  [∀ m, Nonempty (p m)] [∀ m, Fintype (n m)]
  {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {X : (m : ℕ) → Ω m → Matrix (p m) (n m) 𝕜}

/-- If coupled matrix approximations have expected covariance measures with the same weak
limit, then the original expected measures have that limit whenever the common entrywise
mean squared errors vanish. The approximation error law can depend on the approximation
index, but is uniform over the dimensions and positions in the data. -/
theorem tendsto_expectedCovarianceSpectralMeasure_of_approx
    (hX : ∀ m, AEMeasurable (X m) (P m))
    {Y : ℕ → (m : ℕ) → Ω m → Matrix (p m) (n m) 𝕜}
    (hY : ∀ k m, AEMeasurable (Y k m) (P m))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {Z : ℕ → Ω' → 𝕜}
    (hZ : ∀ k, MemLp (Z k) 2 Q)
    (hid : ∀ k m i j, IdentDistrib (fun ω ↦ X m ω i j - Y k m ω i j) (Z k) (P m) Q)
    (herr : Tendsto (fun k ↦ ∫ ω, ‖Z k ω‖ ^ 2 ∂Q) atTop (𝓝 0))
    {μ : ProbabilityMeasure ℝ}
    (hlim : ∀ᶠ k in atTop, Tendsto (fun m ↦ expectedCovarianceSpectralMeasure (hY k m))
      atTop (𝓝 μ)) :
    Tendsto (fun m ↦ expectedCovarianceSpectralMeasure (hX m)) atTop (𝓝 μ) := by
  -- An open negative half-line has zero mass for every approximating measure.
  have hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    obtain ⟨k, hk⟩ := hlim.exists
    have hzero (m : ℕ) : (expectedCovarianceSpectralMeasure (hY k m) : Measure ℝ)
        (Set.Iio 0) = 0 := by
      simpa only [Set.Iio, not_le] using
        ae_iff.1 (ae_nonneg_expectedCovarianceSpectralMeasure (hY k m))
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hk
      (isOpen_Iio (a := (0 : ℝ)))
    simp only [hzero, liminf_const] at hle
    exact ae_iff.2 (by simpa only [Set.Iio, not_le] using le_antisymm hle bot_le)
  apply (ProbabilityMeasure.tendsto_iff_tendsto_map_sqrt
    (.of_forall fun m ↦ ae_nonneg_expectedCovarianceSpectralMeasure (hX m)) hμ).2
  apply tendsto_iff_forall_lipschitz_integral_tendsto.2
  rintro f ⟨C, hC⟩ ⟨K, hK⟩
  let g : ℝ →ᵇ ℝ := ⟨⟨f, hK.continuous⟩, C, hC⟩
  have hint (ν : ProbabilityMeasure ℝ) :
      (∫ x, f x ∂(ν.map Real.sqrt : Measure ℝ)) =
        ∫ x, g (Real.sqrt x) ∂(ν : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map Real.continuous_sqrt.measurable.aemeasurable
        hK.continuous.aestronglyMeasurable]
    rfl
  simp_rw [hint]
  have he : Tendsto (fun k ↦ (K : ℝ) * Real.sqrt (∫ ω, ‖Z k ω‖ ^ 2 ∂Q)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp herr).const_mul (K : ℝ)
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨k, hk, hkerr⟩ := (hlim.and ((tendsto_order.1 he).2 (ε / 2) (by positivity))).exists
  have hg := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (g.compContinuous ⟨Real.sqrt, Real.continuous_sqrt⟩)).continuousAt.tendsto.comp hk
  filter_upwards [Metric.tendsto_nhds.1 hg (ε / 2) (by positivity)] with m hm
  have hdist := norm_integral_comp_sqrt_expectedCovarianceSpectralMeasure_sub_le
    (hX m) (hY k m) (hZ k) (hid k m) (f := g) hK
  have htriangle := dist_triangle
    (∫ x, g (Real.sqrt x) ∂(expectedCovarianceSpectralMeasure (hX m) : Measure ℝ))
    (∫ x, g (Real.sqrt x) ∂(expectedCovarianceSpectralMeasure (hY k m) : Measure ℝ))
    (∫ x, g (Real.sqrt x) ∂(μ : Measure ℝ))
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at hm
  simp only [dist_eq_norm, Function.comp_def] at htriangle hm ⊢
  linarith

end WeakLimit

section BoundedEntries

variable {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {p n : ℕ → Type*} [∀ m, Fintype (p m)] [∀ m, DecidableEq (p m)]
  [∀ m, Nonempty (p m)] [∀ m, Fintype (n m)]
  {X : (m : ℕ) → Ω → Matrix (p m) (n m) 𝕜}

/-- To get almost sure spectral convergence for independent, identically distributed,
centered entries with unit second absolute moment, it suffices to prove weak convergence
of the expected measures in the bounded-entry case. The data dimensions are the same in
both cases, and the row count grows at least linearly. The coupling across sizes is arbitrary. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_entries
    (hind : ∀ m, iIndepFun (fun ij : p m × n m ↦ fun ω ↦ X m ω ij.1 ij.2) P)
    {ν : Measure 𝕜} [IsProbabilityMeasure ν]
    (hLaw : ∀ m i j, HasLaw (fun ω ↦ X m ω i j) ν P)
    (hmean : ∫ x, x ∂ν = 0) (hunit : ∫ x, ‖x‖ ^ 2 ∂ν = 1)
    {δ : ℝ} (hδ : 0 < δ) (hdim : ∀ᶠ m : ℕ in atTop, δ * (m : ℝ) ≤ Fintype.card (p m))
    {μ : ProbabilityMeasure ℝ}
    (hbounded : ∀ (Y : (m : ℕ) → Ω → Matrix (p m) (n m) 𝕜)
      (hY : ∀ m, AEMeasurable (Y m) P) (ρ : Measure 𝕜),
      (∀ m, iIndepFun (fun ij : p m × n m ↦ fun ω ↦ Y m ω ij.1 ij.2) P) →
      (∀ m i j, HasLaw (fun ω ↦ Y m ω i j) ρ P) →
      (∃ B : ℝ, ∀ᵐ x ∂ρ, ‖x‖ ≤ B) →
      (∫ x, x ∂ρ = 0) → (∫ x, ‖x‖ ^ 2 ∂ρ = 1) →
      Tendsto (fun m ↦ expectedCovarianceSpectralMeasure (hY m)) atTop (𝓝 μ)) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ (X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _)) atTop (𝓝 μ) := by
  have hX (m : ℕ) : AEMeasurable (X m) P :=
    .of_eval fun i ↦ .of_eval fun j ↦ (hLaw m i j).aemeasurable
  have hsum (a : ℝ) (ha : 0 < a) : Summable (fun m ↦ Real.exp (-a * Fintype.card (p m))) := by
    have hs : Summable (fun m : ℕ ↦ Real.exp (-(a * δ) * m)) := by
      simpa only [pow_zero, one_mul] using
        Real.summable_pow_mul_exp_neg_nat_mul 0 (mul_pos ha hδ)
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hdim] with m hm
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hm ha.le])
  apply (ae_tendsto_spectralMeasure_sampleCovariance_iff_tendsto_expected hX
    (fun m ↦ (hind m).matrix_row fun i j ↦ (hLaw m i j).aemeasurable) hsum).2
  have h₂ : MemLp (id : 𝕜 → 𝕜) 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
    by_contra h
    have hzero := integral_undef h
    simp only [id_eq, hunit, one_ne_zero] at hzero
  obtain ⟨f, hf, herr⟩ := exists_bounded_centered_unitSecondMoment_approx h₂ hmean hunit
  let Y (k m : ℕ) (ω : Ω) := (X m ω).map (f k)
  have hY (k m : ℕ) : AEMeasurable (Y k m) P :=
    .of_eval fun i ↦ .of_eval fun j ↦ (hf k).1.comp_aemeasurable (hLaw m i j).aemeasurable
  have hmem (k : ℕ) : MemLp (f k) 2 ν := by
    obtain ⟨B, hB⟩ := (hf k).2.1
    exact MemLp.of_bound (hf k).1.aestronglyMeasurable B (.of_forall hB)
  refine tendsto_expectedCovarianceSpectralMeasure_of_approx (Ω := fun _ ↦ Ω) hX hY
    (Z := fun k x ↦ x - f k x) (fun k ↦ h₂.sub (hmem k)) ?_ herr ?_
  · intro k m i j
    have hident := (hLaw m i j).identDistrib
      (by simpa only [Measure.map_id] using
        (hasLaw_map (P := ν) measurable_id.aemeasurable))
    have hsub : Measurable (fun x : 𝕜 ↦ x - f k x) := measurable_id.sub (hf k).1
    simpa only [Y, Matrix.map_apply, Function.comp_def, id_eq] using hident.comp hsub
  · filter_upwards with k
    obtain ⟨hfm, ⟨B, hB⟩, hfc, hfu⟩ := hf k
    apply hbounded (Y k) (hY k) (ν.map (f k))
    · intro m
      exact (hind m).comp (fun _ ↦ f k) (fun _ ↦ hfm)
    · intro m i j
      exact (hasLaw_map (P := ν) hfm.aemeasurable).comp (hLaw m i j)
    · exact ⟨B, (ae_map_iff hfm.aemeasurable (measurableSet_le measurable_norm measurable_const)).2
        (.of_forall hB)⟩
    · exact (integral_map (f := id) hfm.aemeasurable measurable_id.aestronglyMeasurable).trans hfc
    · simpa only [integral_map hfm.aemeasurable
        (measurable_norm.pow_const 2).aestronglyMeasurable] using hfu

end BoundedEntries

end TauCeti.Probability
