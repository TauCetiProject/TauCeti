/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic.LinearCombination
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Cauchy.ApproximateIdentity

/-!
# Recovering a density from the resolvent transform

When the vertical boundary values of the imaginary resolvent transform of a finite measure
exist everywhere on an open set and are continuous there, the restricted measure has those
values divided by `π` as its density. This local form allows atoms or singular mass elsewhere.

The interval inversion formula and Fatou's lemma show that the proposed density defines a
submeasure. Its transform has the given boundary values by the Cauchy approximate identity,
which uses Mathlib's `tendsto_integral_comp_smul_smul_of_integrable'`. The remaining positive
measure has zero boundary values, and a closed-ball mass bound shows that it gives no mass to
the open set. Both measure comparisons use Mathlib's `Besicovitch.vitaliFamily` and
`VitaliFamily.measure_le_of_frequently_le`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  for Stieltjes inversion.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Real Topology

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- A finite measure gives zero mass to any set on which its imaginary resolvent transform
has pointwise vertical boundary limit zero. -/
theorem measure_eq_zero_of_tendsto_im_resolventTransform_zero {s : Set ℝ}
    (h : ∀ x ∈ s, Tendsto (fun η : ℝ ↦ (resolventTransform μ (x + η * I)).im)
      (𝓝[>] 0) (𝓝 0)) : μ s = 0 := by
  -- Dominate the measure by arbitrarily small multiples of Lebesgue measure on bounded sets.
  let ρ := μ + (volume : Measure ℝ)
  have hμρ : μ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hle (t : Set ℝ) (ht : t ⊆ s) (c : ℝ≥0) (hc : 0 < c) :
      μ t ≤ (c : ℝ≥0∞) * volume t := by
    let := (volume : Measure ℝ).isLocallyFiniteMeasure_smul (ENNReal.coe_ne_top (r := c))
    refine (Besicovitch.vitaliFamily ρ).measure_le_of_frequently_le
      ((c : ℝ≥0∞) • volume) hμρ t fun x hx ↦ ?_
    apply (Besicovitch.tendsto_filterAt ρ x).frequently
    apply Eventually.frequently
    have hcReal : 0 < (c : ℝ) := by exact_mod_cast hc
    filter_upwards [self_mem_nhdsWithin, (h x (ht hx)).eventually (Iio_mem_nhds hcReal)]
      with η hη hηc
    have hη' : 0 < η := hη
    rw [smul_apply, smul_eq_mul, Real.volume_closedBall, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul c.coe_nonneg, mul_comm (c : ℝ), ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal
      ((measureReal_closedBall_le_two_mul_mul_im_resolventTransform x hη').trans
        (mul_le_mul_of_nonneg_left hηc.le (by positivity)))
  have hzero (n : ℕ) : μ (s ∩ closedBall 0 n) = 0 := by
    let t := s ∩ closedBall (0 : ℝ) n
    have ht : volume t ≠ ∞ :=
      ne_top_of_le_ne_top (isCompact_closedBall (0 : ℝ) (n : ℝ)).measure_lt_top.ne
        (measure_mono inter_subset_right)
    apply le_antisymm _ bot_le
    refine ge_of_tendsto (x := 𝓝[>] (0 : ℝ≥0))
      (f := fun c : ℝ≥0 ↦ (c : ℝ≥0∞) * volume t) ?_ ?_
    · have hc : Tendsto (fun c : ℝ≥0 ↦ (c : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) :=
        by simpa using (ENNReal.continuous_coe.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const hc (Or.inr ht)
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact hle t inter_subset_left c hc
  rw [← iUnion_inter_closedBall_nat s 0]
  exact measure_iUnion_null hzero

private theorem pi_inv_mul_im_resolventTransform_nonneg (x : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ π⁻¹ * (resolventTransform μ (x + η * I)).im := by
  rw [im_resolventTransform]
  refine mul_nonneg (by positivity) (integral_nonneg fun t ↦ ?_)
  have him : ((x : ℂ) + η * I).im = η := by simp
  rw [him]
  positivity

private theorem lintegral_Ioc_ofReal_le_measure_Icc_of_tendsto {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ᵐ x : ℝ ∂volume.restrict (Ioc a b),
      Tendsto (fun η : ℝ ↦ π⁻¹ * (resolventTransform μ (x + η * I)).im)
        (𝓝[>] 0) (𝓝 (f x))) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) ≤ μ (Icc a b) := by
  by_cases hab : a < b
  swap
  · simp [Ioc_eq_empty hab]
  let F := fun (η x : ℝ) ↦ π⁻¹ * (resolventTransform μ (x + η * I)).im
  have hlim : Tendsto (fun η ↦ ∫ x in Ioc a b, F η x) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
    simpa only [F, intervalIntegral.integral_of_le hab.le, integral_const_mul] using
      tendsto_intervalIntegral_im_resolventTransform (μ := μ) hab
  have hcont {η : ℝ} (hη : η ≠ 0) : Continuous (F η) := by
    apply continuous_iff_continuousAt.2 fun x ↦
      continuousAt_const.mul (Complex.continuous_im.continuousAt.comp ?_)
    exact (continuousAt_resolventTransform_of_im_ne_zero (by simpa using hη)).comp
      ((Complex.continuous_ofReal.add continuous_const).continuousAt)
  have heq : (fun η ↦ ∫⁻ x in Ioc a b, ENNReal.ofReal (F η x)) =ᶠ[𝓝[>] 0]
      fun η ↦ ENNReal.ofReal (∫ x in Ioc a b, F η x) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : 0 < η := hη
    rw [ofReal_integral_eq_lintegral_ofReal
      ((hcont hη'.ne').integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    exact ae_of_all _ fun x ↦ pi_inv_mul_im_resolventTransform_nonneg x hη'.le
  have hfatou := lintegral_liminf_le' (μ := volume.restrict (Ioc a b))
    (u := 𝓝[>] (0 : ℝ)) (f := fun η x ↦ ENNReal.ofReal (F η x))
  calc
    _ = ∫⁻ x in Ioc a b, liminf (fun η ↦ ENNReal.ofReal (F η x)) (𝓝[>] 0) :=
      lintegral_congr_ae (h.mono fun _ hx ↦
        ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm)
    _ ≤ liminf (fun η ↦ ∫⁻ x in Ioc a b, ENNReal.ofReal (F η x)) (𝓝[>] 0) :=
      hfatou (fun η ↦ by
        rcases eq_or_ne η 0 with rfl | hη
        · simp [F, im_resolventTransform]
        · exact ((hcont hη).measurable.ennreal_ofReal).aemeasurable)
    _ = ENNReal.ofReal (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2) :=
      (((ENNReal.continuous_ofReal.tendsto _).comp hlim).congr' heq.symm).liminf_eq
    _ ≤ μ (Icc a b) := by
      rw [← ofReal_measureReal]
      apply ENNReal.ofReal_le_ofReal
      rw [← Ico_union_right hab.le, ← Ioo_union_left hab,
        measureReal_union (by simp [hab.ne']) (measurableSet_singleton b),
        measureReal_union (by simp) (measurableSet_singleton a)]
      linarith [measureReal_nonneg (μ := μ) (s := {a}), measureReal_nonneg (μ := μ) (s := {b})]

/-- The pointwise vertical boundary values of the normalized imaginary resolvent transform
of a finite measure define a dominated density measure on an open set. -/
theorem Measure.withDensity_restrict_le_of_tendsto_im_resolventTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ] {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (h : ∀ x ∈ s, Tendsto (fun η : ℝ ↦ π⁻¹ * (resolventTransform μ (x + η * I)).im)
      (𝓝[>] 0) (𝓝 (f x))) :
    (volume.restrict s).withDensity (fun x ↦ ENNReal.ofReal (f x)) ≤ μ := by
  let ν := (volume.restrict s).withDensity (fun x ↦ ENNReal.ofReal (f x))
  have hν : ν ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (Measure.restrict_le_self.absolutelyContinuous)
  refine Measure.le_iff.2 fun t ht ↦ ?_
  have hνs : ν.restrict s = ν := volume.restrict_withDensity_restrict s _
  have hts : ν t = ν (t ∩ s) := by
    rw [← Measure.restrict_apply ht, hνs]
  rw [hts]
  refine ((Besicovitch.vitaliFamily volume).measure_le_of_frequently_le μ hν (t ∩ s)
    fun x hx ↦ ?_).trans (measure_mono inter_subset_left)
  apply (Besicovitch.tendsto_filterAt volume x).frequently
  apply Eventually.frequently
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (hs.mem_nhds hx.2)
  filter_upwards [Ioo_mem_nhdsGT hr] with η hη
  have hball : closedBall x η ⊆ s := (closedBall_subset_ball hη.2).trans hrs
  rw [Real.closedBall_eq_Icc] at hball ⊢
  have hlt : x - η < x + η := by linarith [hη.1]
  have hνIoc : ν (Icc (x - η) (x + η)) = ν (Ioc (x - η) (x + η)) := by
    rw [← Ioc_union_left hlt.le, measure_union (by simp) (measurableSet_singleton _),
      hν (measure_singleton _), add_zero]
  rw [hνIoc, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict_of_subset (Ioc_subset_Icc_self.trans hball)]
  exact lintegral_Ioc_ofReal_le_measure_Icc_of_tendsto
    ((ae_restrict_mem measurableSet_Ioc).mono fun y hy ↦ h y (hball (Ioc_subset_Icc_self hy)))

/-- The normalized imaginary resolvent transform of a finite measure with nonnegative density
approaches the density at each point of continuity. -/
theorem tendsto_pi_inv_mul_im_resolventTransform_withDensity {g : ℝ → ℝ≥0}
    (hg : Integrable (fun t ↦ (g t : ℝ)) volume) {x : ℝ} (hx : ContinuousAt g x) :
    Tendsto (fun η : ℝ ↦ π⁻¹ *
      (resolventTransform (volume.withDensity (fun t ↦ (g t : ℝ≥0∞))) (x + η * I)).im)
      (𝓝[>] 0) (𝓝 (g x : ℝ)) := by
  let : IsFiniteMeasure (volume.withDensity (fun t ↦ (g t : ℝ≥0∞))) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral
  have hpeak := TauCeti.Probability.tendsto_integral_cauchyPDFReal_smul hg
    (NNReal.continuous_coe.continuousAt.comp hx)
  refine hpeak.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : 0 < η := hη
  rw [im_resolventTransform,
    integral_withDensity_eq_integral_smul₀ (aemeasurable_coe_nnreal_real_iff.1 hg.aemeasurable),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    simp only [ProbabilityTheory.cauchyPDFReal_def, Real.coe_toNNReal _ hη'.le, smul_eq_mul,
      NNReal.smul_def, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add, div_eq_mul_inv]
    ring

private theorem tendsto_im_resolventTransform_sub_of_tendsto {ν : Measure ℝ}
    (hν : ν ≤ μ) (x : ℝ) {r : ℝ}
    (hμlim : Tendsto (fun η : ℝ ↦ π⁻¹ * (resolventTransform μ (x + η * I)).im)
      (𝓝[>] 0) (𝓝 r))
    (hνlim : Tendsto (fun η : ℝ ↦ π⁻¹ * (resolventTransform ν (x + η * I)).im)
      (𝓝[>] 0) (𝓝 r)) :
    Tendsto (fun η : ℝ ↦ (resolventTransform (μ - ν) (x + η * I)).im) (𝓝[>] 0) (𝓝 0) := by
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hν
  have hlim := (hμlim.sub hνlim).const_mul π
  simp only [sub_self, mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : 0 < η := hη
  have hz : ((x : ℂ) + η * I).im ≠ 0 := by simpa using hη'.ne'
  rw [μ.resolventTransform_sub hν (integrable_resolvent_of_im_ne_zero hz), Complex.sub_im]
  have hπ : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  linear_combination
    ((resolventTransform μ (x + η * I)).im - (resolventTransform ν (x + η * I)).im) * hπ

namespace Measure

/-- **Stieltjes inversion for a continuous boundary density.** If the imaginary resolvent
transform divided by `π` tends vertically to a function `f` at every point of an open set
`s` and `f` is continuous there, then the finite measure has Lebesgue density `f` on `s`. -/
theorem restrict_eq_withDensity_of_tendsto_im_resolventTransform (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ} (hf : ContinuousOn f s)
    (h : ∀ x ∈ s, Tendsto (fun η : ℝ ↦ π⁻¹ * (resolventTransform μ (x + η * I)).im)
      (𝓝[>] 0) (𝓝 (f x))) :
    μ.restrict s = (volume.restrict s).withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  let g := fun x ↦ (s.indicator f x).toNNReal
  let ν := volume.withDensity (fun x ↦ (g x : ℝ≥0∞))
  have hνeq : ν = (volume.restrict s).withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
    rw [← withDensity_indicator hs.measurableSet]
    apply congrArg volume.withDensity
    ext x
    by_cases hx : x ∈ s <;> simp [g, hx, ENNReal.ofReal]
  have hνle : ν ≤ μ := hνeq ▸ μ.withDensity_restrict_le_of_tendsto_im_resolventTransform hs h
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hg : Integrable (fun x ↦ (g x : ℝ)) volume := by
    classical
    have hgm : Measurable (s.indicator f) := by
      simpa only [← Pi.zero_def, piecewise_eq_indicator] using
        hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hs.measurableSet
    have hgmeas : Measurable g := continuous_real_toNNReal.measurable.comp hgm
    exact TauCeti.MeasureTheory.integrable_of_eq_withDensity (ν := ν)
      (by simp only [ν, ENNReal.ofReal_coe_nnreal])
      (NNReal.continuous_coe.measurable.comp hgmeas).aemeasurable
      (ae_of_all _ fun x ↦ (g x).coe_nonneg)
  have hsub (x : ℝ) (hx : x ∈ s) :
      Tendsto (fun η : ℝ ↦ (resolventTransform (μ - ν) (x + η * I)).im) (𝓝[>] 0) (𝓝 0) := by
    have hf₀ : 0 ≤ f x := ge_of_tendsto (h x hx) (by
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη' : 0 < η := hη
      exact pi_inv_mul_im_resolventTransform_nonneg x hη'.le)
    have hcont : ContinuousAt (s.indicator f) x :=
      (hf x hx).continuousAt (hs.mem_nhds hx) |>.congr (by
        filter_upwards [hs.mem_nhds hx] with y hy
        simp [hy])
    have hνlim := tendsto_pi_inv_mul_im_resolventTransform_withDensity hg
      (continuous_real_toNNReal.continuousAt.comp hcont)
    have heq : (g x : ℝ) = f x := by simp [g, hx, Real.coe_toNNReal _ hf₀]
    rw [heq] at hνlim
    exact tendsto_im_resolventTransform_sub_of_tendsto hνle x (h x hx) hνlim
  have hzero := Measure.restrict_eq_zero.2
    (measure_eq_zero_of_tendsto_im_resolventTransform_zero hsub)
  calc
    μ.restrict s = (μ - ν).restrict s + ν.restrict s := by
      rw [← Measure.restrict_add, Measure.sub_add_cancel_of_le hνle]
    _ = (volume.restrict s).withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
      rw [hzero, zero_add, hνeq, volume.restrict_withDensity_restrict s]

end Measure

end MeasureTheory

end
