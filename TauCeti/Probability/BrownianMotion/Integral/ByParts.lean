/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Wiener
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.Bochner.Lp

/-!
# Integration by parts for deterministic Wiener integrals

Let `h` be continuous on `[0, a]` and differentiable on `(0, a)` with integrable derivative `h'`.
The Wiener integral of `h` on the horizon `(0, a]` against a pre-Brownian motion `B` is given by
the integration by parts formula
`∫₀ᵃ h dB = h a B_a - ∫₀ᵃ h' u B_u du`.

As an identity in `L²(P)` the last integral is the Bochner integral of the continuous `L²` curve
`u ↦ B_u` (`ProbabilityTheory.IsPreBrownianReal.wienerIntegral_eq_smul_toL2_sub_integral`). When
the sample paths are jointly measurable in time and sample, which holds for Brownian motion
(`ProbabilityTheory.IsBrownianReal.aestronglyMeasurable_uncurry`), it is almost surely the
samplewise time integral of the paths
(`ProbabilityTheory.IsPreBrownianReal.wienerIntegral_ae_eq_mul_sub_integral`). This expresses
Wiener integrals of smooth deterministic integrands through ordinary integrals of the paths, and
conversely identifies such pathwise expressions as Gaussian.

The proof writes `h` on `(0, a]` as `h a - ∫ₛᵃ h'`, that is, as `h a` times the indicator of
`(0, a]` minus the `L²`-valued integral of `h' u` times the indicators of `(0, u]`, and applies the
Wiener integral, which sends the indicator of `(0, u]` to `B_u`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 and Problem 3.2.27.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The indicator class of the initial interval `(0, u]` on the horizon `a`. -/
private def initialIndicator (a u : ℝ≥0) : Lp ℝ 2 (timeMeasure a) :=
  indicatorConstLp 2 (measurableSet_Iic (a := u)) (measure_ne_top _ _) 1

private theorem coeFn_initialIndicator (a u : ℝ≥0) :
    ⇑(initialIndicator a u) =ᵐ[timeMeasure a] (Iic u).indicator 1 :=
  indicatorConstLp_coeFn

private theorem wienerIntegral_initialIndicator (hB : IsPreBrownianReal B P) (a u : ℝ≥0) :
    hB.wienerIntegral a (initialIndicator a u) = hB.toL2 (min u a) := by
  simp [initialIndicator]

/-- The initial-interval indicators depend continuously on the endpoint. The Wiener integral of a
pre-Brownian motion is an isometry sending them to the continuous `L²` curve of the motion. -/
private theorem continuous_initialIndicator (hB : IsPreBrownianReal B P) (a : ℝ≥0) :
    Continuous fun u : ℝ ↦ initialIndicator a u.toNNReal := by
  refine (hB.wienerIntegral a).isometry.isEmbedding.continuous_iff.2 ?_
  simp only [Function.comp_def, wienerIntegral_initialIndicator]
  exact hB.continuous_toL2.comp (continuous_real_toNNReal.min continuous_const)

/-- **Fundamental theorem of calculus on `(s, a]`.** For `s ∈ (0, a]`, integrating `h' u` over the
`u ∈ (0, a]` with `s ≤ u` gives `h a - h s`. -/
private theorem integral_mul_indicator_Iic_toNNReal {a : ℝ≥0} {h h' : ℝ → ℝ}
    (hcont : ContinuousOn h (Icc 0 a)) (hderiv : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt h (h' x) x)
    (hint : IntervalIntegrable h' volume 0 a) {s : ℝ≥0} (hs : s ∈ Ioc 0 a) :
    ∫ u in Ioc (0 : ℝ) a, h' u * (Iic u.toNNReal).indicator 1 s = h a - h s := by
  have hs0 : (0 : ℝ) < s := hs.1
  have hsa : (s : ℝ) ≤ a := hs.2
  have hind' : EqOn (fun u ↦ h' u * (Iic u.toNNReal).indicator 1 s) ((Ici (s : ℝ)).indicator h')
      (Ioc 0 a) := fun u _ ↦ by
    by_cases hu : (s : ℝ) ≤ u
    · simp [indicator_of_mem (mem_Iic.2 ((Real.le_toNNReal_iff_coe_le' hs.1).2 hu)), hu]
    · have hu' : s ∉ Iic u.toNNReal := fun h ↦
        hu ((Real.le_toNNReal_iff_coe_le' hs.1).1 (mem_Iic.1 h))
      simp [indicator_of_notMem hu', hu]
  have hset : Ici (s : ℝ) ∩ Ioc 0 a = Icc (s : ℝ) a := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, hs0.trans_le hx.1, hx.2⟩⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hind',
    integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsa,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsa
      (hcont.mono (Icc_subset_Icc_left hs0.le))
      (fun x hx ↦ hderiv x ⟨hs0.trans hx.1, hx.2⟩)
      (hint.mono_set (by
        rw [uIcc_of_le hsa, uIcc_of_le a.coe_nonneg]; exact Icc_subset_Icc_left hs0.le))]

/-- **Integration by parts on the horizon.** If `f` represents `h` on `(0, a]`, then
`f = h a 1_{(0,a]} - ∫₀ᵃ h' u 1_{(0,u]} du` in `L²`. -/
private theorem eq_smul_sub_integral_initialIndicator (hB : IsPreBrownianReal B P) {a : ℝ≥0}
    {h h' : ℝ → ℝ} (hcont : ContinuousOn h (Icc 0 a))
    (hderiv : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt h (h' x) x)
    (hint : IntervalIntegrable h' volume 0 a) {f : Lp ℝ 2 (timeMeasure a)}
    (hf : f =ᵐ[timeMeasure a] fun s ↦ h s) :
    f = h a • initialIndicator a a -
      ∫ u in (0 : ℝ)..a, h' u • initialIndicator a u.toNNReal := by
  have hF : Integrable (fun u ↦ h' u • initialIndicator a u.toNNReal)
      (volume.restrict (Ioc (0 : ℝ) a)) :=
    (hint.smul_continuousOn (continuous_initialIndicator hB a).continuousOn).1
  have hX : AEStronglyMeasurable
      (fun p : ℝ × ℝ≥0 ↦ h' p.1 * (Iic p.1.toNNReal).indicator 1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) a)).prod (timeMeasure a)) := by
    refine (hint.1.aestronglyMeasurable.comp_fst).mul ?_
    have hfun : (fun p : ℝ × ℝ≥0 ↦ (Iic p.1.toNNReal).indicator (1 : ℝ≥0 → ℝ) p.2) =
        {p : ℝ × ℝ≥0 | p.2 ≤ p.1.toNNReal}.indicator 1 := by
      ext p
      simp only [indicator_apply, mem_Iic, mem_ofPred_eq, Pi.one_apply]
    rw [hfun]
    exact (measurable_one.indicator
      (measurableSet_le measurable_snd measurable_fst.real_toNNReal)).aestronglyMeasurable
  have heq : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) a),
      ⇑(h' u • initialIndicator a u.toNNReal) =ᵐ[timeMeasure a]
        fun s ↦ h' u * (Iic u.toNNReal).indicator 1 s := by
    refine Eventually.of_forall fun u ↦ ?_
    filter_upwards [Lp.coeFn_smul (h' u) (initialIndicator a u.toNNReal),
      coeFn_initialIndicator a u.toNNReal] with s hs hi
    rw [hs, Pi.smul_apply, hi, smul_eq_mul]
  have hI := Integrable.coeFn_integral_Lp hF
    (X := fun (u : ℝ) (s : ℝ≥0) ↦ h' u * (Iic u.toNNReal).indicator 1 s) hX heq
  rw [← intervalIntegral.integral_of_le a.coe_nonneg] at hI
  apply Lp.ext
  filter_upwards [hf, hI, Lp.coeFn_sub (h a • initialIndicator a a)
      (∫ u in (0 : ℝ)..a, h' u • initialIndicator a u.toNNReal),
    Lp.coeFn_smul (h a) (initialIndicator a a), coeFn_initialIndicator a a,
    ae_mem_Ioc_timeMeasure a] with s hfs hIs hsub hsmul hind hs
  rw [hfs, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hind, hIs,
    indicator_of_mem (mem_Iic.2 hs.2), Pi.one_apply, smul_eq_mul, mul_one]
  rw [integral_mul_indicator_Iic_toNNReal hcont hderiv hint hs]
  ring

/-- **Integration by parts for Wiener integrals, in `L²`.** Let `h` be continuous on `[0, a]` and
differentiable on `(0, a)` with interval integrable derivative `h'`. The Wiener integral on
`(0, a]` of an `L²` class `f` represented by `h` is `h a B_a - ∫₀ᵃ h' u B_u du`, the last integral
being the Bochner integral of the `L²` curve of `B`. -/
theorem wienerIntegral_eq_smul_toL2_sub_integral (hB : IsPreBrownianReal B P) {a : ℝ≥0}
    {h h' : ℝ → ℝ} (hcont : ContinuousOn h (Icc 0 a))
    (hderiv : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt h (h' x) x)
    (hint : IntervalIntegrable h' volume 0 a) {f : Lp ℝ 2 (timeMeasure a)}
    (hf : f =ᵐ[timeMeasure a] fun s ↦ h s) :
    hB.wienerIntegral a f = h a • hB.toL2 a - ∫ u in (0 : ℝ)..a, h' u • hB.toL2 u.toNNReal := by
  have hF : IntervalIntegrable (fun u ↦ h' u • initialIndicator a u.toNNReal) volume 0 a :=
    hint.smul_continuousOn (continuous_initialIndicator hB a).continuousOn
  rw [eq_smul_sub_integral_initialIndicator hB hcont hderiv hint hf, map_sub, map_smul,
    wienerIntegral_initialIndicator, min_self]
  congr 1
  rw [← LinearIsometry.coe_toContinuousLinearMap,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hF]
  refine intervalIntegral.integral_congr fun u hu ↦ ?_
  rw [uIcc_of_le a.coe_nonneg] at hu
  simp only [map_smul, LinearIsometry.coe_toContinuousLinearMap, wienerIntegral_initialIndicator,
    min_eq_left (Real.toNNReal_le_iff_le_coe.2 hu.2)]

/-- **Integration by parts for Wiener integrals, samplewise.** Let `h` be continuous on `[0, a]`
and differentiable on `(0, a)` with interval integrable derivative `h'`. If the paths of `B` are
jointly measurable on `(0, a] × Ω`, then the Wiener integral on `(0, a]` of an `L²` class `f`
represented by `h` is almost surely `h a B_a - ∫₀ᵃ h' u B_u du`, with the samplewise time
integral of the paths. -/
theorem wienerIntegral_ae_eq_mul_sub_integral (hB : IsPreBrownianReal B P) {a : ℝ≥0}
    {h h' : ℝ → ℝ} (hcont : ContinuousOn h (Icc 0 a))
    (hderiv : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt h (h' x) x)
    (hint : IntervalIntegrable h' volume 0 a) {f : Lp ℝ 2 (timeMeasure a)}
    (hf : f =ᵐ[timeMeasure a] fun s ↦ h s)
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) a)).prod P)) :
    ⇑(hB.wienerIntegral a f) =ᵐ[P]
      fun ω ↦ h a * B a ω - ∫ u in (0 : ℝ)..a, h' u * B u.toNNReal ω := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hF : Integrable (fun u ↦ h' u • hB.toL2 u.toNNReal) (volume.restrict (Ioc (0 : ℝ) a)) :=
    (hint.smul_continuousOn hB.continuous_toL2_toNNReal.continuousOn).1
  have hI := Integrable.coeFn_integral_Lp hF (X := fun u ω ↦ h' u * B u.toNNReal ω)
    ((hint.1.aestronglyMeasurable.comp_fst).mul hm)
    (Eventually.of_forall fun u ↦ (Lp.coeFn_smul (h' u) (hB.toL2 u.toNNReal)).trans
      ((hB.coeFn_toL2 u.toNNReal).mono fun ω hω ↦ by simp [hω]))
  rw [hB.wienerIntegral_eq_smul_toL2_sub_integral hcont hderiv hint hf,
    intervalIntegral.integral_of_le a.coe_nonneg]
  filter_upwards [Lp.coeFn_sub (h a • hB.toL2 a)
      (∫ u in Ioc (0 : ℝ) a, h' u • hB.toL2 u.toNNReal),
    Lp.coeFn_smul (h a) (hB.toL2 a), hB.coeFn_toL2 a, hI] with ω hsub hsmul hBa hIω
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hBa, hIω, smul_eq_mul,
    intervalIntegral.integral_of_le a.coe_nonneg]

end ProbabilityTheory.IsPreBrownianReal
