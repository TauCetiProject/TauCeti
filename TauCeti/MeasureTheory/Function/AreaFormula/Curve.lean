/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Topology.EMetricSpace.CurveLength
import TauCeti.Topology.MetricSpace.Arclength.Basic

/-!
# The area formula for curves

This file specializes the area formula with multiplicity to maps from a real interval. For a
Lipschitz curve, its total variation is the one-dimensional Hausdorff integral of the extended
cardinality of its fibers. Thus length counts repeated traversals, while the Hausdorff measure of
the trace does not.

The curve need only be Lipschitz on the parameter interval. A finite-dimensional Lipschitz
extension reduces the result to the global area formula; derivatives and fiber sums are then
transported back to the original curve. The one-dimensional geometric Jacobian is identified
with the norm of the velocity.

The multiplicity formula then extends to every continuous curve on a compact interval, the
Banach indicatrix formula `ContinuousOn.eVariationOn_eq_lintegral_encard`. A rectifiable curve
factors through its arclength parametrization, which is 1-Lipschitz and has the same length.
Its fibers have the same cardinality as those of the original curve except over the countably
many values taken on pauses. For a curve of infinite length, the lower bound
`ContinuousOn.eVariationOn_le_lintegral_encard` makes the multiplicity integral infinite too.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, Section 3.3 (the area formula for Lipschitz maps).
* H. Federer, *Geometric Measure Theory*, Theorem 2.10.13 (the Banach indicatrix formula for
  continuous curves).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LipschitzOnWith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {K : ℝ≥0} {γ : ℝ → V} {a b : ℝ}

/-- The weighted area formula for a curve Lipschitz on a compact interval. The weight is attached
to the parameter, and the right-hand side sums it over every fiber, including infinite fibers. -/
theorem lintegral_enorm_deriv_mul_eq_lintegral_tsum (hγ : LipschitzOnWith K γ (Icc a b))
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ * g t =
      ∫⁻ y, ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}), g t ∂μHE[1] := by
  obtain ⟨f, hf, hfeq⟩ := hγ.extend_finite_dimension
  have harea := hf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum
    (nullMeasurableSet_Icc : NullMeasurableSet (Icc a b) volume) hg
  rw [Module.finrank_self] at harea
  have hsets (y : V) : Icc a b ∩ f ⁻¹' {y} = Icc a b ∩ γ ⁻¹' {y} := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact and_congr_right fun ht ↦ by rw [hfeq ht]
  have hfibers (y : V) :
      (∑' t : ↥(Icc a b ∩ f ⁻¹' {y}), g t) =
        ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}), g t := by
    rw [hsets y]
  calc
    (∫⁻ t in Icc a b, ‖deriv γ t‖ₑ * g t) =
        ∫⁻ t in Icc a b, ENNReal.ofReal (fderiv ℝ f t).normDet * g t := by
      apply setLIntegral_congr_fun_ae measurableSet_Icc
      filter_upwards [volume.ae_ne a, volume.ae_ne b] with t hta htb ht
      have ht' : t ∈ Ioo a b :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
      have heq : f =ᶠ[nhds t] γ := by
        filter_upwards [Icc_mem_nhds ht'.1 ht'.2] with x hx
        exact (hfeq hx).symm
      rw [heq.fderiv_eq, LinearMap.normDet_eq_norm_apply_one]
      rw [ofReal_norm, ContinuousLinearMap.coe_coe, fderiv_apply_one_eq_deriv]
    _ = ∫⁻ y, ∑' t : ↥(Icc a b ∩ f ⁻¹' {y}), g t ∂μHE[1] := harea
    _ = _ := lintegral_congr hfibers

/-- The length of a curve Lipschitz on `[a, b]` is the one-dimensional Hausdorff integral of its
fiber multiplicity. Infinite fibers have infinite multiplicity. -/
theorem eVariationOn_eq_lintegral_encard (hγ : LipschitzOnWith K γ (Icc a b)) :
    eVariationOn γ (Icc a b) =
      ∫⁻ y, (((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞)) ∂μHE[1] := by
  by_cases hab : a ≤ b
  · have hγu : LipschitzOnWith K γ (uIcc a b) := by rwa [uIcc_of_le hab]
    have hAC : AbsolutelyContinuousOnInterval γ a b := hγu.absolutelyContinuousOnInterval
    calc
      eVariationOn γ (Icc a b) = ∫⁻ t in uIoc a b, ‖deriv γ t‖ₑ := by
        rw [← uIcc_of_le hab]
        exact hAC.eVariationOn_eq_lintegral_enorm_deriv
      _ = ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ := by
        rw [uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc]
      _ = _ := by
        simpa only [mul_one, ENNReal.tsum_set_one] using
          hγ.lintegral_enorm_deriv_mul_eq_lintegral_tsum (g := fun _ ↦ 1) measurable_const
  · simp [Icc_eq_empty hab]

end LipschitzOnWith

namespace ContinuousOn

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {γ : ℝ → V} {a b : ℝ}

/-- **Banach indicatrix formula for curves.** The length of a continuous curve on `[a, b]` is the
one-dimensional Hausdorff integral of the extended cardinality of its fibers. No Lipschitz or
bounded-variation hypothesis is needed: both sides are infinite together. Pauses and repeated
traversals are allowed, and infinite fibers have infinite multiplicity. -/
theorem eVariationOn_eq_lintegral_encard (hγ : ContinuousOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) =
      ∫⁻ y, (((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞)) ∂μHE[1] := by
  refine le_antisymm (by
    rw [Measure.euclideanHausdorffMeasure_one]
    exact hγ.eVariationOn_le_lintegral_encard) ?_
  by_cases hbv : BoundedVariationOn γ (Icc a b)
  swap
  · rw [BoundedVariationOn, not_ne_iff] at hbv
    rw [hbv]
    exact le_top
  by_cases hab : a ≤ b
  swap
  · simp [Icc_eq_empty hab]
  -- Factor `γ` through cumulative arclength and compare fibers with those of the factor.
  obtain ⟨g, hg, hfac, hvar⟩ := hbv.exists_arclength_factorization hγ hab
  set L := (eVariationOn γ (Icc a b)).toReal with hL
  let s := variationOnFromTo γ (Icc a b) a
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hm : MonotoneOn s (Icc a b) :=
    variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn ha
  have hsa : s a = 0 := variationOnFromTo.self _ _ _
  have hsb : s b = L := by
    simp only [s, variationOnFromTo.eq_of_le _ _ hab, inter_self, L]
  have hs : MapsTo s (Icc a b) (Icc 0 L) := fun t ht ↦
    ⟨hsa ▸ hm ha ht ht.1, hsb ▸ hm ht (right_mem_Icc.mpr hab) ht.2⟩
  -- Two parameters in one fiber with the same arclength bound a pause of `γ`. The values
  -- taken on pauses form a countable set, hence a null set.
  let P := {y | ∃ t ∈ Icc a b, ∃ t' ∈ Icc a b, t < t' ∧ s t = s t' ∧ γ t = y}
  have hPnull : μHE[1] P = 0 := by
    rw [Measure.euclideanHausdorffMeasure_one]
    have := Measure.nullSingletonClass_hausdorff V (show (0 : ℝ) < 1 by norm_num)
    exact (hm.countable_setOf_eq_comp hfac).measure_zero _
  have hfib : ∀ᵐ y ∂μHE[1], ((Icc a b ∩ γ ⁻¹' {y}).encard : ℝ≥0∞) ≤
      ((Icc 0 L ∩ g ⁻¹' {y}).encard : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hPnull] with y hy
    rw [ENat.toENNReal_le]
    refine encard_le_encard_of_injOn (f := s) (fun t ht ↦ ⟨hs ht.1, ?_⟩) ?_
    · exact (hfac ht.1).trans ht.2
    · intro t ht t' ht' hst
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hy ⟨t, ht.1, t', ht'.1, h, hst, ht.2⟩
      · exact hy ⟨t', ht'.1, t, ht.1, h, hst.symm, ht'.2⟩
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  calc
    _ ≤ ∫⁻ y, ((Icc 0 L ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[1] := lintegral_mono_ae hfib
    _ = eVariationOn g (Icc 0 L) := hg.eVariationOn_eq_lintegral_encard.symm
    _ = eVariationOn γ (Icc a b) := by
      rw [hvar 0 (left_mem_Icc.mpr hL0) L (right_mem_Icc.mpr hL0) hL0, sub_zero, hL,
        ENNReal.ofReal_toReal hbv]

end ContinuousOn
