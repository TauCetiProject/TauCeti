/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
import TauCeti.Analysis.InnerProductSpace.NormDet

/-!
# The area formula for Lipschitz curves

This file specializes the area formula with multiplicity to maps from a real interval. For a
Lipschitz curve, its total variation is the one-dimensional Hausdorff integral of the extended
cardinality of its fibers. Thus length counts repeated traversals, while the Hausdorff measure of
the trace does not.

The curve need only be Lipschitz on the parameter interval. A finite-dimensional Lipschitz
extension reduces the result to the global area formula; derivatives and fiber sums are then
transported back to the original curve. The one-dimensional geometric Jacobian is identified
with the norm of the velocity.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, Section 3.3 (the area formula for Lipschitz maps).
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
