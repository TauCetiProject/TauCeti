/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Real-valued area integration with multiplicity

The area formula with extended nonnegative weights remains meaningful when either side is
infinite. When its parameter-side integral is finite, almost every weighted fiber is summable.
The extended formula can then be read as an equality of ordinary real integrals, with the weight
on the target given by the sum over the fiber.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

open Set Function MeasureTheory Measure Module Filter
open scoped ENNReal NNReal

namespace LipschitzWith

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {g : U → ℝ≥0} {K : ℝ≥0}

/-- If the weighted Jacobian has finite integral, then so does the extended weighted
multiplicity on the target. This is the extended area formula read through the finiteness
hypothesis, and is the common input for the real-valued results below. -/
theorem lintegral_tsum_fiber_ne_top
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet * (g x : ℝ)) s) :
    ∫⁻ y, ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ≥0∞) ∂μHE[finrank ℝ U] ≠ ∞ := by
  rw [← hf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum hs hg.coe_nnreal_ennreal]
  simpa only [ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), ENNReal.ofReal_coe_nnreal]
    using hint.lintegral_lt_top.ne

/-- If the weighted Jacobian has finite integral, then the real weights on almost every fiber
are summable. This is the finiteness statement needed before passing from the extended area
formula to an ordinary integral. -/
theorem ae_summable_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet * (g x : ℝ)) s) :
    ∀ᵐ y ∂μHE[finrank ℝ U], Summable fun x : ↥(s ∩ f ⁻¹' {y}) ↦ (g x : ℝ) := by
  let G : V → ℝ≥0∞ := fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ≥0∞)
  have hg' : Measurable fun x ↦ (g x : ℝ≥0∞) := hg.coe_nnreal_ennreal
  have hG : AEMeasurable G μHE[finrank ℝ U] := hf.aemeasurable_tsum_fiber hs hg'
  have hGfinite : ∫⁻ y, G y ∂μHE[finrank ℝ U] ≠ ∞ := hf.lintegral_tsum_fiber_ne_top hs hg hint
  filter_upwards [ae_lt_top' hG hGfinite] with y hy
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hy.ne

/-- Under the finite-integral hypothesis, the real weighted multiplicity is integrable on the
target. Nonsummable fiber weights cause no totalization issue: by
`LipschitzWith.ae_summable_fiber` they occur only on a Hausdorff-null set. Fibers themselves may
be infinite, e.g. where the weight vanishes. -/
theorem integrable_tsum_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet * (g x : ℝ)) s) :
    Integrable (fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ))
      μHE[finrank ℝ U] := by
  let G : V → ℝ≥0∞ := fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ≥0∞)
  have hg' : Measurable fun x ↦ (g x : ℝ≥0∞) := hg.coe_nnreal_ennreal
  have hG : AEMeasurable G μHE[finrank ℝ U] := hf.aemeasurable_tsum_fiber hs hg'
  have hGfinite : ∫⁻ y, G y ∂μHE[finrank ℝ U] ≠ ∞ := hf.lintegral_tsum_fiber_ne_top hs hg hint
  refine (integrable_toReal_of_lintegral_ne_top hG hGfinite).congr ?_
  exact Filter.Eventually.of_forall fun y ↦ by
    simpa only [ENNReal.coe_toReal] using
      (ENNReal.tsum_toReal_eq
        (f := fun x : ↥(s ∩ f ⁻¹' {y}) ↦ (g x : ℝ≥0∞)) fun _ ↦ ENNReal.coe_ne_top)

/-- **The real weighted area formula with multiplicity.** If the nonnegative weighted
Jacobian has finite integral, its ordinary integral equals the integral of the real sum of the
weights over each fiber. Both real-valued integrands are integrable. -/
theorem integral_normDet_fderiv_mul_eq_integral_tsum
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume) (hg : Measurable g)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet * (g x : ℝ)) s) :
    ∫ x in s, (fderiv ℝ f x).normDet * (g x : ℝ) =
      ∫ y, ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ) ∂μHE[finrank ℝ U] := by
  let A : U → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (fderiv ℝ f x).normDet * (g x : ℝ≥0∞)
  let G : V → ℝ≥0∞ := fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ≥0∞)
  have hJ : Measurable fun x ↦ (fderiv ℝ f x).normDet :=
    ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f)
  have hA : AEMeasurable A (volume.restrict s) :=
    ((ENNReal.measurable_ofReal.comp hJ).mul hg.coe_nnreal_ennreal).aemeasurable.restrict
  have hApoint : ∀ x, A x < ∞ := fun x ↦ ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  have hg' : Measurable fun x ↦ (g x : ℝ≥0∞) := hg.coe_nnreal_ennreal
  have hG : AEMeasurable G μHE[finrank ℝ U] := hf.aemeasurable_tsum_fiber hs hg'
  have harea := hf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum hs hg'
  have hGfinite : ∫⁻ y, G y ∂μHE[finrank ℝ U] ≠ ∞ := hf.lintegral_tsum_fiber_ne_top hs hg hint
  have hGpoint : ∀ᵐ y ∂μHE[finrank ℝ U], G y < ∞ := ae_lt_top' hG hGfinite
  calc
    ∫ x in s, (fderiv ℝ f x).normDet * (g x : ℝ) =
        (∫⁻ x in s, A x).toReal := by
      rw [← integral_toReal hA (Filter.Eventually.of_forall hApoint)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [A, ENNReal.toReal_mul, ENNReal.toReal_ofReal
          (LinearMap.normDet_nonneg _), ENNReal.coe_toReal]
    _ = (∫⁻ y, G y ∂μHE[finrank ℝ U]).toReal := congrArg ENNReal.toReal harea
    _ = ∫ y, (G y).toReal ∂μHE[finrank ℝ U] := (integral_toReal hG hGpoint).symm
    _ = ∫ y, ∑' x : ↥(s ∩ f ⁻¹' {y}), (g x : ℝ) ∂μHE[finrank ℝ U] := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        simpa only [G, ENNReal.coe_toReal] using
          (ENNReal.tsum_toReal_eq
            (f := fun x : ↥(s ∩ f ⁻¹' {y}) ↦ (g x : ℝ≥0∞)) fun _ ↦ ENNReal.coe_ne_top)

/-- If the Jacobian is integrable, then almost every fiber of the Lipschitz map over the
parameter set is finite. -/
theorem ae_finite_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) s) :
    ∀ᵐ y ∂μHE[finrank ℝ U], (s ∩ f ⁻¹' {y}).Finite := by
  have hsum := hf.ae_summable_fiber hs (g := fun _ ↦ 1) measurable_const (by simpa using hint)
  filter_upwards [hsum] with y hy
  exact Set.finite_coe_iff.mp (Finite.of_summable_const zero_lt_one hy)

/-- If the Jacobian is integrable, then the real-valued cardinality of the fiber is
integrable with respect to normalized Hausdorff measure. -/
theorem integrable_ncard_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) s) :
    Integrable (fun y ↦ ((s ∩ f ⁻¹' {y}).ncard : ℝ)) μHE[finrank ℝ U] := by
  have h := hf.integrable_tsum_fiber hs (g := fun _ ↦ 1) measurable_const (by simpa using hint)
  refine h.congr ?_
  filter_upwards [hf.ae_finite_fiber hs hint] with y hy
  let _ : Finite ↥(s ∩ f ⁻¹' {y}) := Set.finite_coe_iff.mpr hy
  simp

/-- The real unweighted area formula: an integrable Jacobian integrates to the ordinary
cardinality of the fiber. Almost every fiber is finite by `LipschitzWith.ae_finite_fiber`. -/
theorem integral_normDet_fderiv_eq_integral_ncard
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) s) :
    ∫ x in s, (fderiv ℝ f x).normDet =
      ∫ y, ((s ∩ f ⁻¹' {y}).ncard : ℝ) ∂μHE[finrank ℝ U] := by
  have h := hf.integral_normDet_fderiv_mul_eq_integral_tsum hs (g := fun _ ↦ 1)
    measurable_const (by simpa using hint)
  calc
    ∫ x in s, (fderiv ℝ f x).normDet =
        ∫ y, ∑' _ : ↥(s ∩ f ⁻¹' {y}), (1 : ℝ) ∂μHE[finrank ℝ U] := by
      simpa using h
    _ = ∫ y, ((s ∩ f ⁻¹' {y}).ncard : ℝ) ∂μHE[finrank ℝ U] := by
      apply integral_congr_ae
      filter_upwards [hf.ae_finite_fiber hs hint] with y hy
      let _ : Finite ↥(s ∩ f ⁻¹' {y}) := Set.finite_coe_iff.mpr hy
      simp

end LipschitzWith
