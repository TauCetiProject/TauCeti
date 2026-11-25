/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.Erf.Basic
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# A closed segment: the Gaussian frontier bound needs an open set

The closed segment `S = [0, 1] × {0}` of `ℝ²` is convex and Lebesgue-null, so its Gaussian
perimeter is `P_γ(S) = 0` (`gaussianPerimeter_segment`). Its interior is empty, so its frontier is
the segment itself (`frontier_segment`), whose Gaussian length is
`∫₀¹ (2π)⁻¹ e^{−t²/2} dt = φ(0) (Φ(1) − 1/2)` (`setLIntegral_frontier_segment`), which is
positive. So the identity `P_μ(C) = μ^{n−1}(∂C)` for open convex sets `C` fails for this closed
convex set: openness, or a nonempty interior, is needed.
-/

open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.GaussianSegment

/-- The first coordinate vector `e₁` of `ℝ²`. -/
def unitX : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The closed segment from `0` to `e₁` in `ℝ²`. -/
def closedSeg : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ 0 unitX

/-- The segment is the image of `[0, 1]` under `t ↦ t e₁`. -/
theorem closedSeg_eq_image : closedSeg = (fun t : ℝ => t • unitX) '' Icc 0 1 := by
  simp [closedSeg, segment_eq_image']

/-- The parametrization `t ↦ t e₁` of the first axis is an isometry. -/
theorem isometry_smul_unitX : Isometry fun t : ℝ => t • unitX :=
  Isometry.of_dist_eq fun s t => by
    rw [dist_eq_norm, ← sub_smul, norm_smul, unitX, PiLp.norm_single, norm_one, mul_one,
      Real.dist_eq, Real.norm_eq_abs]

/-- The segment is Lebesgue-null: it lies in the line `ℝ e₁`. -/
theorem volume_closedSeg : volume closedSeg = 0 := by
  have hne : (ℝ ∙ unitX) ≠ ⊤ := by
    intro h
    have h1 := finrank_span_singleton (K := ℝ) (v := unitX) (by simp [unitX])
    rw [h, finrank_top, finrank_euclideanSpace_fin] at h1
    omega
  refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_submodule volume _ hne)
  rw [closedSeg_eq_image] at hx
  obtain ⟨t, -, rfl⟩ := hx
  exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self unitX)

/-- **The Gaussian perimeter of the segment vanishes**: the segment is a null set. -/
theorem gaussianPerimeter_segment : gaussianPerimeter closedSeg = 0 := by
  rw [gaussianPerimeter_def, weightedPerimeter_congr_ae (t := ∅), weightedPerimeter_empty]
  exact (ae_eq_empty.2 volume_closedSeg).filter_mono ae_restrict_le

/-- The frontier of the segment is the segment itself: it is closed with empty interior. -/
theorem frontier_segment : frontier closedSeg = closedSeg := by
  have hc : IsClosed closedSeg := by
    rw [closedSeg_eq_image]
    exact (isCompact_Icc.image isometry_smul_unitX.continuous).isClosed
  rw [frontier, hc.closure_eq, Measure.interior_eq_empty_of_null volume_closedSeg, sdiff_empty]

/-- The Gaussian density at `t e₁` is `φ(0) φ(t)`. -/
theorem exp_neg_gaussianWeight_smul_unitX (t : ℝ) :
    Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) (t • unitX)) =
      gaussianPDFReal 0 1 0 * gaussianPDFReal 0 1 t := by
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [gaussianWeight_def, norm_smul, unitX, PiLp.norm_single, norm_one, mul_one,
    finrank_euclideanSpace_fin, gaussianPDFReal_def]
  simp only [Real.norm_eq_abs, sq_abs, NNReal.coe_one, mul_one, sub_zero, Nat.cast_ofNat]
  rw [show -(t ^ 2 / 2 + 2 / 2 * Real.log (2 * Real.pi)) =
      -Real.log (2 * Real.pi) + -t ^ 2 / 2 by ring, Real.exp_add, Real.exp_neg,
    Real.exp_log h2π]
  have hs : (√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt h2π.le]
  rw [show -(0 : ℝ) ^ 2 / 2 = 0 by norm_num, Real.exp_zero, mul_one, ← hs]
  ring

/-- **The Gaussian length of the segment** is `φ(0) (Φ(1) − 1/2)`. -/
theorem setLIntegral_frontier_segment :
    ∫⁻ x in frontier closedSeg,
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) ∂μHE[1] =
      ENNReal.ofReal (gaussianPDFReal 0 1 0 * (cdf (gaussianReal 0 1) 1 - 1 / 2)) := by
  have hm : MeasurableSet ((fun t : ℝ => t • unitX) '' Icc 0 1) :=
    (isCompact_Icc.image isometry_smul_unitX.continuous).isClosed.measurableSet
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) :=
    ((contDiff_gaussianWeight (n := 0)).continuous.measurable.neg.exp).ennreal_ofReal
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  rw [frontier_segment, closedSeg_eq_image,
    ← Measure.restrict_restrict_of_subset (image_subset_range _ _),
    ← isometry_smul_unitX.map_euclideanHausdorffMeasure,
    setLIntegral_map hm hmeas isometry_smul_unitX.continuous.measurable,
    preimage_image_eq _ isometry_smul_unitX.injective, hvol]
  simp only [exp_neg_gaussianWeight_smul_unitX]
  have hpdf : ∀ t, ENNReal.ofReal (gaussianPDFReal 0 1 0 * gaussianPDFReal 0 1 t) =
      ENNReal.ofReal (gaussianPDFReal 0 1 0) * gaussianPDF 0 1 t := fun t => by
    rw [gaussianPDF, ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  simp_rw [hpdf]
  have hI : gaussianReal 0 1 (Ioc 0 1) = ENNReal.ofReal (cdf (gaussianReal 0 1) 1 - 1 / 2) := by
    conv_lhs => rw [← measure_cdf (gaussianReal 0 1)]
    rw [StieltjesFunction.measure_Ioc, Probability.cdf_gaussianReal_self 0 one_ne_zero]
  rw [← setLIntegral_congr Ioc_ae_eq_Icc, lintegral_const_mul _ (measurable_gaussianPDF 0 1),
    ← gaussianReal_apply 0 one_ne_zero, hI, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]

/-- **The frontier bound is strict for the segment.** The Gaussian perimeter `0` of the closed
segment is strictly smaller than the Gaussian length of its frontier. -/
theorem gaussianPerimeter_segment_lt :
    gaussianPerimeter closedSeg <
      ∫⁻ x in frontier closedSeg,
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) ∂μHE[1] := by
  rw [gaussianPerimeter_segment, setLIntegral_frontier_segment, ENNReal.ofReal_pos]
  refine mul_pos (gaussianPDFReal_pos _ _ _ one_ne_zero) (sub_pos.2 ?_)
  rw [Probability.cdf_gaussianReal_zero_one]
  have := Real.erf_pos (x := 1 / √2) (by positivity)
  linarith

end TauCeti.Examples.GaussianSegment
