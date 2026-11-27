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
import TauCeti.Analysis.Convex.Topology
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# A closed segment: the Gaussian frontier bound needs an open set

The closed segment `S = [0, 1] × {0}` of `ℝ²` is convex and Lebesgue-null, so its Gaussian
perimeter is `P_γ(S) = 0` (`gaussianPerimeter_closedSeg`). Its interior is empty, so its frontier
is the segment itself (`frontier_closedSeg`), whose Gaussian length is
`∫₀¹ (2π)⁻¹ e^{−t²/2} dt = φ(0) (Φ(1) − 1/2)` (`setLIntegral_frontier_closedSeg`), which is
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
private theorem closedSeg_eq_image : closedSeg = (fun t : ℝ => t • unitX) '' Icc 0 1 := by
  simp [closedSeg, segment_eq_image']

/-- The norm of `t e₁` is `|t|`. -/
private theorem norm_smul_unitX (t : ℝ) : ‖t • unitX‖ = |t| := by
  rw [norm_smul, unitX, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- The parametrization `t ↦ t e₁` of the first axis is an isometry. -/
private theorem isometry_smul_unitX : Isometry fun t : ℝ => t • unitX :=
  (LinearIsometry.toSpanSingleton ℝ _ (by simpa using norm_smul_unitX 1)).isometry

/-- The segment is closed. -/
private theorem isClosed_closedSeg : IsClosed closedSeg :=
  (TauCeti.isCompact_segment ℝ 0 unitX).isClosed

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
theorem gaussianPerimeter_closedSeg : gaussianPerimeter closedSeg = 0 := by
  rw [gaussianPerimeter_congr_ae (ae_eq_empty.2 volume_closedSeg), gaussianPerimeter_empty]

/-- The frontier of the segment is the segment itself: it is closed with empty interior. -/
theorem frontier_closedSeg : frontier closedSeg = closedSeg := by
  rw [frontier, isClosed_closedSeg.closure_eq, Measure.interior_eq_empty_of_null volume_closedSeg,
    sdiff_empty]

/-- The Gaussian density at `t e₁` is `φ(0) φ(t)`. -/
private theorem exp_neg_gaussianWeight_smul_unitX (t : ℝ) :
    Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) (t • unitX)) =
      gaussianPDFReal 0 1 0 * gaussianPDFReal 0 1 t := by
  have hs : (2 * Real.pi) ^ (-((2 : ℕ) : ℝ) / 2) = (√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    norm_num [Real.rpow_neg_one]
  rw [exp_neg_gaussianWeight_of_norm_eq (norm_smul_unitX t), finrank_euclideanSpace_fin, hs]
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, sq_abs, neg_div,
    zero_pow two_ne_zero, zero_div, neg_zero, Real.exp_zero]
  ring

/-- The integral `∫₀¹ φ(0) φ(t) dt` equals `φ(0) (Φ(1) − 1/2)`. -/
private theorem setLIntegral_Icc_gaussianPDFReal :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (gaussianPDFReal 0 1 0 * gaussianPDFReal 0 1 t) =
      ENNReal.ofReal (gaussianPDFReal 0 1 0 * (cdf (gaussianReal 0 1) 1 - 1 / 2)) := by
  have hI : gaussianReal 0 1 (Ioc 0 1) = ENNReal.ofReal (cdf (gaussianReal 0 1) 1 - 1 / 2) := by
    conv_lhs => rw [← measure_cdf (gaussianReal 0 1)]
    rw [StieltjesFunction.measure_Ioc, Probability.cdf_gaussianReal_self 0 one_ne_zero]
  rw [gaussianReal_apply 0 one_ne_zero, gaussianPDF_def] at hI
  simp_rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 0), ← hI]
  rw [lintegral_const_mul _ (measurable_gaussianPDFReal 0 1).ennreal_ofReal,
    setLIntegral_congr Ioc_ae_eq_Icc]

/-- **The Gaussian length of the segment** is `φ(0) (Φ(1) − 1/2)`. -/
theorem setLIntegral_frontier_closedSeg :
    ∫⁻ x in frontier closedSeg,
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) ∂μHE[1] =
      ENNReal.ofReal (gaussianPDFReal 0 1 0 * (cdf (gaussianReal 0 1) 1 - 1 / 2)) := by
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) :=
    ((contDiff_gaussianWeight (n := 0)).continuous.measurable.neg.exp).ennreal_ofReal
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  rw [frontier_closedSeg, closedSeg_eq_image,
    ← isometry_smul_unitX.map_euclideanHausdorffMeasure_restrict,
    lintegral_map hmeas isometry_smul_unitX.continuous.measurable, hvol]
  simp only [exp_neg_gaussianWeight_smul_unitX]
  exact setLIntegral_Icc_gaussianPDFReal

/-- **The frontier bound is strict for the segment.** The Gaussian perimeter `0` of the closed
segment is strictly smaller than the Gaussian length of its frontier. -/
theorem gaussianPerimeter_closedSeg_lt :
    gaussianPerimeter closedSeg <
      ∫⁻ x in frontier closedSeg,
        ENNReal.ofReal (Real.exp (-gaussianWeight (EuclideanSpace ℝ (Fin 2)) x)) ∂μHE[1] := by
  rw [gaussianPerimeter_closedSeg, setLIntegral_frontier_closedSeg, ENNReal.ofReal_pos]
  refine mul_pos (gaussianPDFReal_pos _ _ _ one_ne_zero) (sub_pos.2 ?_)
  simpa [Probability.cdf_gaussianReal_self 0 one_ne_zero] using
    Probability.strictMono_cdf_gaussianReal 0 one_ne_zero (zero_lt_one' ℝ)

end TauCeti.Examples.GaussianSegment
