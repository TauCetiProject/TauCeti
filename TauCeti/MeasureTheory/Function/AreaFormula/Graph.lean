/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import TauCeti.Analysis.Normed.Lp.GraphDomain
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Surface measure on Lipschitz graphs

The normal graph parametrization of a function `φ : E → ℝ` sends `y` to `(φ y, y)` in the
Euclidean product `WithLp 2 (ℝ × E)`. When `φ` is `K`-Lipschitz, this parametrization is
`(K + 1)`-Lipschitz and its inverse on the graph, the second projection, is `1`-Lipschitz.
Consequently, normalized Hausdorff measure on the graph is quantitatively equivalent to volume
measure on the parameter space.

The exact weighted surface-integration formula on such a graph is the area formula for injective
Lipschitz maps, `LipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul`, applied to the
graph parametrization: integration over the graph with normalized Euclidean Hausdorff measure is
integration over the parameter space against the geometric Jacobian of the graph map, whose
derivative is the graph `x ↦ (A x, x)` of the derivative `A` of `φ`. The unweighted form computes
the surface measure of every measurable graph patch. These results allow an `L²` trace
constructed in graph coordinates to be interpreted as a trace with respect to Euclidean surface
measure.

## Main declarations

* `ContinuousLinearMap.normalGraphL`: the continuous linear graph map `x ↦ (A x, x)`.
* `HasFDerivAt.normalGraphEmbedding`: the derivative of a graph parametrization is the graph of
  the derivative.
* `LipschitzWith.lintegral_normalGraphEmbedding_image_eq_lintegral_normDet_fderiv_mul`: the
  weighted graph area formula.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral`: the
  surface-measure formula for a graph patch.
* `TauCeti.volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image`: surface measure on
  a graph dominates volume in the parameter space.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le`: the reverse bound for
  a Lipschitz graph.
* `LipschitzWith.map_volume_normalGraphEmbedding_le_surfaceMeasure` and
  `LipschitzWith.surfaceMeasure_le_smul_map_volume_normalGraphEmbedding`: the corresponding
  comparison of measures on the graph.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff`: null sets
  correspond under a Lipschitz graph parametrization.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §8.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula and Lipschitz graphs).
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped ENNReal NNReal

namespace TauCeti

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear graph map `x ↦ (A x, x)` associated to `A : E →L[ℝ] ℝ`. -/
def _root_.ContinuousLinearMap.normalGraphL (A : E →L[ℝ] ℝ) :
    E →L[ℝ] WithLp 2 (ℝ × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap ∘L
    A.prod (ContinuousLinearMap.id ℝ E)

/-- The continuous linear graph map is the normal graph parametrization of `A`. -/
@[simp]
theorem _root_.ContinuousLinearMap.normalGraphL_apply (A : E →L[ℝ] ℝ) (x : E) :
    A.normalGraphL x = normalGraphEmbedding A x :=
  (WithLp.ext_iff 2).2 <| Prod.ext (normalGraphEmbedding_fst A x).symm
    (normalGraphEmbedding_snd A x).symm

/-- The derivative of a graph parametrization is the graph of the derivative. -/
theorem _root_.HasFDerivAt.normalGraphEmbedding {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ φ' x) :
    HasFDerivAt (TauCeti.normalGraphEmbedding φ) φ'.normalGraphL x := by
  have h : TauCeti.normalGraphEmbedding φ =
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm ∘ fun y ↦ (φ y, y) :=
    funext fun y ↦ (WithLp.ext_iff 2).2 <| Prod.ext (normalGraphEmbedding_fst φ y)
      (normalGraphEmbedding_snd φ y)
  rw [h]
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm :
    (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).hasFDerivAt.comp x (hφ.prodMk (hasFDerivAt_id x))

/-- At a differentiability point, the Fréchet derivative of a graph parametrization is the
continuous linear graph of the derivative. -/
theorem _root_.DifferentiableAt.fderiv_normalGraphEmbedding {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (TauCeti.normalGraphEmbedding φ) x = (fderiv ℝ φ x).normalGraphL :=
  hφ.hasFDerivAt.normalGraphEmbedding.fderiv

end Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Weighted area formula for a Lipschitz graph.** Integration over a measurable graph patch
against normalized `dim E`-dimensional Hausdorff measure equals integration over its parameter
set against the graph Jacobian. The weight need not be measurable. -/
theorem _root_.LipschitzWith.lintegral_normalGraphEmbedding_image_eq_lintegral_normDet_fderiv_mul
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) {s : Set E} (hs : MeasurableSet s)
    (g : WithLp 2 (ℝ × E) → ℝ≥0∞) :
    ∫⁻ z in TauCeti.normalGraphEmbedding φ '' s, g z ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ (TauCeti.normalGraphEmbedding φ) x).normDet *
        g (TauCeti.normalGraphEmbedding φ x) :=
  hφ.normalGraphEmbedding.lintegral_image_eq_lintegral_normDet_fderiv_mul hs
    (injective_normalGraphEmbedding φ).injOn g

/-- **Surface measure of a Lipschitz graph.** The normalized `dim E`-dimensional Hausdorff
measure of a measurable graph patch is the integral of the geometric Jacobian of its graph
parametrization. -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) {s : Set E} (hs : MeasurableSet s) :
    μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ (TauCeti.normalGraphEmbedding φ) x).normDet :=
  (hφ.normalGraphEmbedding.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs
    (injective_normalGraphEmbedding φ).injOn).symm

/-- Euclidean surface measure of a normal graph dominates volume of its parameter set. This
lower bound uses only that the tangential projection is `1`-Lipschitz. -/
theorem volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image (φ : E → ℝ)
    (s : Set E) :
    volume s ≤ μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) := by
  let π : WithLp 2 (ℝ × E) → E := WithLp.snd
  have hπ : LipschitzWith 1 π := LipschitzWith.of_edist_le WithLp.edist_snd_le
  have h := hπ.lipschitzOnWith.euclideanHausdorffMeasure_image_le
    (finrank ℝ E) (s := TauCeti.normalGraphEmbedding φ '' s)
  have h_image : π '' (TauCeti.normalGraphEmbedding φ '' s) = s := by
    rw [image_image]
    simp only [π, normalGraphEmbedding_snd, image_id']
  rw [h_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  simpa using h

/-- The Euclidean surface measure of a `K`-Lipschitz normal graph over `s` is at most
`(K + 1) ^ dim E` times the volume of `s`. -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) (s : Set E) :
    μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) ≤
      (↑(K + 1) : ℝ≥0∞) ^ finrank ℝ E * volume s := by
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    hφ.normalGraphEmbedding.lipschitzOnWith.euclideanHausdorffMeasure_image_le
      (finrank ℝ E) (s := s)

/-- Pushing volume forward by a Lipschitz graph parametrization gives a measure bounded by
Euclidean surface measure restricted to the graph. -/
theorem _root_.LipschitzWith.map_volume_normalGraphEmbedding_le_surfaceMeasure
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) :
    Measure.map (TauCeti.normalGraphEmbedding φ) volume ≤
      (μHE[finrank ℝ E]).restrict (range (TauCeti.normalGraphEmbedding φ)) := by
  refine Measure.le_iff.2 fun t ht ↦ ?_
  rw [Measure.map_apply hφ.normalGraphEmbedding.continuous.measurable ht,
    Measure.restrict_apply ht]
  rw [← image_preimage_eq_inter_range]
  exact volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image φ _

/-- Euclidean surface measure restricted to a `K`-Lipschitz graph is at most
`(K + 1) ^ dim E` times the pushforward of volume by its parametrization. -/
theorem _root_.LipschitzWith.surfaceMeasure_le_smul_map_volume_normalGraphEmbedding
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) :
    (μHE[finrank ℝ E]).restrict (range (TauCeti.normalGraphEmbedding φ)) ≤
      (↑(K + 1) : ℝ≥0∞) ^ finrank ℝ E •
        Measure.map (TauCeti.normalGraphEmbedding φ) volume := by
  refine Measure.le_iff.2 fun t ht ↦ ?_
  rw [Measure.restrict_apply ht, Measure.smul_apply,
    Measure.map_apply hφ.normalGraphEmbedding.continuous.measurable ht]
  rw [← image_preimage_eq_inter_range]
  exact hφ.euclideanHausdorffMeasure_normalGraphEmbedding_image_le _

/-- A set has zero volume exactly when its image in a Lipschitz normal graph has zero Euclidean
surface measure. -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) (s : Set E) :
    μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) = 0 ↔ volume s = 0 := by
  constructor
  · intro h
    exact nonpos_iff_eq_zero.mp
      ((volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image φ s).trans_eq h)
  · intro h
    exact nonpos_iff_eq_zero.mp <|
      (hφ.euclideanHausdorffMeasure_normalGraphEmbedding_image_le s).trans_eq (by simp [h])

end TauCeti

end
