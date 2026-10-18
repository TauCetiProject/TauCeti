/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.WithLp
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.MeasureTheory.Function.AreaFormula.Integral
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Surface measure on Lipschitz graphs

The normal graph parametrization of a function `φ : E → ℝ` sends `y` to `(φ y, y)` in the
Euclidean product `WithLp 2 (ℝ × E)`. When `φ` is `K`-Lipschitz, this parametrization is
`(K + 1)`-Lipschitz and its inverse on the graph, the second projection, is `1`-Lipschitz.
Consequently, normalized Hausdorff measure on the graph is quantitatively equivalent to volume
measure on the parameter space.

For a differentiable graph, the geometric Jacobian of the parametrization is
`sqrt (1 + ‖fderiv ℝ φ x‖²)`. The weighted area formula therefore becomes the classical graph
surface-integration formula, with both extended nonnegative and Bochner integral versions. These
results allow an `L²` trace constructed in graph coordinates to be interpreted as a trace with
respect to Euclidean surface measure.

## Main declarations

* `TauCeti.volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image`: surface measure on
  a graph dominates volume in the parameter space.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le`: the reverse bound for
  a Lipschitz graph.
* `LipschitzWith.map_volume_normalGraphEmbedding_le_surfaceMeasure` and
  `LipschitzWith.surfaceMeasure_le_smul_map_volume_normalGraphEmbedding`: the corresponding
  comparison of measures on the graph.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff`: null sets
  correspond under a Lipschitz graph parametrization.
* `ContinuousLinearMap.normDet_normalGraphL`: the Jacobian of a linear normal graph.
* `TauCeti.lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul`:
  weighted surface integration on a differentiable normal graph.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula and Lipschitz graphs).
-/

public section

noncomputable section

open MeasureTheory Set Module Matrix
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The graph Jacobian -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The geometric Jacobian of the linear normal graph `x ↦ (A x, x)` is
`sqrt (1 + ‖A‖²)`. -/
theorem _root_.ContinuousLinearMap.normDet_normalGraphL (A : E →L[ℝ] ℝ) :
    A.normalGraphL.normDet = Real.sqrt (1 + ‖A‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ E
  let u : Fin (finrank ℝ E) → ℝ := fun i => A (b i)
  have hfst (v : E) : (A.normalGraphL v).ofLp.1 = A v := by
    change (A.normalGraphL v).fst = A v
    rw [ContinuousLinearMap.normalGraphL_apply, normalGraphEmbedding_fst]
  have hsnd (v : E) : (A.normalGraphL v).ofLp.2 = v := by
    change (A.normalGraphL v).snd = v
    rw [ContinuousLinearMap.normalGraphL_apply, normalGraphEmbedding_snd]
  have hgram : Matrix.gram ℝ (fun i => A.normalGraphL.toLinearMap (b i)) =
      1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit u := by
    ext i j
    simp only [Matrix.gram_apply]
    change inner ℝ (A.normalGraphL (b i)) (A.normalGraphL (b j)) = _
    simp only [WithLp.prod_inner_apply, hfst, hsnd]
    rw [(orthonormal_iff_ite.mp b.orthonormal i j)]
    simp [Matrix.mul_apply, u, Matrix.one_apply, mul_comm, add_comm]
  have hu : u ⬝ᵥ u = ‖A‖ ^ 2 := by
    let z := ContinuousLinearMap.adjoint A 1
    have hAz : A = innerSL ℝ z := by
      ext x
      simpa [z, real_inner_comm] using (ContinuousLinearMap.adjoint_inner_left A x 1).symm
    rw [hAz, innerSL_apply_norm]
    simp only [u, dotProduct, hAz, innerSL_apply_apply]
    simpa [real_inner_comm, real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner z z
  have hsq : A.normalGraphL.normDet ^ 2 = 1 + ‖A‖ ^ 2 := by
    have h := A.normalGraphL.toLinearMap.normDet_sq_eq_det_gram b
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h, hgram, Matrix.det_one_add_replicateCol_mul_replicateRow, hu]
  rw [← Real.sqrt_sq A.normalGraphL.normDet_nonneg, hsq]

omit [MeasurableSpace E] [BorelSpace E] in
/-- At a differentiability point, the geometric Jacobian of a normal graph parametrization is
the classical surface factor `sqrt (1 + ‖Dφ‖²)`. -/
theorem _root_.DifferentiableAt.normDet_fderiv_normalGraphEmbedding {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    (fderiv ℝ (normalGraphEmbedding φ) x).normDet =
      Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2) := by
  rw [hφ.fderiv_normalGraphEmbedding, ContinuousLinearMap.normDet_normalGraphL]

/-! ### Exact surface integration -/

/-- Weighted surface integration on a differentiable normal graph. The weight is allowed to be
nonmeasurable and both sides are extended nonnegative integrals. -/
theorem lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul
    {φ : E → ℝ} {s : Set E} (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x) (g : WithLp 2 (ℝ × E) → ℝ≥0∞) :
    ∫⁻ y in normalGraphEmbedding φ '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2)) *
        g (normalGraphEmbedding φ x) := by
  rw [lintegral_image_eq_lintegral_normDet_fderiv_mul (f := normalGraphEmbedding φ) hs
    (fun x hx => (hφ x hx).hasFDerivAt.normalGraphEmbedding.differentiableAt)
    (fun x hx => by
      rw [(hφ x hx).fderiv_normalGraphEmbedding]
      exact (fderiv ℝ φ x).injective_normalGraphL)
    (injective_normalGraphEmbedding φ).injOn]
  exact setLIntegral_congr_fun hs fun x hx => by
    rw [(hφ x hx).normDet_fderiv_normalGraphEmbedding]

/-- The normalized Euclidean surface measure of a differentiable normal graph is the integral of
the classical surface factor `sqrt (1 + ‖Dφ‖²)`. -/
theorem
    euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq
    {φ : E → ℝ} {s : Set E} (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x) :
    μHE[finrank ℝ E] (normalGraphEmbedding φ '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2)) := by
  simpa only [Pi.one_apply, mul_one, setLIntegral_one, Measure.restrict_apply_univ] using
    (lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul
      hs hφ (fun _ => 1))

/-- Integrability on a differentiable normal graph is equivalent to integrability of the
pullback multiplied by the classical surface factor. -/
theorem integrableOn_normalGraphEmbedding_image_iff_integrableOn_sqrt_one_add_norm_fderiv_sq_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → ℝ} {s : Set E}
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x)
    (g : WithLp 2 (ℝ × E) → F) :
    IntegrableOn g (normalGraphEmbedding φ '' s) μHE[finrank ℝ E] ↔
      IntegrableOn (fun x => Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2) •
        g (normalGraphEmbedding φ x)) s := by
  rw [integrableOn_image_iff_integrableOn_normDet_fderiv_smul
    (f := normalGraphEmbedding φ) hs
    (fun x hx => (hφ x hx).hasFDerivAt.normalGraphEmbedding.differentiableAt)
    (fun x hx => by
      rw [(hφ x hx).fderiv_normalGraphEmbedding]
      exact (fderiv ℝ φ x).injective_normalGraphL)
    (injective_normalGraphEmbedding φ).injOn]
  exact integrableOn_congr_fun (fun x hx => by
    rw [(hφ x hx).normDet_fderiv_normalGraphEmbedding]) hs

/-- Bochner surface integration on a differentiable normal graph. Its two sides are integrable
simultaneously by
`TauCeti.integrableOn_normalGraphEmbedding_image_iff_integrableOn_sqrt_one_add_norm_fderiv_sq_smul`.
-/
theorem integral_normalGraphEmbedding_image_eq_integral_sqrt_one_add_norm_fderiv_sq_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → ℝ} {s : Set E}
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x)
    (g : WithLp 2 (ℝ × E) → F) :
    ∫ y in normalGraphEmbedding φ '' s, g y ∂μHE[finrank ℝ E] =
      ∫ x in s, Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2) •
        g (normalGraphEmbedding φ x) := by
  rw [integral_image_eq_integral_normDet_fderiv_smul (f := normalGraphEmbedding φ) hs
    (fun x hx => (hφ x hx).hasFDerivAt.normalGraphEmbedding.differentiableAt)
    (fun x hx => by
      rw [(hφ x hx).fderiv_normalGraphEmbedding]
      exact (fderiv ℝ φ x).injective_normalGraphL)
    (injective_normalGraphEmbedding φ).injOn]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [(hφ x hx).normDet_fderiv_normalGraphEmbedding]

/-! ### Lipschitz graph measure comparison -/

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
