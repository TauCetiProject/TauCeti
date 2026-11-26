/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.WithLp
public import TauCeti.MeasureTheory.Function.AreaFormula.Integral
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.MeasureTheory.Measure.LocallyNull

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

In every codimension, the graph of a Lipschitz map `φ : E → F` between finite-dimensional real
inner product spaces is parametrized by `x ↦ (x, φ x)` in `WithLp 2 (E × F)`. Its
`dim E`-dimensional Euclidean Hausdorff measure over `s` is `∫_s sqrt (det (I + Dφ† Dφ))`, which
reduces to the normal-graph factor `sqrt (1 + ‖Dφ‖²)` when `F = ℝ`.

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
* `TauCeti.lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul`:
  weighted surface integration on a differentiable normal graph.
* `euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq`:
  the surface measure of a differentiable normal graph.
* `integrableOn_normalGraphEmbedding_image_iff_integrableOn_sqrt_one_add_norm_fderiv_sq_smul`:
  integrability on a differentiable normal graph.
* `TauCeti.integral_normalGraphEmbedding_image_eq_integral_sqrt_one_add_norm_fderiv_sq_smul`:
  Bochner surface integration on a differentiable normal graph.
* `lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul`, in the
  namespaces `LipschitzWith` and `LipschitzOnWith`: weighted surface integration on the graph of a
  Lipschitz function, on the whole space or on an open set. The surface factor
  `sqrt (1 + ‖Dφ‖²)` is defined almost everywhere, by Rademacher's theorem.
* `restrict_euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_map_withDensity`, in the
  namespace `LipschitzOnWith`: the **Lipschitz-graph surface measure**. For `φ` Lipschitz on an
  open `U`, surface measure on the graph of `φ` over a measurable `s ⊆ U` is the pushforward of
  `sqrt (1 + ‖Dφ‖²) dx` on `s` under `x ↦ (φ x, x)`. The lemma of the same name in the namespace
  `LipschitzWith` is the case of a function Lipschitz on the whole space.
* `ContinuousLinearMap.euclideanHausdorffMeasure_normalGraphEmbedding_image` and
  `TauCeti.euclideanHausdorffMeasure_normalGraphEmbedding_id_image_Ioo`: the graph of a linear
  function `ℓ` over `s` has surface measure `sqrt (1 + ‖ℓ‖²) |s|`; in particular the diagonal
  segment over `(0, 1)` has length `√2`.
* `LocallyLipschitzOn.lintegral_graph_image_eq_lintegral_sqrt_det_mul`: weighted integration on
  the graph `x ↦ (x, φ x)` of a map `φ : E → F` locally Lipschitz on an open set `U`, over a
  measurable `s ⊆ U`, in every codimension, against `sqrt (det (I + Dφ† Dφ)) dx`.
* `LocallyLipschitzOn.euclideanHausdorffMeasure_graph_image`: the **area of a locally Lipschitz
  graph in every codimension**. For `φ : E → F` between finite-dimensional real inner product
  spaces, locally Lipschitz on an open `U`, and a measurable `s ⊆ U`, the `dim E`-dimensional
  Euclidean Hausdorff measure of the graph `x ↦ (x, φ x)` over `s` is
  `∫_s sqrt (det (I + Dφ(x)† Dφ(x))) dx`.
* `LipschitzWith.lintegral_graph_image_eq_lintegral_sqrt_det_mul` and
  `LipschitzWith.euclideanHausdorffMeasure_graph_image`: the same for a Lipschitz `φ` and any
  measurable `s`.

The graph Jacobian itself, `DifferentiableAt.normDet_fderiv_normalGraphEmbedding`, is in
`TauCeti.Analysis.Calculus.FDeriv.WithLp`. For a Lipschitz `φ`, the graph parametrization is
Lipschitz and injective, so the area formula for injective Lipschitz maps
(`LipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul`) applies to it, and at the points
where `φ` is differentiable, almost every point by Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`), its Jacobian is the surface factor. A function Lipschitz
on an open set `U` agrees on `U` with a Lipschitz function on the whole space
(`LipschitzOnWith.extend_real`), with the same derivative at the points of `U`.

In higher codimension the graph parametrization is `x ↦ (x, φ x)`, whose derivative is the
linear graph of `Dφ(x)` (`DifferentiableAt.fderiv_graph`), with Jacobian `sqrt (det (I + A† A))`
(`ContinuousLinearMap.normDet_graphL`). For `φ` locally Lipschitz on an open `U`, the area formula
for injective maps with injective derivative
(`TauCeti.lintegral_image_eq_lintegral_normDet_fderiv_mul`) applies on the points of `s` where `φ`
is differentiable; the remaining points form a null set by Rademacher's theorem
(`LocallyLipschitzOn.ae_differentiableAt_of_mem`), and its image under the graph parametrization
is `H^{dim E}`-null because the parametrization is locally Lipschitz. A Lipschitz `φ` is the case
`U = univ`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula and Lipschitz graphs).
* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis 3, Australian National University, 1983, §8, 8.6(3) (the area of a `C¹` graph).
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

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
    (fun x hx => (hφ x hx).injective_fderiv_normalGraphEmbedding)
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
    (fun x hx => (hφ x hx).injective_fderiv_normalGraphEmbedding)
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
    (fun x hx => (hφ x hx).injective_fderiv_normalGraphEmbedding)
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
  rw [Measure.restrict_apply ht, _root_.smul_apply,
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

/-! ### Linear graphs -/

namespace ContinuousLinearMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The graph of a linear function `ℓ` over a measurable set `s` has surface measure
`sqrt (1 + ‖ℓ‖²)` times the volume of `s`. For `ℓ = 0` this is the volume of `s`: normalized
Hausdorff measure on a hyperplane is its volume. -/
theorem euclideanHausdorffMeasure_normalGraphEmbedding_image (ℓ : E →L[ℝ] ℝ) {s : Set E}
    (hs : MeasurableSet s) :
    μHE[finrank ℝ E] (normalGraphEmbedding ℓ '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖ℓ‖ ^ 2)) * volume s := by
  rw [euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq
    hs fun x _ => ℓ.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, setLIntegral_const]

end ContinuousLinearMap

namespace TauCeti

/-- The diagonal segment over `(0, 1)`, the graph of the identity of `ℝ`, has length `√2`. -/
theorem euclideanHausdorffMeasure_normalGraphEmbedding_id_image_Ioo :
    μHE[1] (normalGraphEmbedding id '' Ioo (0 : ℝ) 1) = ENNReal.ofReal (Real.sqrt 2) := by
  have h := (ContinuousLinearMap.id ℝ ℝ).euclideanHausdorffMeasure_normalGraphEmbedding_image
    (measurableSet_Ioo (a := 0) (b := 1))
  rw [ContinuousLinearMap.norm_id, Real.volume_Ioo, Module.finrank_self] at h
  norm_num at h
  exact h

end TauCeti

/-! ### Lipschitz graphs -/

namespace LipschitzWith

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {φ : E → ℝ} {s : Set E}

/-- **Weighted surface integration on a Lipschitz normal graph.** For a Lipschitz `φ : E → ℝ` and a
measurable `s ⊆ E`, the integral of a weight `g` over the graph of `φ` above `s`, against the
normalized Euclidean Hausdorff measure, is the integral over `s` of `g` along the graph
parametrization `x ↦ (φ x, x)` against `sqrt (1 + ‖Dφ‖²) dx`. The surface factor is defined at the
points where `φ` is differentiable, which is almost every point. The weight need not be
measurable. -/
theorem lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul
    (hφ : LipschitzWith K φ) (hs : MeasurableSet s) (g : WithLp 2 (ℝ × E) → ℝ≥0∞) :
    ∫⁻ y in TauCeti.normalGraphEmbedding φ '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2)) *
        g (TauCeti.normalGraphEmbedding φ x) := by
  rw [hφ.normalGraphEmbedding.lintegral_image_eq_lintegral_normDet_fderiv_mul hs
    (injective_normalGraphEmbedding φ).injOn g]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [hφ.ae_differentiableAt] with x hx _
  rw [hx.normDet_fderiv_normalGraphEmbedding]

/-- The normalized Euclidean surface measure of the graph of a Lipschitz function over a
measurable set `s` is the integral over `s` of the surface factor `sqrt (1 + ‖Dφ‖²)`. -/
theorem
    euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq
    (hφ : LipschitzWith K φ) (hs : MeasurableSet s) :
    μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2)) := by
  simpa only [Pi.one_apply, mul_one, setLIntegral_one, Measure.restrict_apply_univ] using
    hφ.lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul hs 1

/-- **The surface measure of a Lipschitz graph.** For a Lipschitz `φ : E → ℝ` and a measurable
`s ⊆ E`, the normalized Euclidean Hausdorff measure restricted to the graph of `φ` over `s` is the
pushforward of the measure `sqrt (1 + ‖Dφ‖²) dx` on `s` under `x ↦ (φ x, x)`. -/
theorem restrict_euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_map_withDensity
    (hφ : LipschitzWith K φ) (hs : MeasurableSet s) :
    (μHE[finrank ℝ E]).restrict (TauCeti.normalGraphEmbedding φ '' s) =
      Measure.map (TauCeti.normalGraphEmbedding φ) ((volume.restrict s).withDensity fun x =>
        ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2))) := by
  have hm : Measurable (TauCeti.normalGraphEmbedding φ) :=
    hφ.normalGraphEmbedding.continuous.measurable
  ext t ht
  rw [Measure.map_apply hm ht, withDensity_apply _ (hm ht), ← lintegral_indicator_one ht,
    hφ.lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul hs,
    ← lintegral_indicator (hm ht)]
  refine lintegral_congr fun x => ?_
  by_cases hx : TauCeti.normalGraphEmbedding φ x ∈ t <;> simp [indicator, hx]

end LipschitzWith

namespace LipschitzOnWith

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {φ : E → ℝ} {U s : Set E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function `φ` Lipschitz on an open set `U` agrees on `U` with a Lipschitz function `ψ` on the
whole space, whose graph parametrization and derivative are those of `φ` at the points of `U`. -/
private theorem exists_lipschitzWith_eqOn_normalGraphEmbedding_and_fderiv_eq
    (hφ : LipschitzOnWith K φ U) (hU : IsOpen U) :
    ∃ ψ : E → ℝ, LipschitzWith K ψ ∧
      EqOn (TauCeti.normalGraphEmbedding φ) (TauCeti.normalGraphEmbedding ψ) U ∧
      ∀ x ∈ U, fderiv ℝ φ x = fderiv ℝ ψ x := by
  obtain ⟨ψ, hψ, hφψ⟩ := hφ.extend_real
  refine ⟨ψ, hψ, fun x hx => ?_, fun x hx =>
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hφψ).fderiv_eq⟩
  rw [normalGraphEmbedding_apply, normalGraphEmbedding_apply, hφψ hx]

/-- **Weighted surface integration on a Lipschitz normal graph over an open set.** For `φ`
Lipschitz on an open set `U` and a measurable `s ⊆ U`, the integral of a weight `g` over the graph
of `φ` above `s`, against the normalized Euclidean Hausdorff measure, is the integral over `s` of
`g` along the graph parametrization `x ↦ (φ x, x)` against `sqrt (1 + ‖Dφ‖²) dx`. The weight need
not be measurable. -/
theorem lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul
    (hφ : LipschitzOnWith K φ U) (hU : IsOpen U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (g : WithLp 2 (ℝ × E) → ℝ≥0∞) :
    ∫⁻ y in TauCeti.normalGraphEmbedding φ '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2)) *
        g (TauCeti.normalGraphEmbedding φ x) := by
  obtain ⟨ψ, hψ, heq, hfd⟩ := hφ.exists_lipschitzWith_eqOn_normalGraphEmbedding_and_fderiv_eq hU
  rw [image_congr (heq.mono hsU),
    hψ.lintegral_normalGraphEmbedding_image_eq_lintegral_sqrt_one_add_norm_fderiv_sq_mul hs g]
  exact setLIntegral_congr_fun hs fun x hx => by rw [hfd x (hsU hx), heq (hsU hx)]

/-- **The surface measure of a Lipschitz graph over an open set.** For `φ` Lipschitz on an open set
`U` and a measurable `s ⊆ U`, for instance `s = U`, the normalized Euclidean Hausdorff measure
restricted to the graph of `φ` over `s` is the pushforward of the measure `sqrt (1 + ‖Dφ‖²) dx` on
`s` under `x ↦ (φ x, x)`. -/
theorem restrict_euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_map_withDensity
    (hφ : LipschitzOnWith K φ U) (hU : IsOpen U) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    (μHE[finrank ℝ E]).restrict (TauCeti.normalGraphEmbedding φ '' s) =
      Measure.map (TauCeti.normalGraphEmbedding φ) ((volume.restrict s).withDensity fun x =>
        ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2))) := by
  obtain ⟨ψ, hψ, heq, hfd⟩ := hφ.exists_lipschitzWith_eqOn_normalGraphEmbedding_and_fderiv_eq hU
  have hdens : ((volume.restrict s).withDensity fun x =>
      ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2))) =
      (volume.restrict s).withDensity fun x =>
        ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ ψ x‖ ^ 2)) :=
    withDensity_congr_ae ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun x hx => by
      simp only [hfd x (hsU hx)]))
  rw [image_congr (heq.mono hsU),
    hψ.restrict_euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_map_withDensity hs, hdens]
  refine Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le ?_)
  exact (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun x hx => (heq (hsU hx)).symm)

end LipschitzOnWith

/-! ### Lipschitz graphs in every codimension -/

namespace LocallyLipschitzOn

/-- For `φ` locally Lipschitz on a null set `t`, the graph parametrization `x ↦ (x, φ x)` maps
`t` to an `H^{dim E}`-null set. -/
theorem euclideanHausdorffMeasure_graph_image_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [EMetricSpace F] [MeasurableSpace F] [BorelSpace F] {φ : E → F} {t : Set E}
    (hφ : LocallyLipschitzOn t φ) (ht : volume t = 0) :
    μHE[finrank ℝ E] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' t) = 0 := by
  refine TauCeti.measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof t)
    fun x hx ↦ ?_
  obtain ⟨K, v, hv, hφv⟩ := hφ hx
  -- The graph parametrization is `(K + 1)`-Lipschitz on `v`.
  have hG : LipschitzOnWith (K + 1) (fun x ↦ WithLp.toLp 2 (x, φ x)) v := hφv.graph
  refine ⟨t ∩ v, Filter.inter_mem self_mem_nhdsWithin hv, nonpos_iff_eq_zero.1
    (((hG.mono inter_subset_right).euclideanHausdorffMeasure_image_le _).trans ?_)⟩
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    measure_mono_null inter_subset_left ht, mul_zero]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {φ : E → F} {U s : Set E}

/-- **Weighted integration on a locally Lipschitz graph.** For `φ : E → F` locally Lipschitz on an
open set `U` and a measurable `s ⊆ U`, the integral of a weight `g` over the graph of `φ` above `s`,
against the `dim E`-dimensional Euclidean Hausdorff measure, is the integral over `s` of `g` along
the graph parametrization `x ↦ (x, φ x)` against `sqrt (det (I + Dφ(x)† Dφ(x))) dx`. Here `Dφ(x)`
is `fderiv ℝ φ x`, the true derivative at almost every point of `U` by Rademacher's theorem. The
weight need not be measurable. -/
theorem lintegral_graph_image_eq_lintegral_sqrt_det_mul (hφ : LocallyLipschitzOn U φ)
    (hU : IsOpen U) (hs : MeasurableSet s) (hsU : s ⊆ U) (g : WithLp 2 (E × F) → ℝ≥0∞) :
    ∫⁻ y in (fun x ↦ WithLp.toLp 2 (x, φ x)) '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (LinearMap.det
        (1 + LinearMap.adjoint (fderiv ℝ φ x : E →ₗ[ℝ] F) ∘ₗ (fderiv ℝ φ x : E →ₗ[ℝ] F)))) *
        g (WithLp.toLp 2 (x, φ x)) := by
  set G : E → WithLp 2 (E × F) := fun x ↦ WithLp.toLp 2 (x, φ x)
  set S := {x | DifferentiableAt ℝ φ x}
  have hD : MeasurableSet (s ∩ S) := hs.inter (measurableSet_of_differentiableAt ℝ φ)
  -- The points of `s` where `φ` is not differentiable form a null set.
  have hnull : volume (s \ S) = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_)
      (ae_iff.1 (hφ.ae_differentiableAt_of_mem hU (μ := volume)))
    rw [mem_ofPred_eq]
    exact fun hd ↦ hx.2 (hd (hsU hx.1))
  have hsD : s ∩ S =ᵐ[volume] s :=
    ae_eq_set.2 ⟨measure_mono_null (fun x hx ↦ (hx.2 hx.1.1).elim) measure_empty,
      measure_mono_null (t := s \ S) (fun x hx ↦ ⟨hx.1, fun h ↦ hx.2 ⟨hx.1, h⟩⟩) hnull⟩
  have himg : G '' s =ᵐ[μHE[finrank ℝ E]] G '' (s ∩ S) := by
    rw [← inter_union_sdiff s S, image_union, inter_union_sdiff]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2
      ((hφ.mono (sdiff_subset.trans hsU)).euclideanHausdorffMeasure_graph_image_eq_zero hnull))
  rw [setLIntegral_congr himg, TauCeti.lintegral_image_eq_lintegral_normDet_fderiv_mul hD
    (fun x hx ↦ hx.2.hasFDerivAt.graph.differentiableAt)
    (fun x hx ↦ by rw [hx.2.fderiv_graph]; exact ContinuousLinearMap.injective_graphL _)
    (fun x _ y _ hxy ↦ congrArg Prod.fst (WithLp.toLp_injective 2 hxy)) g,
    ← setLIntegral_congr hsD]
  exact setLIntegral_congr_fun hD fun x hx ↦ by
    rw [hx.2.fderiv_graph, ContinuousLinearMap.normDet_graphL]

/-- **The area of a locally Lipschitz graph.** For `φ : E → F` locally Lipschitz on an open set
`U` and a measurable `s ⊆ U`, the `dim E`-dimensional Euclidean Hausdorff measure of the graph of
`φ` over `s` is `∫_s sqrt (det (I + Dφ(x)† Dφ(x))) dx`. -/
theorem euclideanHausdorffMeasure_graph_image (hφ : LocallyLipschitzOn U φ) (hU : IsOpen U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    μHE[finrank ℝ E] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (LinearMap.det
        (1 + LinearMap.adjoint (fderiv ℝ φ x : E →ₗ[ℝ] F) ∘ₗ (fderiv ℝ φ x : E →ₗ[ℝ] F)))) := by
  simpa only [Pi.one_apply, mul_one, setLIntegral_one, Measure.restrict_apply_univ] using
    hφ.lintegral_graph_image_eq_lintegral_sqrt_det_mul hU hs hsU 1

end LocallyLipschitzOn

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {K : ℝ≥0} {φ : E → F} {s : Set E}

/-- **Weighted integration on a Lipschitz graph.** For a Lipschitz `φ : E → F` and a measurable
`s ⊆ E`, the integral of a weight `g` over the graph of `φ` above `s`, against the
`dim E`-dimensional Euclidean Hausdorff measure, is the integral over `s` of `g` along the graph
parametrization `x ↦ (x, φ x)` against `sqrt (det (I + Dφ(x)† Dφ(x))) dx`. Here `Dφ(x)` is
`fderiv ℝ φ x`, which is the true derivative at almost every point by Rademacher's theorem; the
remaining null set does not affect the integral. The weight need not be measurable. This is the
case `U = univ` of `LocallyLipschitzOn.lintegral_graph_image_eq_lintegral_sqrt_det_mul`. -/
theorem lintegral_graph_image_eq_lintegral_sqrt_det_mul (hφ : LipschitzWith K φ)
    (hs : MeasurableSet s) (g : WithLp 2 (E × F) → ℝ≥0∞) :
    ∫⁻ y in (fun x ↦ WithLp.toLp 2 (x, φ x)) '' s, g y ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (LinearMap.det
        (1 + LinearMap.adjoint (fderiv ℝ φ x : E →ₗ[ℝ] F) ∘ₗ (fderiv ℝ φ x : E →ₗ[ℝ] F)))) *
        g (WithLp.toLp 2 (x, φ x)) :=
  hφ.locallyLipschitz.locallyLipschitzOn.lintegral_graph_image_eq_lintegral_sqrt_det_mul isOpen_univ
    hs (subset_univ s) g

/-- **The area of a Lipschitz graph.** For a Lipschitz `φ : E → F` and a measurable `s ⊆ E`, the
`dim E`-dimensional Euclidean Hausdorff measure of the graph of `φ` over `s` is
`∫_s sqrt (det (I + Dφ(x)† Dφ(x))) dx`. Here `Dφ(x)` is `fderiv ℝ φ x`, which is the true
derivative at almost every point by Rademacher's theorem; the remaining null set does not affect
the integral. -/
theorem euclideanHausdorffMeasure_graph_image (hφ : LipschitzWith K φ) (hs : MeasurableSet s) :
    μHE[finrank ℝ E] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (LinearMap.det
        (1 + LinearMap.adjoint (fderiv ℝ φ x : E →ₗ[ℝ] F) ∘ₗ (fderiv ℝ φ x : E →ₗ[ℝ] F)))) := by
  simpa only [Pi.one_apply, mul_one, setLIntegral_one, Measure.restrict_apply_univ] using
    hφ.lintegral_graph_image_eq_lintegral_sqrt_det_mul hs 1

end LipschitzWith

end
