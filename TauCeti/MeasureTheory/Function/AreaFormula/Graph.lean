/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Surface measure on Lipschitz graphs

The normal graph parametrization of a function `φ : E → ℝ` sends `y` to `(φ y, y)` in the
Euclidean product `WithLp 2 (ℝ × E)`. When `φ` is `K`-Lipschitz, this parametrization is
`(K + 1)`-Lipschitz and its inverse on the graph, the second projection, is `1`-Lipschitz.
Consequently, normalized Hausdorff measure on the graph is quantitatively equivalent to volume
measure on the parameter space.

The exact weighted surface-integration formula is also recorded. Its density is the geometric
Jacobian `(fderiv ℝ (normalGraphEmbedding φ) y).normDet`, as supplied by the area formula for
injective Lipschitz maps. These results allow an `L²` trace constructed in graph coordinates to be
interpreted as a trace with respect to Euclidean surface measure.

## Main declarations

* `TauCeti.normalGraphEmbedding`: the parametrization `y ↦ (φ y, y)`.
* `LipschitzWith.normalGraphEmbedding`: its Lipschitz bound.
* `TauCeti.volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image`: surface measure on
  a graph dominates volume in the parameter space.
* `LipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le`: the reverse bound for
  a Lipschitz graph.
* `LipschitzWith.map_volume_normalGraphEmbedding_le_surfaceMeasure` and
  `LipschitzWith.surfaceMeasure_le_smul_map_volume_normalGraphEmbedding`: the corresponding
  comparison of measures on the graph.
* `LipschitzWith.lintegral_normalGraphEmbedding_image_eq`: weighted integration on a Lipschitz
  graph in parameter coordinates.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula and Lipschitz graphs).
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The normal graph parametrization `y ↦ (φ y, y)` in the Euclidean product `ℝ × E`. -/
def normalGraphEmbedding (φ : E → ℝ) (y : E) : WithLp 2 (ℝ × E) :=
  WithLp.toLp 2 (φ y, y)

omit [NormedAddCommGroup E] in
/-- The normal coordinate of the graph parametrization is the graphing function. -/
@[simp]
theorem normalGraphEmbedding_fst (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).fst = φ y :=
  (rfl)

omit [NormedAddCommGroup E] in
/-- The tangential coordinate of the graph parametrization is its argument. -/
@[simp]
theorem normalGraphEmbedding_snd (φ : E → ℝ) (y : E) :
    (normalGraphEmbedding φ y).snd = y :=
  (rfl)

omit [NormedAddCommGroup E] in
/-- The normal graph parametrization is injective. -/
theorem injective_normalGraphEmbedding (φ : E → ℝ) :
    Function.Injective (normalGraphEmbedding φ) := fun _ _ h ↦ by
  simpa using congrArg WithLp.snd h

omit [NormedAddCommGroup E] in
/-- The range of the normal graph parametrization is the graph equation `t = φ y`. -/
theorem range_normalGraphEmbedding (φ : E → ℝ) :
    range (normalGraphEmbedding φ) = {x | x.fst = φ x.snd} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    refine ⟨x.snd, (WithLp.ext_iff 2).2 ?_⟩
    exact Prod.ext hx.symm rfl

/-- The second projection is a `1`-Lipschitz inverse to the graph parametrization on its range. -/
theorem antilipschitzWith_normalGraphEmbedding (φ : E → ℝ) :
    AntilipschitzWith 1 (normalGraphEmbedding φ) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  simpa only [NNReal.coe_one, one_mul, normalGraphEmbedding_snd] using
    WithLp.dist_snd_le (normalGraphEmbedding φ x) (normalGraphEmbedding φ y)

/-- A `K`-Lipschitz function has a `(K + 1)`-Lipschitz normal graph parametrization. -/
theorem _root_.LipschitzWith.normalGraphEmbedding {K : ℝ≥0} {φ : E → ℝ}
    (hφ : LipschitzWith K φ) :
    LipschitzWith (K + 1) (TauCeti.normalGraphEmbedding φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (TauCeti.normalGraphEmbedding φ x) (TauCeti.normalGraphEmbedding φ y) ≤
        dist (TauCeti.normalGraphEmbedding φ x) (WithLp.toLp 2 (φ y, x)) +
          dist (WithLp.toLp 2 (φ y, x)) (TauCeti.normalGraphEmbedding φ y) :=
      dist_triangle _ _ _
    _ = dist (φ x) (φ y) + dist x y := by
      simp [TauCeti.normalGraphEmbedding, WithLp.prod_dist_eq_of_L2]
    _ ≤ K * dist x y + dist x y := add_le_add (hφ.dist_le_mul x y) le_rfl
    _ = (K + 1) * dist x y := by ring

/-- A continuous normal graph is closed in the Euclidean product. -/
theorem _root_.Continuous.isClosed_range_normalGraphEmbedding {φ : E → ℝ} (hφ : Continuous φ) :
    IsClosed (range (TauCeti.normalGraphEmbedding φ)) := by
  rw [range_normalGraphEmbedding]
  exact isClosed_eq (WithLp.prod_continuous_ofLp 2 ℝ E).fst
    (hφ.comp (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Euclidean surface measure of a normal graph dominates volume of its parameter set. This
lower bound uses only that the tangential projection is `1`-Lipschitz. -/
theorem volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image (φ : E → ℝ)
    (s : Set E) :
    volume s ≤ μHE[finrank ℝ E] (TauCeti.normalGraphEmbedding φ '' s) := by
  let π : WithLp 2 (ℝ × E) → E := WithLp.snd
  have hπ : LipschitzWith 1 π := LipschitzWith.of_edist_le WithLp.edist_snd_le
  have h := hπ.lipschitzOnWith.euclideanHausdorffMeasure_image_le
    (finrank ℝ E) (s := TauCeti.normalGraphEmbedding φ '' s)
  rw [show π '' (TauCeti.normalGraphEmbedding φ '' s) = s by
    rw [image_image]
    simp only [π, normalGraphEmbedding_snd, image_id'],
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
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

/-- Weighted surface integration on a Lipschitz normal graph, expressed in parameter coordinates.
The density is the geometric Jacobian of the graph parametrization. -/
theorem _root_.LipschitzWith.lintegral_normalGraphEmbedding_image_eq
    {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) {s : Set E}
    (hs : MeasurableSet s) (g : WithLp 2 (ℝ × E) → ℝ≥0∞) :
    ∫⁻ z in TauCeti.normalGraphEmbedding φ '' s, g z ∂μHE[finrank ℝ E] =
      ∫⁻ y in s,
        ENNReal.ofReal (LinearMap.normDet (𝕜 := ℝ) (U := E)
            (V := WithLp 2 (ℝ × E))
            (fderiv ℝ (TauCeti.normalGraphEmbedding φ) y).toLinearMap) *
          g (TauCeti.normalGraphEmbedding φ y) :=
  hφ.normalGraphEmbedding.lintegral_image_eq_lintegral_normDet_fderiv_mul hs
    (injective_normalGraphEmbedding φ).injOn g

end TauCeti

end
