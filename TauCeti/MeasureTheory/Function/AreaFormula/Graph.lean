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
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Surface measure on normal graphs

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

The graph Jacobian itself, `DifferentiableAt.normDet_fderiv_normalGraphEmbedding`, is in
`TauCeti.Analysis.Calculus.FDeriv.WithLp`. For a Lipschitz `φ`, the graph parametrization is
Lipschitz and injective, so the area formula for injective Lipschitz maps
(`LipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul`) applies to it, and at the points
where `φ` is differentiable, almost every point by Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`), its Jacobian is the surface factor. A function Lipschitz
on an open set `U` agrees on `U` with a Lipschitz function on the whole space
(`LipschitzOnWith.extend_real`), with the same derivative at the points of `U`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula and Lipschitz graphs).
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

end
