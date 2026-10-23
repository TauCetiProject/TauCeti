/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.MeasureTheory.Function.AreaFormula.Graph
public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Surface measure in a Lipschitz boundary chart

A Lipschitz boundary chart parametrizes the part of the frontier inside its cylinder by

`y ↦ e.symm (normalGraphEmbedding φ y)`.

This file identifies the image of that parametrization and compares tangential Lebesgue measure
with normalized Euclidean Hausdorff measure on the frontier. It also gives the weighted area
formula in chart coordinates. These results are the measure-theoretic bridge from local Sobolev
traces in graph coordinates to traces on the boundary itself.

## Main declarations

* `Set.IsLipschitzChartWith.image_boundaryParametrization`: the chart parametrization covers
  exactly the frontier inside the chart cylinder.
* `Set.IsLipschitzChartWith.volume_le_euclideanHausdorffMeasure_frontier_inter`: surface measure
  dominates tangential volume in a chart.
* `Set.IsLipschitzChartWith.euclideanHausdorffMeasure_frontier_inter_le`: the converse estimate,
  with explicit dependence on the Lipschitz constant.
* `Set.IsLipschitzChartWith.lintegral_frontier_inter_eq`: the weighted area formula in chart
  coordinates.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §3.3 (the area formula and Lipschitz graphs).
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace Set.IsLipschitzChartWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section NormedTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {Omega : Set F} {L : ℝ≥0} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {phi : E → ℝ} {a b : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace F] [BorelSpace F] in
/-- The tangential parameters whose graph points lie in the cylinder of a boundary chart form
an open, hence measurable, set. -/
theorem measurableSet_normalGraphEmbedding_preimage_normalCylinder
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    MeasurableSet (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) :=
  ((TauCeti.isOpen_normalCylinder a b).preimage
    h.lipschitzWith.normalGraphEmbedding.continuous).measurableSet

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- The graph parametrization of a Lipschitz boundary chart is Lipschitz, with the same bound
as the normal graph parametrization. -/
theorem lipschitzWith_boundaryParametrization (h : Omega.IsLipschitzChartWith L e phi a b) :
    LipschitzWith (L + 1) (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [e.symm.isometry.dist_eq]
  exact h.lipschitzWith.normalGraphEmbedding.dist_le_mul x y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- A Lipschitz chart parametrizes exactly the part of the frontier lying inside its cylinder. -/
theorem image_boundaryParametrization (h : Omega.IsLipschitzChartWith L e phi a b) :
    (fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) ''
        (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) =
      frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hz : TauCeti.normalGraphEmbedding phi y ∈
        e '' frontier Omega ∩ TauCeti.normalCylinder a b := by
      rw [h.toIsLipschitzChart.image_frontier_inter_normalCylinder]
      exact ⟨by simp, hy⟩
    obtain ⟨z, hzF, hze⟩ := hz.1
    have hzx : z = e.symm (TauCeti.normalGraphEmbedding phi y) := by
      rw [← hze, e.symm_apply_apply]
    have hxF : e.symm (TauCeti.normalGraphEmbedding phi y) ∈ frontier Omega := by
      rw [← hzx]
      exact hzF
    exact ⟨hxF, by simpa using hz.2⟩
  · rintro ⟨hx, hxC⟩
    have hz : e x ∈ {z | z.fst = phi z.snd} ∩ TauCeti.normalCylinder a b := by
      rw [← h.toIsLipschitzChart.image_frontier_inter_normalCylinder]
      exact ⟨⟨x, hx, rfl⟩, hxC⟩
    have hgraph : TauCeti.normalGraphEmbedding phi (e x).snd = e x :=
      (WithLp.ext_iff 2).2 <| Prod.ext (by simpa using hz.1.symm) (by simp)
    refine ⟨(e x).snd, ?_, ?_⟩
    · simpa [hgraph] using hz.2
    · apply e.injective
      rw [e.apply_symm_apply, hgraph]

/-- In a Lipschitz boundary chart, normalized surface measure dominates tangential Lebesgue
measure. -/
theorem volume_le_euclideanHausdorffMeasure_frontier_inter
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) ≤
      μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) := by
  rw [← h.image_boundaryParametrization]
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact TauCeti.volume_le_euclideanHausdorffMeasure_normalGraphEmbedding_image phi _

/-- In a Lipschitz boundary chart, normalized surface measure is at most
`(L + 1) ^ dim E` times tangential Lebesgue measure. -/
theorem euclideanHausdorffMeasure_frontier_inter_le
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) ≤
      ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ E *
        volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) := by
  rw [← h.image_boundaryParametrization]
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact h.lipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_le _

/-- A set of tangential parameters is Lebesgue-null exactly when the corresponding part of the
boundary chart is null for normalized surface measure. -/
theorem euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff
    (h : Omega.IsLipschitzChartWith L e phi a b) (s : Set E) :
    μHE[finrank ℝ E]
        ((fun y ↦ e.symm (TauCeti.normalGraphEmbedding phi y)) '' s) = 0 ↔
      volume s = 0 := by
  rw [← image_image]
  rw [e.symm.isometry.euclideanHausdorffMeasure_image]
  exact h.lipschitzWith.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff s

/-- The frontier patch in a Lipschitz boundary chart has zero normalized surface measure exactly
when its set of tangential parameters has zero Lebesgue measure. -/
theorem euclideanHausdorffMeasure_frontier_inter_eq_zero_iff
    (h : Omega.IsLipschitzChartWith L e phi a b) :
    μHE[finrank ℝ E] (frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b) = 0 ↔
      volume (TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b) = 0 := by
  rw [← h.image_boundaryParametrization]
  exact h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff _

end NormedTarget

section EuclideanTarget

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {Omega : Set F} {L : ℝ≥0} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {phi : E → ℝ} {a b : ℝ}

/-- **Weighted area formula in a Lipschitz boundary chart.** Surface integration over the part
of the frontier inside the chart cylinder is integration over its tangential parameters, weighted
by the geometric Jacobian of the boundary parametrization. The weight need not be measurable. -/
theorem lintegral_frontier_inter_eq (h : Omega.IsLipschitzChartWith L e phi a b)
    (g : F → ℝ≥0∞) :
    ∫⁻ x in frontier Omega ∩ e ⁻¹' TauCeti.normalCylinder a b, g x ∂μHE[finrank ℝ E] =
      ∫⁻ y in TauCeti.normalGraphEmbedding phi ⁻¹' TauCeti.normalCylinder a b,
        ENNReal.ofReal
            (fderiv ℝ (fun z ↦ e.symm (TauCeti.normalGraphEmbedding phi z)) y).normDet *
          g (e.symm (TauCeti.normalGraphEmbedding phi y)) := by
  rw [← h.image_boundaryParametrization]
  exact (h.lipschitzWith_boundaryParametrization.lintegral_image_eq_lintegral_normDet_fderiv_mul
    h.measurableSet_normalGraphEmbedding_preimage_normalCylinder
      (e.symm.injective.comp (TauCeti.injective_normalGraphEmbedding phi)).injOn g)

end EuclideanTarget

end Set.IsLipschitzChartWith
