/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfCoordinates
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Riemannian volume in a chart

A Riemannian metric determines a measure locally by weighting coordinate Lebesgue measure with
the positive square root of the metric Gram determinant. This file constructs that measure on the
source of each preferred manifold chart and proves that the resulting measures agree on chart
overlaps. The compatibility theorem is the descent input for assembling the Riemannian volume
measure on the whole manifold.

The coordinate Lebesgue measure is `Module.finBasis ℝ E |>.addHaar`, matching the basis used by
`TauCeti.chartVolumeDensity`. The overlap proof applies Mathlib's change-of-variables theorem to
the extended chart transition and uses
`TauCeti.chartVolumeDensity_symm_apply_changeChart_fderivWithin` for its Jacobian factor.

The construction works without an orientation and for manifolds with boundary or corners. It
follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
Proposition 2.44.

## Main definitions

* `TauCeti.chartRiemannianVolume`: the Riemannian volume measure supplied by one preferred chart.

## Main results

* `TauCeti.chartRiemannianVolume_apply`: the coordinate integral formula.
* `TauCeti.chartRiemannianVolume_restrict_source`: a chart volume is supported on its source.
* `TauCeti.chartRiemannianVolume_restrict_overlap`: chart volume measures agree on overlaps.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped ENNReal Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Borel measurable space on the model vector space, used for chart volume. -/
local instance chartVolumeMeasurableSpaceE : MeasurableSpace E := borel E

/-- The Borel measurable space on the manifold, used for chart volume. -/
local instance chartVolumeMeasurableSpaceM : MeasurableSpace M := borel M

/-- The model vector space's measurable space is its Borel measurable space. -/
local instance chartVolumeBorelSpaceE : BorelSpace E := ⟨rfl⟩

/-- The manifold's measurable space is its Borel measurable space. -/
local instance chartVolumeBorelSpaceM : BorelSpace M := ⟨rfl⟩

/-- The local Riemannian volume measure supplied by the preferred chart at `α`. It is supported
on the source of that chart. -/
def chartRiemannianVolume (α : M) : Measure M :=
  (((Module.finBasis ℝ E).addHaar.withDensity fun y =>
      ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y))).comap
        ((extChartAt I α).source.domRestrict (extChartAt I α))).map Subtype.val

/-- A chart volume measure evaluates a measurable set by integrating the chart density over its
coordinate image inside the chart source. -/
theorem chartRiemannianVolume_apply (α : M) {s : Set M} (hs : MeasurableSet s) :
    chartRiemannianVolume (I := I) α s =
      ∫⁻ y in (extChartAt I α) '' (s ∩ (extChartAt I α).source),
        ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y))
          ∂(Module.finBasis ℝ E).addHaar := by
  rw [chartRiemannianVolume, Measure.map_apply measurable_subtype_coe hs,
    (measurableEmbedding_extChartAt_restrict (I := I) α).comap_apply]
  have hset :
      (extChartAt I α).source.domRestrict (extChartAt I α) '' Subtype.val ⁻¹' s =
        (extChartAt I α) '' (s ∩ (extChartAt I α).source) :=
    Set.image_domRestrict _ _ _
  rw [hset, withDensity_apply]
  rw [← hset]
  exact (measurableEmbedding_extChartAt_restrict (I := I) α).measurableSet_image.mpr
    (hs.preimage measurable_subtype_coe)

/-- A chart volume measure is supported on the source of its chart. -/
@[simp]
theorem chartRiemannianVolume_restrict_source (α : M) :
    (chartRiemannianVolume (I := I) α).restrict (chartAt H α).source =
      chartRiemannianVolume (I := I) α := by
  ext s hs
  rw [Measure.restrict_apply hs, chartRiemannianVolume_apply α
    (hs.inter (chartAt H α).open_source.measurableSet), chartRiemannianVolume_apply α hs]
  congr 2
  simp only [extChartAt_source, inter_assoc, inter_self]

/-- The local Riemannian volume measures supplied by two preferred charts agree on their overlap.
This is the cocycle condition needed to descend the local coordinate measures to the manifold. -/
theorem chartRiemannianVolume_restrict_overlap (α β : M) :
    (chartRiemannianVolume (I := I) α).restrict
        ((extChartAt I α).source ∩ (extChartAt I β).source) =
      (chartRiemannianVolume (I := I) β).restrict
        ((extChartAt I α).source ∩ (extChartAt I β).source) := by
  let U := (extChartAt I α).source ∩ (extChartAt I β).source
  have hU : MeasurableSet U :=
    (isOpen_extChartAt_source α).measurableSet.inter (isOpen_extChartAt_source β).measurableSet
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    chartRiemannianVolume_apply α (hs.inter hU),
    chartRiemannianVolume_apply β (hs.inter hU)]
  have hUα : U ⊆ (extChartAt I α).source := inter_subset_left
  have hUβ : U ⊆ (extChartAt I β).source := inter_subset_right
  have hsα : (s ∩ U) ∩ (extChartAt I α).source = s ∩ U :=
    inter_eq_left.mpr (inter_subset_right.trans hUα)
  have hsβ : (s ∩ U) ∩ (extChartAt I β).source = s ∩ U :=
    inter_eq_left.mpr (inter_subset_right.trans hUβ)
  rw [hsα, hsβ]
  -- Work on the α-coordinate image of the measurable part of the overlap.
  let A := (extChartAt I α) '' (s ∩ U)
  let e := (extChartAt I α).symm ≫ extChartAt I β
  have hsU : MeasurableSet (s ∩ U) := hs.inter hU
  have hsUα : s ∩ U ⊆ (extChartAt I α).source := inter_subset_right.trans hUα
  have hsUβ : s ∩ U ⊆ (extChartAt I β).source := inter_subset_right.trans hUβ
  have hA : MeasurableSet A := hsU.image_extChartAt α hsUα
  have hA_target : A ⊆ (extChartAt I α).target :=
    image_mono hsUα |>.trans (extChartAt I α).image_source_eq_target.subset
  have hA_range : A ⊆ Set.range I := hA_target.trans (extChartAt_target_subset_range α)
  have hA_source : A ⊆ e.source := by
    rintro y ⟨x, hx, rfl⟩
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
      (extChartAt I α).left_inv (hsUα hx)]
    exact ⟨(extChartAt I α).map_source (hsUα hx), hsUβ hx⟩
  have himage : e '' A = (extChartAt I β) '' (s ∩ U) := by
    simp only [A, image_image]
    apply image_congr
    intro x hx
    simp only [e, PartialEquiv.trans_apply, (extChartAt I α).left_inv (hsUα hx)]
  have hderiv : ∀ y ∈ A,
      HasFDerivWithinAt e
        (fderivWithin ℝ ((extChartAt I β) ∘ (extChartAt I α).symm) (Set.range I) y) A y := by
    rintro y ⟨x, hx, rfl⟩
    exact (hasFDerivWithinAt_tangentCoordChange (I := I)
      (mem_inter (hsUα hx) (hsUβ hx))).mono hA_range
  -- Change variables to β-coordinates, then use the density's Jacobian transformation law.
  rw [← himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (Module.finBasis ℝ E).addHaar hA hderiv (e.injOn.mono hA_source)]
  apply setLIntegral_congr_fun hA
  rintro y ⟨x, hx, rfl⟩
  have hy : extChartAt I α x ∈ e.source := hA_source ⟨x, hx, rfl⟩
  have hdensity := chartVolumeDensity_symm_apply_changeChart_fderivWithin
    (I := I) α β hy
  calc
    ENNReal.ofReal (chartVolumeDensity (I := I) α
        ((extChartAt I α).symm ((extChartAt I α) x))) =
        ENNReal.ofReal
          (|(fderivWithin ℝ ((extChartAt I β) ∘ (extChartAt I α).symm) (Set.range I)
              ((extChartAt I α) x)).det| *
            chartVolumeDensity (I := I) β ((extChartAt I α).symm ((extChartAt I α) x))) :=
      congrArg ENNReal.ofReal hdensity
    _ = ENNReal.ofReal
          |(fderivWithin ℝ ((extChartAt I β) ∘ (extChartAt I α).symm) (Set.range I)
              ((extChartAt I α) x)).det| *
        ENNReal.ofReal
          (chartVolumeDensity (I := I) β ((extChartAt I α).symm ((extChartAt I α) x))) :=
      ENNReal.ofReal_mul (abs_nonneg _)
    _ = ENNReal.ofReal
          |(fderivWithin ℝ ((extChartAt I β) ∘ (extChartAt I α).symm) (Set.range I)
              ((extChartAt I α) x)).det| *
        ENNReal.ofReal (chartVolumeDensity (I := I) β
          ((extChartAt I β).symm (e ((extChartAt I α) x)))) := by
      have he_apply : e ((extChartAt I α) x) = (extChartAt I β) x := by
        simp only [e, PartialEquiv.trans_apply, (extChartAt I α).left_inv (hsUα hx)]
      rw [he_apply, (extChartAt I β).left_inv (hsUβ hx),
        (extChartAt I α).left_inv (hsUα hx)]

end TauCeti
